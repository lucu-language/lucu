use std::{
    collections::HashMap,
    ffi::OsStr,
    fs::{read_dir, read_to_string},
    path::{Path, PathBuf},
    println,
    process::Command,
};

use analyzer::{analyze, Analysis};
use ast::{parse_ast, AST};
use clap::Parser;
use error::{Errors, File, FileIdx};
use inkwell::targets::{TargetMachine, TargetTriple};
use lexer::Tokenizer;
use vecmap::VecMap;

mod analyzer;
mod ast;
mod error;
mod ir;
mod lexer;
mod llvm;
mod sema;
mod vecmap;

#[derive(Debug)]
pub struct Target {
    pub triple: String,
    pub cpu: Option<String>,
    pub features: Option<String>,
}

pub enum LucuOS {
    Linux,
    Windows,
    WASI,
    Unknown,
}

pub enum LucuArch {
    I386,
    Amd64,
    Arm32,
    Arm64,
    Wasm32,
    Wasm64,
}

impl LucuArch {
    pub fn as_str(&self) -> &'static str {
        match self {
            LucuArch::I386 => "i386",
            LucuArch::Amd64 => "amd64",
            LucuArch::Arm32 => "arm32",
            LucuArch::Arm64 => "arm64",
            LucuArch::Wasm32 => "wasm32",
            LucuArch::Wasm64 => "wasm64",
        }
    }
    pub fn register_size(&self) -> u32 {
        match self {
            LucuArch::I386 => 32,
            LucuArch::Amd64 => 64,
            LucuArch::Arm32 => 32,
            LucuArch::Arm64 => 64,

            // wasm doesn't really have "registers"
            // but it fully supports 32 and 64 bits integers, regardless of ptr size
            // so we decide that the wasm register size is always 64 bits
            LucuArch::Wasm32 => 64,
            LucuArch::Wasm64 => 64,
        }
    }
    pub fn ptr_size(&self) -> u32 {
        match self {
            LucuArch::I386 => 32,
            LucuArch::Amd64 => 64,
            LucuArch::Arm32 => 32,
            LucuArch::Arm64 => 64,
            LucuArch::Wasm32 => 32,
            LucuArch::Wasm64 => 64,
        }
    }
    pub fn array_len_size(&self) -> u32 {
        match self {
            LucuArch::I386 => 32,
            LucuArch::Amd64 => 64,
            LucuArch::Arm32 => 32,
            LucuArch::Arm64 => 64,
            LucuArch::Wasm32 => 32,
            LucuArch::Wasm64 => 64,
        }
    }
}

impl LucuOS {
    pub fn as_str(&self) -> &'static str {
        match self {
            LucuOS::Linux => "linux",
            LucuOS::Windows => "windows",
            LucuOS::WASI => "wasi",
            LucuOS::Unknown => "unknown",
        }
    }
    pub fn wasm_import_module(&self) -> &'static str {
        match self {
            LucuOS::WASI => "wasi_snapshot_preview1",
            _ => "env",
        }
    }
}

impl Target {
    pub fn lucu_os(&self) -> LucuOS {
        let mut split = self.triple.split('-');
        let _arch = split.next();
        let _vendor = split.next();
        let sys = split.next();
        let env = split.next();

        match (sys, env) {
            (Some("linux"), _) => LucuOS::Linux,
            (Some("windows"), _) => LucuOS::Windows,
            (Some("wasi"), _) => LucuOS::WASI,
            _ => LucuOS::Unknown,
        }
    }
    pub fn lucu_arch(&self) -> LucuArch {
        if self.triple.starts_with("amd64")
            || self.triple.starts_with("x86_64")
            || self.triple.starts_with("x64")
        {
            LucuArch::Amd64
        } else if self.triple.starts_with("i386") || self.triple.starts_with("x86") {
            LucuArch::I386
        } else if self.triple.starts_with("arm64") || self.triple.starts_with("aarch64") {
            LucuArch::Arm64
        } else if self.triple.starts_with("arm") {
            LucuArch::Arm32
        } else if self.triple.starts_with("wasm64") {
            LucuArch::Wasm64
        } else if self.triple.starts_with("wasm") {
            LucuArch::Wasm32
        } else {
            panic!(
                "unknown architecture {}",
                match self.triple.split_once('-') {
                    Some((arch, _)) => arch,
                    None => &self.triple,
                }
            )
        }
    }
    pub fn host(cpu: Option<String>, features: Option<String>) -> Self {
        Self {
            triple: TargetMachine::get_default_triple()
                .as_str()
                .to_owned()
                .into_string()
                .unwrap(),

            // TODO: get common denominator
            cpu: Some(cpu.unwrap_or_else(|| TargetMachine::get_host_cpu_name().to_string())),
            features: Some(
                features.unwrap_or_else(|| TargetMachine::get_host_cpu_features().to_string()),
            ),
        }
    }
}

fn parse_from_filename(
    main_file: &Path,
    core_path: &Path,
    target: &Target,
) -> Result<(AST, Analysis, VecMap<FileIdx, File>), Errors> {
    let mut parsed = AST::default();
    let mut errors = Errors::new();

    let preamble = core_path.join("core").join("preamble.lucu");
    let system = match target.lucu_os() {
        LucuOS::Linux => Some(core_path.join("core").join("sys/linux")),
        LucuOS::Windows => Some(core_path.join("core").join("sys/nt")),
        LucuOS::WASI => Some(core_path.join("core").join("sys/wasi")),
        LucuOS::Unknown => None,
    };
    let mut files_todo = vec![
        (main_file.to_path_buf(), parsed.main),
        (preamble, parsed.preamble),
    ];
    if let Some(system) = system {
        files_todo.push((system, parsed.system));
    }

    let mut libs = HashMap::new();
    let core = core_path.join("core");
    libs.insert("core", core.as_path());
    let vendor = core_path.join("vendor");
    libs.insert("vendor", vendor.as_path());

    let mut n = 0;
    while let Some(&(ref path, pkg)) = files_todo.get(n) {
        n += 1;

        match path.extension() == Some(OsStr::new("lucu")) {
            true => {
                let content = read_to_string(&path).unwrap().replace('\t', "  ");
                let idx = errors.files.push(
                    FileIdx,
                    File {
                        content: content.clone(),
                        name: path.to_string_lossy().into_owned(),
                    },
                );
                let tok = Tokenizer::new(&content, idx, &mut errors);
                parse_ast(
                    tok,
                    pkg,
                    &mut parsed,
                    &path.clone().parent().unwrap(),
                    &libs,
                    &mut files_todo,
                );
            }
            false => match read_dir(&path) {
                Ok(files) => {
                    let iter = files.filter_map(|entry| {
                        // get lucu files
                        let path = entry.ok()?.path();
                        if path.extension() == Some(OsStr::new("lucu")) {
                            Some(path)
                        } else {
                            None
                        }
                    });

                    let path = path.clone();
                    for file in iter {
                        let content = read_to_string(&file).unwrap().replace('\t', "  ");
                        let idx = errors.files.push(
                            FileIdx,
                            File {
                                content: content.clone(),
                                name: file.to_string_lossy().into_owned(),
                            },
                        );
                        let tok = Tokenizer::new(&content, idx, &mut errors);
                        parse_ast(tok, pkg, &mut parsed, &path, &libs, &mut files_todo);
                    }
                }
                Err(_) => {}
            },
        }
    }

    let ir = sema::analyze(&parsed, &mut errors, &target);
    println!("{}", ir);

    if errors.is_empty() {
        // OLD ANALYZER
        let asys = analyze(&parsed, &mut errors, &target);
        if errors.is_empty() {
            Ok((parsed, asys, errors.files))
        } else {
            Err(errors)
        }
    } else {
        Err(errors)
    }
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(help = ".lucu file with entry point")]
    main: PathBuf,
    #[arg(
        short,
        long,
        help = "Set the file name of the outputted executable\n  defaults to 'out(.exe)'"
    )]
    out: Option<PathBuf>,

    #[arg(
        long,
        help = "Target architecture triple\n  defaults to the host architecture"
    )]
    target: Option<String>,
    #[arg(
        long,
        help = "Target cpu name\n  defaults to the common denominator for the target architecture"
    )]
    cpu: Option<String>,
    #[arg(
        long,
        help = "Target cpu features\n  defaults to the common denominator for the target architecture"
    )]
    features: Option<String>,

    #[arg(
        long,
        help = "Set the location of the folder that contains the core and vendor libraries"
    )]
    core: Option<PathBuf>,
    #[arg(long, help = "Print compiler output in plaintext, without color")]
    plaintext: bool,
    #[arg(long, help = "Print compiler debug info")]
    debug: bool,
}

fn main() {
    unsafe { backtrace_on_stack_overflow::enable() };

    let args = Args::parse();
    let core = args.core.unwrap_or_else(|| {
        option_env!("LUCU_CORE")
            .map(Path::new)
            .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")))
            .to_path_buf()
    });

    let debug = args.debug;
    let color = !args.plaintext;
    let output = args.out.unwrap_or_else(|| PathBuf::from("out"));

    let target = match args.target {
        Some(t) => {
            let triple = TargetTriple::create(&t);
            let triple = TargetMachine::normalize_triple(&triple);
            Target {
                triple: triple.as_str().to_owned().into_string().unwrap(),

                // TODO: get common denominator
                cpu: args.cpu,
                features: args.features,
            }
        }
        None => Target::host(args.cpu, args.features),
    };

    // analyze
    match parse_from_filename(&args.main, &core, &target) {
        Ok((parsed, asys, files)) => {
            // generate ir
            let ir = ir::generate_ir(&parsed, &asys, &target, &files);
            if debug {
                println!("\n--- IR ---");
                println!("{}", ir);
                println!("\n--- LLVM ---");
            }

            // generate llvm
            llvm::generate_ir(&ir, &output.with_extension("o"), debug, &target);

            // output
            if debug {
                println!("\n--- OUTPUT ---");
            }

            // TODO: config for linker and runner
            let os = target.lucu_os();
            let arch = target.lucu_arch();
            match (&os, &arch) {
                (LucuOS::Linux, LucuArch::Amd64) => {
                    Command::new("ld")
                        .arg(&output.with_extension("o"))
                        .args(ir.links.iter().map(|lib| format!("-l{}", lib)))
                        .arg("-o")
                        .arg(&output)
                        .arg("-e_start")
                        .status()
                        .unwrap();
                    Command::new(Path::new("./").join(&output))
                        .status()
                        .unwrap();
                }
                (LucuOS::Windows, LucuArch::Amd64) => {
                    Command::new("x86_64-w64-mingw32-ld")
                        .arg(&output.with_extension("o"))
                        .args(ir.links.iter().map(|lib| format!("-l{}", lib)))
                        .arg("-o")
                        .arg(&output.with_extension("exe"))
                        .arg("-e_start")
                        .status()
                        .unwrap();
                    Command::new(Path::new("./").join(&output).with_extension("exe"))
                        .status()
                        .unwrap();
                }
                (_, LucuArch::Wasm32 | LucuArch::Wasm64) => {
                    let env = os.wasm_import_module();
                    Command::new("wasm-ld")
                        .arg(&output.with_extension("o"))
                        .args(
                            ir.links
                                .iter()
                                .filter(|lib| !str::eq(lib, env))
                                .map(|lib| format!("-l{}", lib)),
                        )
                        .arg("--import-undefined") // TODO: get list of symbols from "env" library
                        .arg("-o")
                        .arg(&output.with_extension("wasm"))
                        .arg("-z")
                        .arg("stack-size=1048576")
                        .arg("-e_start")
                        .status()
                        .unwrap();

                    if matches!(os, LucuOS::WASI) {
                        Command::new("wasmtime")
                            .arg(&output.with_extension("wasm"))
                            .status()
                            .unwrap();
                    } else {
                        println!(
                            "unknown runner for triple: {}\nplease run the program manually",
                            target.triple
                        );
                    }
                }
                _ => {
                    println!(
                        "unknown linker setup for triple: {}\nplease link the program manually",
                        target.triple
                    );
                }
            }
        }
        Err(errors) => {
            errors.print(color);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::assert_eq;

    use super::*;

    fn execute(filename: &Path, output: &Path) -> String {
        let core = Path::new(env!("CARGO_MANIFEST_DIR"));
        let target = Target::host(None, None);

        match parse_from_filename(Path::new(filename), &core, &target) {
            Ok((parsed, asys, files)) => {
                let ir = ir::generate_ir(&parsed, &asys, &target, &files);
                llvm::generate_ir(&ir, &output.with_extension("o"), false, &target);

                match target.lucu_os() {
                    LucuOS::Linux => {
                        Command::new("ld")
                            .arg(&output.with_extension("o"))
                            .arg("-o")
                            .arg(&output)
                            .arg("-e_start")
                            .status()
                            .unwrap();
                        Command::new(Path::new("./").join(&output))
                            .status()
                            .unwrap();
                    }
                    LucuOS::Unknown => {
                        panic!("unknown os for triple: {}", target.triple);
                    }
                    other => panic!("no test environment defined for os: {}", other.as_str()),
                }

                let vec = Command::new(output).output().unwrap().stdout;
                String::from_utf8(vec).unwrap()
            }
            Err(errors) => {
                errors.print(false);
                String::from("[ERROR]")
            }
        }
    }

    fn test_file(filename: &str, expected: &str) {
        let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");

        let dir = std::env::temp_dir();
        assert_eq!(
            execute(
                &examples.join(filename).with_extension("lucu"),
                &dir.join(filename)
            ),
            expected
        )
    }

    #[test]
    fn safe_div() {
        test_file("div", "3\n1\n420\n")
    }

    #[test]
    fn hello() {
        test_file("hello", "Hello, World!\n")
    }

    #[test]
    fn implicit_explicit() {
        test_file("implicit", "69\n420\n90\n")
    }

    #[test]
    fn implicit_nonzero() {
        test_file("nonzero", "7\n2\n")
    }

    #[test]
    fn handler_type() {
        test_file("simple_effect", "420\n69\n69\n")
    }

    #[test]
    fn fail_union() {
        test_file("yeet", "42\nHello, World!\n")
    }

    #[test]
    fn naked_vs_nonnaked() {
        test_file("naked", "5\n5\nreachable\n69\n")
    }

    #[test]
    fn mutation_outside() {
        test_file("setter", "69\n420\n24\n42\n")
    }

    #[test]
    fn mutation_inside() {
        test_file("counter", "5\n6\n7\n")
    }

    #[test]
    fn effect_function_handlers() {
        test_file("printget", "onetwotea")
    }
}
