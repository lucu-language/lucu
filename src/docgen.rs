use core::fmt;

use crate::{
    ast::{
        AliasIdx, Ast, Effect, Expression, FailType, FunDecl, Ident, Param, PolyParam, StructIdx,
        Type, TypeIdx,
    },
    error::{get_lines, File, FileIdx, Ranged},
    vecmap::VecMap,
};

pub trait Docgen {
    fn gen(&self, files: &VecMap<FileIdx, File>, ast: &Ast, f: &mut impl fmt::Write)
        -> fmt::Result;
}

fn get_comment(files: &VecMap<FileIdx, File>, ast: &Ast, ident: Ident) -> String {
    let pos = ast.idents[ident].1;
    let file = ast.idents[ident].3;

    let lines = files[file].content[0..pos].lines();
    let lines = lines
        .rev()
        .skip(1)
        .take_while(|line| line.trim_start().starts_with("#"))
        .map(|line| line.trim_start_matches(['#', ' ', '\t']));

    let mut lines = lines.collect::<Vec<_>>();
    lines.reverse();
    lines.join("\n").trim().to_owned()
}

impl<K: Into<usize>, V: Docgen> Docgen for VecMap<K, V> {
    fn gen(
        &self,
        files: &VecMap<FileIdx, File>,
        ast: &Ast,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        for item in self.values().take(self.len().saturating_sub(1)) {
            item.gen(files, ast, f)?;
            write!(f, ", ")?;
        }
        if let Some(item) = self.values().last() {
            item.gen(files, ast, f)?;
        }
        Ok(())
    }
}

impl<V: Docgen> Docgen for Vec<V> {
    fn gen(
        &self,
        files: &VecMap<FileIdx, File>,
        ast: &Ast,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        for item in self.iter().take(self.len() - 1) {
            item.gen(files, ast, f)?;
            write!(f, ", ")?;
        }
        if let Some(item) = self.iter().last() {
            item.gen(files, ast, f)?;
        }
        Ok(())
    }
}

impl Docgen for PolyParam {
    fn gen(
        &self,
        files: &VecMap<FileIdx, File>,
        ast: &Ast,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        write!(f, "{}", ast.ident(self.name))?;
        if let Some(ty) = self.ty {
            write!(f, " ")?;
            ty.gen(files, ast, f)?;
        }
        Ok(())
    }
}

impl Docgen for TypeIdx {
    fn gen(
        &self,
        files: &VecMap<FileIdx, File>,
        ast: &Ast,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        match ast.types[*self].0 {
            Type::Never => write!(f, "!")?,
            Type::Path(ref id) => {
                if let Some(pkg) = id.ident.package {
                    write!(f, "{}.", ast.ident(pkg))?;
                }
                write!(f, "{}", ast.ident(id.ident.ident))?;
                if let Some(generics) = id.params.as_ref() {
                    write!(f, "(")?;
                    generics.gen(files, ast, f)?;
                    write!(f, ")")?;
                }
            }
            Type::Generic(id) => write!(f, "{}", ast.ident(id))?,
            Type::Handler(ref id, fail) => {
                write!(f, "impl ")?;
                if let Some(pkg) = id.ident.package {
                    write!(f, "{}.", ast.ident(pkg))?;
                }
                write!(f, "{}", ast.ident(id.ident.ident))?;
                if let Some(generics) = id.params.as_ref() {
                    write!(f, "(")?;
                    generics.gen(files, ast, f)?;
                    write!(f, ")")?;
                }
                match fail {
                    FailType::Never => {}
                    FailType::Some(ty) => {
                        write!(f, " -> ")?;
                        ty.gen(files, ast, f)?;
                    }
                }
            }
            Type::GenericHandler(id, fail) => {
                write!(f, "impl ")?;
                write!(f, "{}", ast.ident(id))?;
                match fail {
                    FailType::Never => {}
                    FailType::Some(ty) => {
                        write!(f, " -> ")?;
                        ty.gen(files, ast, f)?;
                    }
                }
            }
            Type::Maybe(ty) => {
                write!(f, "?")?;
                ty.gen(files, ast, f)?;
            }
            Type::Pointer(isconst, ty) => {
                write!(f, "^")?;
                if isconst {
                    write!(f, "const ")?;
                }
                ty.gen(files, ast, f)?;
            }
            Type::Slice(isconst, ty) => {
                write!(f, "[]")?;
                if isconst {
                    write!(f, "const ")?;
                }
                ty.gen(files, ast, f)?;
            }
            Type::ConstArray(expr, ty) => {
                match ast.exprs[expr].0 {
                    Expression::Int(i) => write!(f, "[{}]", i)?,
                    Expression::Ident(i) => write!(f, "[{}]", ast.ident(i))?,
                    _ => todo!(),
                }
                ty.gen(files, ast, f)?;
            }
            Type::Error => unreachable!(),
        }
        Ok(())
    }
}

fn write_title(
    files: &VecMap<FileIdx, File>,
    ident: &Ranged<String>,
    f: &mut impl fmt::Write,
) -> fmt::Result {
    writeln!(f, "### {}", ident.0)?;
    let (pos, _) = get_lines(&files[ident.3].content, ident.empty());
    writeln!(f, "[source]({}#L{})", files[ident.3].name, pos.line)?;
    Ok(())
}

impl Docgen for FunDecl {
    fn gen(
        &self,
        files: &VecMap<FileIdx, File>,
        ast: &Ast,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        write_title(files, &ast.idents[self.name], f)?;
        writeln!(f, "```")?;
        write!(f, "fun {}(", ast.ident(self.name))?;
        self.sign.inputs.gen(files, ast, f)?;
        write!(f, ")")?;

        if let Some(output) = self.sign.output {
            write!(f, " ")?;
            output.gen(files, ast, f)?;
        }

        if !self.sign.effects.is_empty() {
            write!(f, " / ")?;
            for id in self.sign.effects.iter() {
                if let Some(pkg) = id.ident.package {
                    write!(f, "{}.", ast.ident(pkg))?;
                }
                write!(f, "{}", ast.ident(id.ident.ident))?;
                if let Some(generics) = id.params.as_ref() {
                    write!(f, "(")?;
                    generics.gen(files, ast, f)?;
                    write!(f, ")")?;
                }
                write!(f, " ")?;
            }
        }
        writeln!(f, "\n```")?;

        let comment = get_comment(files, ast, self.name);
        if !comment.is_empty() {
            writeln!(f, "{}", comment)?;
        }

        Ok(())
    }
}

impl Docgen for Param {
    fn gen(
        &self,
        files: &VecMap<FileIdx, File>,
        ast: &Ast,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        if self.mutable {
            write!(f, "mut ")?;
        }
        write!(f, "{} ", ast.ident(self.name))?;
        self.ty.gen(files, ast, f)?;
        Ok(())
    }
}

impl Docgen for AliasIdx {
    fn gen(
        &self,
        files: &VecMap<FileIdx, File>,
        ast: &Ast,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        let (name, ty) = ast.aliases[*self];
        write_title(files, &ast.idents[name], f)?;
        write!(f, "```\ntype {} = ", ast.ident(name))?;
        ty.gen(files, ast, f)?;
        writeln!(f, "\n```")?;

        let comment = get_comment(files, ast, name);
        if !comment.is_empty() {
            writeln!(f, "{}", comment)?;
        }

        Ok(())
    }
}

impl Docgen for (Ident, TypeIdx) {
    fn gen(
        &self,
        files: &VecMap<FileIdx, File>,
        ast: &Ast,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        write!(f, "{} ", ast.ident(self.0))?;
        self.1.gen(files, ast, f)?;
        Ok(())
    }
}

impl Docgen for StructIdx {
    fn gen(
        &self,
        files: &VecMap<FileIdx, File>,
        ast: &Ast,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        let struc = &ast.structs[*self];
        write_title(files, &ast.idents[struc.name], f)?;
        write!(f, "```\nstruct {}(", ast.ident(struc.name))?;
        struc.elems.gen(files, ast, f)?;
        writeln!(f, ")\n```")?;

        let comment = get_comment(files, ast, struc.name);
        if !comment.is_empty() {
            writeln!(f, "{}", comment)?;
        }

        Ok(())
    }
}

impl Docgen for Effect {
    fn gen(
        &self,
        files: &VecMap<FileIdx, File>,
        ast: &Ast,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        write_title(files, &ast.idents[self.name], f)?;
        writeln!(f, "```")?;
        write!(f, "effect {}", ast.ident(self.name))?;
        if let Some(generics) = self.generics.as_ref() {
            write!(f, "(")?;
            generics.gen(files, ast, f)?;
            write!(f, ")")?;
        }
        writeln!(f, "\n```")?;

        let comment = get_comment(files, ast, self.name);
        if !comment.is_empty() {
            writeln!(f, "{}", comment)?;
        }

        writeln!(f, "\n*Handler functions*\n")?;
        for fun in self.functions.values() {
            writeln!(f, "- `{}`", ast.ident(fun.name))?;
        }

        Ok(())
    }
}
