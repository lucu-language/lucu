use core::fmt;

use crate::{
    ast::{Ast, Effect, Ident, PolyParam},
    error::{File, FileIdx},
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
        .take_while(|line| line.starts_with("#"))
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
        for item in self.values().take(self.len() - 1) {
            item.gen(files, ast, f)?;
            write!(f, ", ")?;
        }
        if let Some(item) = self.values().last() {
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

        Ok(())
    }
}
