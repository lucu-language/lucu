use std::fmt;

use compact_str::CompactString;
use strum::IntoStaticStr;

use crate::ast;

#[derive(Debug, PartialEq, Eq)]
pub struct String(pub CompactString);
#[derive(Debug, PartialEq, Eq)]
pub struct Ident(pub CompactString);
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Module {
    pub imports: Vec<ast::Import>,
    pub definitions: Vec<ast::Definition>,
}
#[derive(Debug, PartialEq, Eq)]
pub struct Import {
    pub path: ast::String,
    pub ident: Option<ast::Ident>,
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Definition::")]
pub enum Definition {
    Function(ast::FunctionDeclaration, Option<ast::FunctionDefinition>),
    Type(ast::Name, Option<ast::TypeDefinition>),
    Effect(ast::Name, Option<ast::EffectDefinition>),
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "FunctionDefinition::")]
pub enum FunctionDefinition {
    Expression(Box<ast::Expression>),
    Intrinsic,
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "TypeDefinition::")]
pub enum TypeDefinition {
    Type(Box<ast::Type>),
    Struct(ast::Struct),
    Intrinsic,
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "EffectDefinition::")]
pub enum EffectDefinition {
    Body(ast::EffectBody),
    Alias(Vec<ast::Path>),
    Intrinsic,
}
#[derive(Debug, PartialEq, Eq)]
pub struct EffectBody {
    pub definitions: Vec<ast::Definition>,
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Kind::")]
pub enum Kind {
    Type,
    Effect,
    Region,
    Constant(Box<ast::Type>),
}
#[derive(Debug, PartialEq, Eq)]
pub struct GenericParameter {
    pub name: ast::Name,
    pub kind: Option<ast::Kind>,
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "GenericArgument::")]
pub enum GenericArgument {
    Path(ast::Path),
    Type(Box<ast::Type>),
    Constant(Box<ast::Constant>),
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Constant::")]
pub enum Constant {
    // TODO
}
#[derive(Debug, PartialEq, Eq)]
pub struct Name {
    pub ident: ast::Ident,
    pub generics: Option<Vec<ast::GenericParameter>>,
}
#[derive(PartialEq, Eq)]
pub struct Path {
    pub package: Option<ast::Ident>,
    pub name: ast::Ident,
    pub generics: Option<Vec<ast::GenericArgument>>,
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Type::")]
pub enum Type {
    Path(ast::Path),
    Pointer(Box<ast::Type>, Option<ast::Path>),
    Slice(Box<ast::Type>, Option<ast::Path>),
}
#[derive(Debug, PartialEq, Eq)]
pub struct Struct {
    pub members: Vec<ast::StructMember>,
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "StructMember::")]
pub enum StructMember {
    Data(ast::Ident, Box<ast::Type>),
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Expression::")]
pub enum Expression {
    Block,
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "FunctionParameter::")]
pub enum FunctionParameter {
    Data(ast::Ident, Box<ast::Type>),
    Lambda(ast::FunctionDeclaration),
}
#[derive(Debug, PartialEq, Eq)]
pub struct FunctionDeclaration {
    pub name: ast::Name,
    pub parameters: Option<Vec<ast::FunctionParameter>>,
    pub returns: Option<ast::Returns>,
    pub effects: Option<Vec<ast::Path>>,
}
#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Returns::")]
pub enum Returns {
    Never,
    Data(Box<ast::Type>),
}

impl String {
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl Ident {
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl Name {
    pub fn as_str(&self) -> &str {
        self.ident.as_str()
    }
}

impl Definition {
    pub fn name(&self) -> Option<&ast::Name> {
        match self {
            Definition::Function(fun, _) => Some(&fun.name),
            Definition::Type(name, _) => Some(name),
            Definition::Effect(name, _) => Some(name),
        }
    }
    pub fn generics(&self) -> &[ast::GenericParameter] {
        match self {
            Definition::Function(fun, _) => fun.name.generics.as_deref().unwrap_or_default(),
            Definition::Type(name, _) => name.generics.as_deref().unwrap_or_default(),
            Definition::Effect(name, _) => name.generics.as_deref().unwrap_or_default(),
        }
    }
    pub fn children(&self) -> &[ast::Definition] {
        match self {
            Definition::Effect(_, def) => {
                if let Some(def) = def {
                    match &def.0 {
                        EffectDefinition::Body(body) => &body.definitions,
                        _ => &[],
                    }
                } else {
                    &[]
                }
            }
            _ => &[],
        }
    }
}

impl fmt::Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.package {
            Some(pkg) => write!(f, "\"{}.{}\"", pkg.0.0, self.name.0.0),
            None => write!(f, "\"{}\"", self.name.0.0),
        }
    }
}
