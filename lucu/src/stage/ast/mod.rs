pub mod err;
pub mod parser;
pub mod visit;

use crate::span::Spanned;

pub mod inner {
    use std::fmt;

    use compact_str::CompactString;
    use strum::IntoStaticStr;

    use crate::stage::ast;

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
        Function(ast::Function),
        Type(ast::TypeAlias),
        Effect(ast::Effect),
    }
    #[derive(Debug, PartialEq, Eq)]
    pub struct Function {
        pub declaration: ast::FunctionDeclaration,
        pub definition: Box<ast::Expression>,
    }
    #[derive(Debug, PartialEq, Eq)]
    pub struct TypeAlias {
        pub name: ast::Name,
        pub definition: Box<ast::Type>,
    }
    #[derive(Debug, PartialEq, Eq)]
    pub struct Effect {
        pub name: ast::Name,
        pub definition: ast::EffectDefinition,
    }
    #[derive(Debug, PartialEq, Eq, IntoStaticStr)]
    #[strum(prefix = "EffectDefinition::")]
    pub enum EffectDefinition {
        Body(ast::EffectBody),
        Alias(Vec<ast::Path>),
    }
    #[derive(Debug, PartialEq, Eq)]
    pub struct EffectBody {
        pub functions: Vec<ast::FunctionDeclaration>,
    }
    #[derive(Debug, PartialEq, Eq, IntoStaticStr)]
    #[strum(prefix = "Kind::")]
    pub enum Kind {
        Type,
        Effect,
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
        Int,
        Path(ast::Path),
        Struct(ast::Struct),
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
                Definition::Function(fun) => Some(&fun.declaration.name),
                Definition::Type(ty) => Some(&ty.name),
                Definition::Effect(ty) => Some(&ty.name),
            }
        }
        pub fn generics(&self) -> &[ast::GenericParameter] {
            // TODO: those without a name may also have generics
            self.name()
                .and_then(|name| name.generics.as_deref())
                .unwrap_or_default()
        }
        pub fn children(&self) -> &[ast::Definition] {
            // TODO: children
            &[]
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
}

pub type String = Spanned<inner::String>;
pub type Ident = Spanned<inner::Ident>;
pub type Module = Spanned<inner::Module>;
pub type Import = Spanned<inner::Import>;
pub type Definition = Spanned<inner::Definition>;
pub type Function = Spanned<inner::Function>;
pub type TypeAlias = Spanned<inner::TypeAlias>;
pub type Kind = Spanned<inner::Kind>;
pub type GenericParameter = Spanned<inner::GenericParameter>;
pub type GenericArgument = Spanned<inner::GenericArgument>;
pub type Constant = Spanned<inner::Constant>;
pub type Name = Spanned<inner::Name>;
pub type Path = Spanned<inner::Path>;
pub type Type = Spanned<inner::Type>;
pub type Struct = Spanned<inner::Struct>;
pub type StructMember = Spanned<inner::StructMember>;
pub type Expression = Spanned<inner::Expression>;
pub type FunctionParameter = Spanned<inner::FunctionParameter>;
pub type FunctionDeclaration = Spanned<inner::FunctionDeclaration>;
pub type Returns = Spanned<inner::Returns>;
pub type Effect = Spanned<inner::Effect>;
pub type EffectDefinition = Spanned<inner::EffectDefinition>;
pub type EffectBody = Spanned<inner::EffectBody>;
