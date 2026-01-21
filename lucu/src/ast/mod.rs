pub mod inner;
pub mod visit;

use crate::span::Spanned;

pub type String = Spanned<inner::String>;
pub type Ident = Spanned<inner::Ident>;
pub type Module = Spanned<inner::Module>;
pub type Import = Spanned<inner::Import>;
pub type Definition = Spanned<inner::Definition>;
pub type TypeDefinition = Spanned<inner::TypeDefinition>;
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
pub type FunctionDefinition = Spanned<inner::FunctionDefinition>;
pub type Returns = Spanned<inner::Returns>;
pub type EffectDefinition = Spanned<inner::EffectDefinition>;
pub type EffectBody = Spanned<inner::EffectBody>;
