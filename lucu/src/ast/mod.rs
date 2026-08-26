mod expr;
pub mod visit;

use std::fmt;

use compact_str::CompactString;
pub use expr::*;
use strum::IntoStaticStr;

use crate::span::{HasSpan, Span};

#[derive(Debug, Eq, Clone, Copy)]
pub struct Token(pub Span);

impl PartialEq for Token {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct String {
    pub token: Token,
    pub value: CompactString,
}

impl String {
    pub fn as_str(&self) -> &str {
        &self.value
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Character {
    pub token: Token,
    pub value: CompactString,
}

impl Character {
    pub fn as_str(&self) -> &str {
        &self.value
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Identifier {
    pub token: Token,
    pub value: CompactString,
}

impl Identifier {
    pub fn as_str(&self) -> &str {
        &self.value
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Integer {
    pub token: Token,
    pub value: u64,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Module {
    pub imports: Separated<Import>,
    pub items: Separated<Item>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Import {
    pub import: Token,
    pub path: String,
    pub ident: Option<Identifier>,
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Item::")]
pub enum Item {
    Function(FunctionDeclaration, Option<(Token, FunctionDefinition)>),
    Type(Token, Name, Option<(Token, TypeDefinition)>),
    Effect(Token, Name, Option<(Token, EffectDefinition)>),
    Region(Token, Name, Option<(Token, RegionDefinition)>),
    Constant(Token, Name, Box<Type>, Option<(Token, ConstantDefinition)>),
    Handle(Token, Option<GenericParameters>, Handler),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Grouped<T> {
    pub open: Token,
    pub inner: T,
    pub close: Token,
}

#[derive(Debug, Eq)]
pub struct Separated<T> {
    pub elements: Vec<(T, Option<Token>)>,
    pub end: u32,
}

impl<T> Separated<T> {
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &T> + DoubleEndedIterator {
        self.elements.iter().map(|(t, _)| t)
    }
}

impl<T: PartialEq> PartialEq for Separated<T> {
    fn eq(&self, other: &Self) -> bool {
        // ignore trailing comma or not
        self.iter().eq(other.iter())
    }
}

pub type GenericParameters = Grouped<Separated<GenericParameter>>;

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Kind::")]
pub enum Kind {
    Type(Token),
    Effect(Token),
    Region(Token),
    Thunk(Token),
    Constant(Box<Type>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Name {
    pub ident: Identifier,
    pub generics: Option<GenericParameters>,
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "RegionKind::")]
pub enum RegionKind {
    None(Token),
    ReadWrite(Token),
    Write(Token),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "GenericParameter::")]
pub enum GenericParameter {
    Type(Name),
    Region(Option<RegionKind>, Identifier),
    Other(Name, Kind),
}

impl GenericParameter {
    pub fn ident(&self) -> &Identifier {
        match self {
            GenericParameter::Type(name) => &name.ident,
            GenericParameter::Region(_, ident) => ident,
            GenericParameter::Other(name, _) => &name.ident,
        }
    }
    pub fn generics(&self) -> Option<&GenericParameters> {
        match self {
            GenericParameter::Type(name) => name.generics.as_ref(),
            GenericParameter::Region(_, _) => None,
            GenericParameter::Other(name, _) => name.generics.as_ref(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "GenericArgument::")]
pub enum GenericArgument {
    Path(Path, Option<WithEffects>),
    Type(Box<Type>, Option<WithEffects>),
    Constant(Box<Constant>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Path {
    pub origin: PathOrigin,
    pub generics: Option<GenericArguments>,
}

#[derive(PartialEq, Eq)]
pub enum PathOrigin {
    Package(Identifier, Token, Identifier),
    Local(Identifier),
    Underscore(Token),
}

pub type GenericArguments = Grouped<Separated<GenericArgument>>;

#[derive(Debug, PartialEq, Eq)]
pub struct Sentinel {
    pub colon: Token,
    pub zero: Token,
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "PointerRegion::")]
pub enum PointerRegion {
    At(Token, Path),
    Kind(RegionKind),
}

#[derive(Debug, Eq)]
pub struct ArrayProperties {
    pub size: Option<Box<Constant>>,
    pub sentinel: Option<Sentinel>,
    pub end: u32,
}

impl PartialEq for ArrayProperties {
    fn eq(&self, other: &Self) -> bool {
        self.size == other.size && self.sentinel == other.sentinel
    }
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Type::")]
pub enum Type {
    Path(Path),
    Maybe(Token, Box<Type>),
    Array(Grouped<ArrayProperties>, Box<Type>),
    Pointer(Token, Option<PointerRegion>, Box<Type>),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Constant::")]
pub enum Constant {
    Path(Path),
    Integer(Integer),
    String(String),
    Character(Character),
    Zero(Token),
}

#[derive(Debug, PartialEq, Eq)]
pub struct FunctionDeclaration {
    pub fun: Token,
    pub name: Name,
    pub parameters: Option<Parameters>,
    pub returns: Option<Returns>,
    pub effects: Option<WithEffects>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct WithEffects {
    pub with: Token,
    pub effects: Vec<Path>,
}

pub type Parameters = Grouped<Separated<Parameter>>;

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "FunctionReturns::")]
pub enum Returns {
    Path(Path),
    Type(Box<Type>),
    Never(Token),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "FunctionParameter::")]
pub enum Parameter {
    Data(Identifier, Box<Type>),
    Lambda(FunctionDeclaration),
}

impl Parameter {
    pub fn name(&self) -> &Identifier {
        match self {
            Parameter::Data(ident, _) => ident,
            Parameter::Lambda(decl) => &decl.name.ident,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Struct {
    pub r#struct: Token,
    pub members: Grouped<Separated<StructMember>>,
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "StructMember::")]
pub enum StructMember {
    Data(Identifier, Box<Type>),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "TypeDefinition::")]
pub enum TypeDefinition {
    Type(Box<Type>),
    Struct(Struct),
    Intrinsic(Token),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "ConstantDefinition::")]
pub enum ConstantDefinition {
    Constant(Box<Constant>),
    Intrinsic(Token),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "FunctionDefinition::")]
pub enum FunctionDefinition {
    Expression {
        inline: Option<Token>,
        body: Box<Expression>,
    },
    Intrinsic(Token),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "EffectDefinition::")]
pub enum EffectDefinition {
    Body(EffectBody),
    Alias(Vec<Path>),
    Intrinsic(Token),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "RegionDefinition::")]
pub enum RegionDefinition {
    Alias(Path),
    Intrinsic(Token),
}

#[derive(Debug, PartialEq, Eq)]
pub struct EffectBody {
    pub items: Grouped<Separated<Item>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Handler {
    pub effect: Path,
    pub with_effects: Option<WithEffects>,
    pub items: Grouped<Separated<Item>>,
}

impl fmt::Debug for PathOrigin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathOrigin::Package(pkg, _, id) => write!(f, "\"{}.{}\"", pkg.value, id.value),
            PathOrigin::Local(id) => write!(f, "\"{}\"", id.value),
            PathOrigin::Underscore(_) => write!(f, "\"_\""),
        }
    }
}

impl HasSpan for Token {
    fn span(&self) -> Span {
        self.0
    }
}

impl HasSpan for String {
    fn span(&self) -> Span {
        self.token.0
    }
}

impl HasSpan for Identifier {
    fn span(&self) -> Span {
        self.token.0
    }
}

impl HasSpan for Module {
    fn span(&self) -> Span {
        let start = self
            .imports
            .elements
            .first()
            .map(|(e, _)| e.span())
            .or_else(|| self.items.elements.first().map(|(e, _)| e.span()))
            .map(|s| s.start)
            .unwrap_or(0);
        let end = self
            .items
            .elements
            .last()
            .map(|(e, _)| e.span())
            .or_else(|| self.imports.elements.last().map(|(e, _)| e.span()))
            .map(|s| s.end)
            .unwrap_or(0);
        Span { start, end }
    }
}

impl HasSpan for Import {
    fn span(&self) -> Span {
        Span {
            start: self.import.span().start,
            end: self
                .ident
                .as_ref()
                .map(HasSpan::span)
                .unwrap_or_else(|| self.path.span())
                .end,
        }
    }
}

impl HasSpan for Item {
    fn span(&self) -> Span {
        match self {
            Item::Function(decl, def) => {
                let start = decl.span().start;
                let end = def
                    .as_ref()
                    .map(|(_, def)| def.span())
                    .unwrap_or_else(|| decl.span())
                    .end;
                Span { start, end }
            }
            Item::Type(token, name, def) => {
                let start = token.span().start;
                let end = def
                    .as_ref()
                    .map(|(_, def)| def.span())
                    .unwrap_or_else(|| name.span())
                    .end;
                Span { start, end }
            }
            Item::Constant(token, _, ty, def) => {
                let start = token.span().start;
                let end = def
                    .as_ref()
                    .map(|(_, def)| def.span())
                    .unwrap_or_else(|| ty.span())
                    .end;
                Span { start, end }
            }
            Item::Region(token, name, def) => {
                let start = token.span().start;
                let end = def
                    .as_ref()
                    .map(|(_, def)| def.span())
                    .unwrap_or_else(|| name.span())
                    .end;
                Span { start, end }
            }
            Item::Effect(token, name, def) => {
                let start = token.span().start;
                let end = def
                    .as_ref()
                    .map(|(_, def)| def.span())
                    .unwrap_or_else(|| name.span())
                    .end;
                Span { start, end }
            }
            Item::Handle(token, _, handler) => {
                let start = token.span().start;
                let end = handler.span().end;
                Span { start, end }
            }
        }
    }
}

impl HasSpan for RegionDefinition {
    fn span(&self) -> Span {
        match self {
            RegionDefinition::Alias(path) => path.span(),
            RegionDefinition::Intrinsic(token) => token.span(),
        }
    }
}

impl HasSpan for ConstantDefinition {
    fn span(&self) -> Span {
        match self {
            ConstantDefinition::Constant(constant) => constant.span(),
            ConstantDefinition::Intrinsic(token) => token.span(),
        }
    }
}

impl<T> HasSpan for Grouped<T> {
    fn span(&self) -> Span {
        Span {
            start: self.open.span().start,
            end: self.close.span().end,
        }
    }
}

impl<T: HasSpan> HasSpan for Separated<T> {
    fn span(&self) -> Span {
        let start = self
            .elements
            .first()
            .map(|(t, _)| t.span().end)
            .unwrap_or(self.end);
        let end = self.end;
        Span { start, end }
    }
}

impl HasSpan for RegionKind {
    fn span(&self) -> Span {
        match self {
            RegionKind::ReadWrite(token) | RegionKind::None(token) | RegionKind::Write(token) => {
                token.span()
            }
        }
    }
}

impl HasSpan for GenericParameter {
    fn span(&self) -> Span {
        match self {
            GenericParameter::Type(name) => name.span(),
            GenericParameter::Region(token, identifier) => {
                let start = token
                    .as_ref()
                    .map(HasSpan::span)
                    .unwrap_or_else(|| identifier.span())
                    .start;
                let end = identifier.span().end;
                Span { start, end }
            }
            GenericParameter::Other(name, kind) => {
                let start = name.span().start;
                let end = kind.span().end;
                Span { start, end }
            }
        }
    }
}

impl HasSpan for ArrayProperties {
    fn span(&self) -> Span {
        let start = self
            .size
            .as_ref()
            .map(|c| c.span().start)
            .or_else(|| self.sentinel.as_ref().map(|s| s.span().start))
            .unwrap_or(self.end);
        let end = self.end;
        Span { start, end }
    }
}

impl HasSpan for Type {
    fn span(&self) -> Span {
        match self {
            Type::Path(path) => path.span(),
            Type::Array(group, ty) => {
                let start = group.span().start;
                let end = ty.span().end;
                Span { start, end }
            }
            Type::Pointer(token, _, ty) | Type::Maybe(token, ty) => {
                let start = token.span().start;
                let end = ty.span().end;
                Span { start, end }
            }
        }
    }
}

impl HasSpan for PathOrigin {
    fn span(&self) -> Span {
        match self {
            PathOrigin::Package(pkg, _, id) => Span {
                start: pkg.span().start,
                end: id.span().end,
            },
            PathOrigin::Local(id) => id.span(),
            PathOrigin::Underscore(token) => token.span(),
        }
    }
}

impl HasSpan for Path {
    fn span(&self) -> Span {
        let start = self.origin.span().start;
        let end = self
            .generics
            .as_ref()
            .map(HasSpan::span)
            .unwrap_or_else(|| self.origin.span())
            .end;
        Span { start, end }
    }
}

impl HasSpan for GenericArgument {
    fn span(&self) -> Span {
        match self {
            GenericArgument::Path(path, effects) => {
                let start = path.span().start;
                let end = effects
                    .as_ref()
                    .map(HasSpan::span)
                    .unwrap_or_else(|| path.span())
                    .end;
                Span { start, end }
            }
            GenericArgument::Type(ty, effects) => {
                let start = ty.span().start;
                let end = effects
                    .as_ref()
                    .map(HasSpan::span)
                    .unwrap_or_else(|| ty.span())
                    .end;
                Span { start, end }
            }
            GenericArgument::Constant(constant) => constant.span(),
        }
    }
}

impl HasSpan for Integer {
    fn span(&self) -> Span {
        self.token.span()
    }
}

impl HasSpan for Character {
    fn span(&self) -> Span {
        self.token.span()
    }
}

impl HasSpan for Constant {
    fn span(&self) -> Span {
        match self {
            Constant::Path(path) => path.span(),
            Constant::Integer(integer) => integer.span(),
            Constant::String(string) => string.span(),
            Constant::Character(character) => character.span(),
            Constant::Zero(token) => token.span(),
        }
    }
}

impl HasSpan for Kind {
    fn span(&self) -> Span {
        match self {
            Kind::Type(token) => token.span(),
            Kind::Effect(token) => token.span(),
            Kind::Region(token) => token.span(),
            Kind::Thunk(token) => token.span(),
            Kind::Constant(ty) => ty.span(),
        }
    }
}

impl HasSpan for Name {
    fn span(&self) -> Span {
        let start = self.ident.span().start;
        let end = self
            .generics
            .as_ref()
            .map(HasSpan::span)
            .unwrap_or_else(|| self.ident.span())
            .end;
        Span { start, end }
    }
}

impl HasSpan for Sentinel {
    fn span(&self) -> Span {
        let start = self.colon.span().start;
        let end = self.zero.span().end;
        Span { start, end }
    }
}

impl HasSpan for PointerRegion {
    fn span(&self) -> Span {
        match self {
            PointerRegion::At(at, region) => {
                let start = at.span().start;
                let end = region.span().end;
                Span { start, end }
            }
            PointerRegion::Kind(region_kind) => region_kind.span(),
        }
    }
}

impl HasSpan for Parameter {
    fn span(&self) -> Span {
        match self {
            Parameter::Data(ident, ty) => {
                let start = ident.span().start;
                let end = ty.span().end;
                Span { start, end }
            }
            Parameter::Lambda(function_declaration) => function_declaration.span(),
        }
    }
}

impl HasSpan for FunctionDeclaration {
    fn span(&self) -> Span {
        let start = self.fun.span().start;
        let end = self
            .effects
            .as_ref()
            .map(HasSpan::span)
            .or_else(|| self.returns.as_ref().map(HasSpan::span))
            .or_else(|| self.parameters.as_ref().map(HasSpan::span))
            .unwrap_or_else(|| self.name.span())
            .end;
        Span { start, end }
    }
}

impl HasSpan for Returns {
    fn span(&self) -> Span {
        match self {
            Returns::Path(path) => path.span(),
            Returns::Type(ty) => ty.span(),
            Returns::Never(token) => token.span(),
        }
    }
}

impl HasSpan for WithEffects {
    fn span(&self) -> Span {
        let start = self.with.span().start;
        let end = self
            .effects
            .last()
            .map(HasSpan::span)
            .unwrap_or_else(|| self.with.span())
            .end;
        Span { start, end }
    }
}

impl HasSpan for Struct {
    fn span(&self) -> Span {
        let start = self.r#struct.span().start;
        let end = self.members.span().end;
        Span { start, end }
    }
}

impl HasSpan for StructMember {
    fn span(&self) -> Span {
        match self {
            StructMember::Data(ident, ty) => {
                let start = ident.span().start;
                let end = ty.span().end;
                Span { start, end }
            }
        }
    }
}

impl HasSpan for TypeDefinition {
    fn span(&self) -> Span {
        match self {
            TypeDefinition::Type(ty) => ty.span(),
            TypeDefinition::Struct(struc) => struc.span(),
            TypeDefinition::Intrinsic(token) => token.span(),
        }
    }
}

impl HasSpan for FunctionDefinition {
    fn span(&self) -> Span {
        match self {
            FunctionDefinition::Expression { inline, body } => {
                let start = inline
                    .map(|t| t.span().start)
                    .unwrap_or_else(|| body.span().start);
                let end = body.span().end;
                Span::new(start, end)
            }
            FunctionDefinition::Intrinsic(token) => token.span(),
        }
    }
}

impl HasSpan for EffectBody {
    fn span(&self) -> Span {
        self.items.span()
    }
}

impl HasSpan for EffectDefinition {
    fn span(&self) -> Span {
        match self {
            EffectDefinition::Body(effect_body) => effect_body.span(),
            EffectDefinition::Alias(paths) => {
                let start = paths.first().expect("ICE: empty effect alias").span().start;
                let end = paths.last().unwrap().span().end;
                Span { start, end }
            }
            EffectDefinition::Intrinsic(token) => token.span(),
        }
    }
}

impl HasSpan for Handler {
    fn span(&self) -> Span {
        let start = self.effect.span().start;
        let end = self.items.span().end;
        Span { start, end }
    }
}

impl Item {
    pub fn name(&self) -> Option<&Name> {
        match self {
            Item::Function(fun, _) => Some(&fun.name),
            Item::Type(_, name, _)
            | Item::Effect(_, name, _)
            | Item::Region(_, name, _)
            | Item::Constant(_, name, _, _) => Some(name),
            Item::Handle(_, _, _) => None,
        }
    }
    pub fn generics(&self) -> Option<&GenericParameters> {
        match self {
            Item::Function(fun, _) => fun.name.generics.as_ref(),
            Item::Type(_, name, _)
            | Item::Effect(_, name, _)
            | Item::Region(_, name, _)
            | Item::Constant(_, name, _, _) => name.generics.as_ref(),
            Item::Handle(_, params, _) => params.as_ref(),
        }
    }
    pub fn children(&self) -> Option<&Separated<Item>> {
        match self {
            Item::Effect(_, _, Some((_, EffectDefinition::Body(body)))) => Some(&body.items.inner),
            _ => None,
        }
    }
}
