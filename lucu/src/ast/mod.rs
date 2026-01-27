pub mod visit;

use std::fmt;

use compact_str::CompactString;
use strum::IntoStaticStr;

use crate::span::{HasSpan, Span};
use crate::tokens;

#[derive(Debug, Eq, Clone, Copy)]
pub struct Token(pub Span);

impl Token {
    pub fn with(self, token: impl Into<tokens::TokenEnum>) -> tokens::Token {
        tokens::Token {
            token: token.into(),
            span: self.0,
        }
    }
}

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
pub struct Ident {
    pub token: Token,
    pub value: CompactString,
}

impl Ident {
    pub fn as_str(&self) -> &str {
        &self.value
    }
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
    pub ident: Option<Ident>,
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Item::")]
pub enum Item {
    Function(FunctionDeclaration, Option<(Token, FunctionDefinition)>),
    Type(Token, Name, Option<(Token, TypeDefinition)>),
    Effect(Token, Name, Option<(Token, EffectDefinition)>),
    Handle(Token, Option<GenericParameters>, Handler),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Grouped<T> {
    pub open: Token,
    pub inner: T,
    pub close: Token,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Separated<T> {
    pub elements: Vec<(T, Option<Token>)>,
}

impl<T> Separated<T> {
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &T> + DoubleEndedIterator {
        self.elements.iter().map(|(t, _)| t)
    }
}

pub type GenericParameters = Grouped<Separated<GenericParameter>>;

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Kind::")]
pub enum Kind {
    Type(Token),
    Effect(Token),
    Region(Token),
    Constant(Box<Type>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Name {
    pub ident: Ident,
    pub generics: Option<GenericParameters>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct GenericParameter {
    pub name: Name,
    pub kind: Option<Kind>,
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "GenericArgument::")]
pub enum GenericArgument {
    Path(Path),
    Type(Box<Type>),
    Constant(Box<Constant>),
}

#[derive(PartialEq, Eq)]
pub struct Path {
    pub package: Option<(Ident, Token)>,
    pub name: Ident,
    pub generics: Option<GenericArguments>,
}

pub type GenericArguments = Grouped<Separated<GenericArgument>>;

#[derive(Debug, PartialEq, Eq)]
pub struct NullTerminated {
    pub colon: Token,
    pub zero: Token,
}

#[derive(Debug, PartialEq, Eq)]
pub struct PointerRegion {
    pub at: Token,
    pub region: Path,
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Type::")]
pub enum Type {
    Path(Path),
    Pointer(Token, Option<PointerRegion>, Box<Type>),
    PointerSlice(Token, Grouped<()>, Option<PointerRegion>, Box<Type>),
    PointerSliceNullTerminated(
        Token,
        Grouped<NullTerminated>,
        Option<PointerRegion>,
        Box<Type>,
    ),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Constant::")]
pub enum Constant {
    // TODO
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
    Never(Token),
    Data(Box<Type>),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "FunctionParameter::")]
pub enum Parameter {
    Data(Ident, Box<Type>),
    Lambda(FunctionDeclaration),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Struct {
    pub r#struct: Token,
    pub members: Grouped<Separated<StructMember>>,
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "StructMember::")]
pub enum StructMember {
    Data(Ident, Box<Type>),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "TypeDefinition::")]
pub enum TypeDefinition {
    Type(Box<Type>),
    Struct(Struct),
    Intrinsic(Token),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "FunctionDefinition::")]
pub enum FunctionDefinition {
    Expression(Box<Expression>),
    Intrinsic(Token),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Expression::")]
pub enum Expression {
    Block(Grouped<()>),
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "EffectDefinition::")]
pub enum EffectDefinition {
    Body(EffectBody),
    Alias(Vec<Path>),
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

impl fmt::Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.package {
            Some((pkg, _)) => write!(f, "\"{}.{}\"", pkg.value, self.name.value),
            None => write!(f, "\"{}\"", self.name.value),
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

impl HasSpan for Ident {
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
            Item::Effect(token, name, def) => {
                let start = token.span().start;
                let end = def
                    .as_ref()
                    .map(|(equals, def)| {
                        if matches!(def, EffectDefinition::Alias(a) if a.is_empty()) {
                            equals.span()
                        } else {
                            def.span()
                        }
                    })
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
            .expect("ICE: trying to get span of empty separated")
            .0
            .span()
            .start;
        let (t, sep) = self.elements.last().unwrap();
        let end = sep
            .as_ref()
            .map(HasSpan::span)
            .unwrap_or_else(|| t.span())
            .end;
        Span { start, end }
    }
}

impl HasSpan for GenericParameter {
    fn span(&self) -> Span {
        let start = self.name.span().start;
        let end = self
            .kind
            .as_ref()
            .map(HasSpan::span)
            .unwrap_or_else(|| self.name.span())
            .end;
        Span { start, end }
    }
}

impl HasSpan for Type {
    fn span(&self) -> Span {
        match self {
            Type::Path(path) => path.span(),
            Type::Pointer(token, _, ty)
            | Type::PointerSlice(token, _, _, ty)
            | Type::PointerSliceNullTerminated(token, _, _, ty) => {
                let start = token.span().start;
                let end = ty.span().end;
                Span { start, end }
            }
        }
    }
}

impl HasSpan for Path {
    fn span(&self) -> Span {
        let start = self
            .package
            .as_ref()
            .map(|(pkg, _)| pkg.span())
            .unwrap_or_else(|| self.name.span())
            .start;
        let end = self
            .generics
            .as_ref()
            .map(HasSpan::span)
            .unwrap_or_else(|| self.name.span())
            .end;
        Span { start, end }
    }
}

impl HasSpan for GenericArgument {
    fn span(&self) -> Span {
        match self {
            GenericArgument::Path(path) => path.span(),
            GenericArgument::Type(ty) => ty.span(),
            GenericArgument::Constant(constant) => constant.span(),
        }
    }
}

impl HasSpan for Constant {
    fn span(&self) -> Span {
        match *self {}
    }
}

impl HasSpan for Kind {
    fn span(&self) -> Span {
        match self {
            Kind::Type(token) => token.span(),
            Kind::Effect(token) => token.span(),
            Kind::Region(token) => token.span(),
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

impl HasSpan for NullTerminated {
    fn span(&self) -> Span {
        let start = self.colon.span().start;
        let end = self.zero.span().end;
        Span { start, end }
    }
}

impl HasSpan for PointerRegion {
    fn span(&self) -> Span {
        let start = self.at.span().start;
        let end = self.region.span().end;
        Span { start, end }
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
            Returns::Never(token) => token.span(),
            Returns::Data(ty) => ty.span(),
        }
    }
}

impl<T: HasSpan> HasSpan for Vec<T> {
    fn span(&self) -> Span {
        let start = self
            .first()
            .expect("ICE: trying to get span of empty vec")
            .span()
            .start;
        let end = self.last().unwrap().span().end;
        Span { start, end }
    }
}

impl HasSpan for WithEffects {
    fn span(&self) -> Span {
        let start = self.with.span().start;
        let end = self.effects.span().end;
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

impl HasSpan for Expression {
    fn span(&self) -> Span {
        match self {
            Expression::Block(grouped) => grouped.span(),
        }
    }
}

impl HasSpan for FunctionDefinition {
    fn span(&self) -> Span {
        match self {
            FunctionDefinition::Expression(expression) => expression.span(),
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
            EffectDefinition::Alias(paths) => paths.span(),
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
            Item::Type(_, name, _) => Some(name),
            Item::Effect(_, name, _) => Some(name),
            Item::Handle(_, _, _) => None,
        }
    }
    pub fn generics(&self) -> &Separated<GenericParameter> {
        match self {
            Item::Function(fun, _) => fun.name.generics.as_ref(),
            Item::Type(_, name, _) => name.generics.as_ref(),
            Item::Effect(_, name, _) => name.generics.as_ref(),
            Item::Handle(_, params, _) => params.as_ref(),
        }
        .map(|g| &g.inner)
        .unwrap_or(
            const {
                &Separated {
                    elements: Vec::new(),
                }
            },
        )
    }
    pub fn children(&self) -> &Separated<Item> {
        match self {
            Item::Effect(_, _, Some((_, EffectDefinition::Body(body)))) => &body.items.inner,
            _ => {
                const {
                    &Separated {
                        elements: Vec::new(),
                    }
                }
            }
        }
    }
}
