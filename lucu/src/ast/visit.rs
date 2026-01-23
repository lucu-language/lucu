use std::hash::Hash;

use crate::ast::{self, inner};
use crate::span::HasSpan;

pub trait Visitor: Copy {
    type Output<'a>: Default + Combine;
    fn visit_path(self, path: &ast::Path) -> Self::Output<'_> {
        self.visit(path)
    }
    fn visit_definition(self, def: &ast::Definition) -> Self::Output<'_> {
        self.visit(def)
    }
    fn visit_struct(self, struc: &ast::Struct) -> Self::Output<'_> {
        self.visit(struc)
    }
    fn visit_function_definition(self, function: &ast::FunctionDefinition) -> Self::Output<'_> {
        self.visit(function)
    }
    fn visit_effect_body(self, body: &ast::EffectBody) -> Self::Output<'_> {
        self.visit(body)
    }
    fn visit(self, ast: &impl Ast) -> Self::Output<'_> {
        ast.visit(self)
    }
}

pub fn visit_option<V: Visitor>(ast: &Option<impl Ast>, visitor: V) -> V::Output<'_> {
    match ast {
        Some(t) => visitor.visit(t),
        None => V::Output::default(),
    }
}

pub fn visit_vec<V: Visitor>(
    #[expect(clippy::ptr_arg)] ast: &Vec<impl Ast>,
    visitor: V,
) -> V::Output<'_> {
    V::Output::combine(ast.iter().map(|inner| visitor.visit(inner)))
}

pub fn visit_option_vec<V: Visitor>(ast: &Option<Vec<impl Ast>>, visitor: V) -> V::Output<'_> {
    match ast {
        Some(ast) => V::Output::combine(ast.iter().map(|inner| visitor.visit(inner))),
        None => V::Output::default(),
    }
}

pub trait Combine {
    fn combine(iter: impl IntoIterator<Item = Self>) -> Self;
}

impl Combine for () {
    fn combine(_iter: impl IntoIterator<Item = Self>) -> Self {}
}

impl<T: Clone> Combine for im::Vector<T> {
    fn combine(iter: impl IntoIterator<Item = Self>) -> Self {
        let mut iter = iter.into_iter();
        let mut combined = iter.next().unwrap_or_default();
        for vec in iter {
            combined.append(vec);
        }
        combined
    }
}

impl<T: Clone + Hash + Eq> Combine for im::HashSet<T> {
    fn combine(iter: impl IntoIterator<Item = Self>) -> Self {
        let mut iter = iter.into_iter();
        let mut combined = iter.next().unwrap_or_default();
        for set in iter {
            combined.extend(set);
        }
        combined
    }
}

impl<K: Clone + Hash + Eq, V: Clone> Combine for im::HashMap<K, V> {
    fn combine(iter: impl IntoIterator<Item = Self>) -> Self {
        let mut iter = iter.into_iter();
        let mut combined = iter.next().unwrap_or_default();
        for map in iter {
            combined.extend(map);
        }
        combined
    }
}

pub trait Ast: HasSpan {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_>;
    fn node_name(&self) -> &'static str;
}

impl Ast for ast::Module {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visit_vec(&self.0.imports, visitor),
            V::Output::combine(
                self.0
                    .definitions
                    .iter()
                    .map(|def| visitor.visit_definition(def)),
            ),
        ])
    }
    fn node_name(&self) -> &'static str {
        "Module"
    }
}

impl Ast for ast::Import {
    fn visit<V: Visitor>(&self, _visitor: V) -> V::Output<'_> {
        V::Output::default()
    }
    fn node_name(&self) -> &'static str {
        "Import"
    }
}

impl Ast for ast::Definition {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            inner::Definition::Function(fun, opt) => V::Output::combine([
                visitor.visit(fun),
                match opt {
                    Some(def) => visitor.visit_function_definition(def),
                    None => V::Output::default(),
                },
            ]),
            inner::Definition::Type(name, opt) => {
                V::Output::combine([visitor.visit(name), visit_option(opt, visitor)])
            }
            inner::Definition::Effect(name, opt) => {
                V::Output::combine([visitor.visit(name), visit_option(opt, visitor)])
            }
            inner::Definition::Handle(generics, handler) => {
                V::Output::combine([visit_option_vec(generics, visitor), visitor.visit(handler)])
            }
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::Handler {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visitor.visit_path(&self.effect),
            V::Output::combine(
                self.definitions
                    .iter()
                    .map(|def| visitor.visit_definition(def)),
            ),
        ])
    }
    fn node_name(&self) -> &'static str {
        "Handler"
    }
}

impl Ast for ast::EffectDefinition {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            inner::EffectDefinition::Body(body) => visitor.visit_effect_body(body),
            inner::EffectDefinition::Alias(alias) => {
                V::Output::combine(alias.iter().map(|inner| visitor.visit_path(inner)))
            }
            inner::EffectDefinition::Intrinsic => V::Output::default(),
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::EffectBody {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine(
            self.definitions
                .iter()
                .map(|def| visitor.visit_definition(def)),
        )
    }
    fn node_name(&self) -> &'static str {
        "EffectBody"
    }
}

impl Ast for ast::FunctionDefinition {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            inner::FunctionDefinition::Expression(spanned) => visitor.visit(&**spanned),
            inner::FunctionDefinition::Intrinsic => V::Output::default(),
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::FunctionDeclaration {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visitor.visit(&self.0.name),
            visit_option_vec(&self.0.parameters, visitor),
            visit_option(&self.0.returns, visitor),
            match &self.0.effects {
                Some(ast) => V::Output::combine(ast.iter().map(|inner| visitor.visit_path(inner))),
                None => V::Output::default(),
            },
        ])
    }
    fn node_name(&self) -> &'static str {
        "FunctionDeclaration"
    }
}

impl Ast for ast::Returns {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            inner::Returns::Never => V::Output::default(),
            inner::Returns::Data(ty) => visitor.visit(&**ty),
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::FunctionParameter {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            inner::FunctionParameter::Data(name, ty) => {
                V::Output::combine([visitor.visit(name), visitor.visit(&**ty)])
            }
            inner::FunctionParameter::Lambda(decl) => visitor.visit(decl),
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::Name {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visitor.visit(&self.0.ident),
            visit_option_vec(&self.0.generics, visitor),
        ])
    }
    fn node_name(&self) -> &'static str {
        "Name"
    }
}

impl Ast for ast::GenericParameter {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visitor.visit(&self.0.name),
            visit_option(&self.0.kind, visitor),
        ])
    }
    fn node_name(&self) -> &'static str {
        "GenericParameter"
    }
}

impl Ast for ast::Kind {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            inner::Kind::Type => V::Output::default(),
            inner::Kind::Effect => V::Output::default(),
            inner::Kind::Region => V::Output::default(),
            inner::Kind::Constant(ty) => visitor.visit(&**ty),
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::Type {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            inner::Type::Pointer(inner, region)
            | inner::Type::PointerSlice(inner, region)
            | inner::Type::PointerSliceNullTerminated(inner, region) => V::Output::combine([
                visitor.visit(&**inner),
                match region {
                    Some(t) => visitor.visit_path(t),
                    None => V::Output::default(),
                },
            ]),
            inner::Type::Path(path) => visitor.visit_path(path),
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::Expression {
    fn visit<V: Visitor>(&self, _visitor: V) -> V::Output<'_> {
        match &self.0 {
            inner::Expression::Block => V::Output::default(),
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::TypeDefinition {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            inner::TypeDefinition::Type(spanned) => visitor.visit(&**spanned),
            inner::TypeDefinition::Intrinsic => V::Output::default(),
            inner::TypeDefinition::Struct(struc) => visitor.visit_struct(struc),
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::Path {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visit_option(&self.0.package, visitor),
            visitor.visit(&self.0.name),
            visit_option_vec(&self.0.generics, visitor),
        ])
    }
    fn node_name(&self) -> &'static str {
        "Path"
    }
}

impl Ast for ast::GenericArgument {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            inner::GenericArgument::Path(path) => visitor.visit_path(path),
            inner::GenericArgument::Type(ty) => visitor.visit(&**ty),
            inner::GenericArgument::Constant(constant) => visitor.visit(&**constant),
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::Constant {
    fn visit<V: Visitor>(&self, _visitor: V) -> V::Output<'_> {
        match self.0 {}
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::Struct {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        visit_vec(&self.0.members, visitor)
    }
    fn node_name(&self) -> &'static str {
        "Struct"
    }
}

impl Ast for ast::StructMember {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            inner::StructMember::Data(name, ty) => {
                V::Output::combine([visitor.visit(name), visitor.visit(&**ty)])
            }
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::String {
    fn visit<V: Visitor>(&self, _visitor: V) -> V::Output<'_> {
        V::Output::default()
    }
    fn node_name(&self) -> &'static str {
        "String"
    }
}

impl Ast for ast::Ident {
    fn visit<V: Visitor>(&self, _visitor: V) -> V::Output<'_> {
        V::Output::default()
    }
    fn node_name(&self) -> &'static str {
        "Ident"
    }
}
