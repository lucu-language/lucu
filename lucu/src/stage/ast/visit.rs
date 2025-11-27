use std::hash::Hash;

use crate::span::HasSpan;
use crate::stage::ast::{self, inner};

pub trait Visitor: Copy {
    type Output<'a>: Default + Combine;
    fn visit_path(self, path: &ast::Path) -> Self::Output<'_> {
        self.visit(path)
    }
    fn visit_function(self, function: &ast::Function) -> Self::Output<'_> {
        self.visit(function)
    }
    fn visit_struct(self, struc: &ast::Struct) -> Self::Output<'_> {
        self.visit(struc)
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
            visit_vec(&self.0.definitions, visitor),
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
            inner::Definition::Function(function) => visitor.visit_function(function),
            inner::Definition::Type(type_alias) => visitor.visit(type_alias),
        }
    }
    fn node_name(&self) -> &'static str {
        (&self.0).into()
    }
}

impl Ast for ast::Function {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visitor.visit(&self.0.declaration),
            visitor.visit(&*self.0.definition),
        ])
    }
    fn node_name(&self) -> &'static str {
        "Function"
    }
}

impl Ast for ast::FunctionDeclaration {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visitor.visit(&self.0.name),
            visit_option_vec(&self.0.parameters, visitor),
            visit_option(&self.0.returns, visitor),
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
            inner::Type::Int => V::Output::default(),
            inner::Type::Path(path) => visitor.visit_path(path),
            inner::Type::Struct(struc) => visitor.visit_struct(struc),
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

impl Ast for ast::TypeAlias {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visitor.visit(&self.0.name),
            visitor.visit(&*self.0.definition),
        ])
    }
    fn node_name(&self) -> &'static str {
        "TypeAlias"
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
