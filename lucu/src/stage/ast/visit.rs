use std::hash::Hash;

use crate::stage::ast;

pub trait Visitor: Copy {
    type Output<'a>: Default + Combine;
    fn visit_path(self, path: &ast::Path) -> Self::Output<'_> {
        Self::Output::combine([path.package.visit(self), path.name.visit(self)])
    }
    fn visit_function(self, function: &ast::Function) -> Self::Output<'_> {
        Self::Output::combine([
            function.declaration.visit(self),
            function.definition.visit(self),
        ])
    }
    fn visit_struct(self, struc: &ast::Struct) -> Self::Output<'_> {
        struc.members.visit(self)
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

pub trait Ast {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_>;
}

impl<T> Ast for Option<T>
where
    T: Ast,
{
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            Some(t) => t.visit(visitor),
            None => V::Output::default(),
        }
    }
}

impl<T> Ast for Vec<T>
where
    T: Ast,
{
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine(self.iter().map(|inner| inner.visit(visitor)))
    }
}

impl Ast for ast::Module {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([self.imports.visit(visitor), self.definitions.visit(visitor)])
    }
}

impl Ast for ast::Import {
    fn visit<V: Visitor>(&self, _visitor: V) -> V::Output<'_> {
        V::Output::default()
    }
}

impl Ast for ast::Definition {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            ast::DefinitionEnum::Function(function) => function.visit(visitor),
            ast::DefinitionEnum::Type(type_alias) => type_alias.visit(visitor),
        }
    }
}

impl Ast for ast::Function {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        visitor.visit_function(self)
    }
}

impl Ast for ast::FunctionDeclaration {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            self.name.visit(visitor),
            self.parameters.visit(visitor),
            self.returns.visit(visitor),
        ])
    }
}

impl Ast for ast::Returns {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            ast::ReturnsEnum::Never => V::Output::default(),
            ast::ReturnsEnum::Data(ty) => ty.visit(visitor),
        }
    }
}

impl Ast for ast::FunctionParameter {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::FunctionParameter::Data(name, ty) => {
                V::Output::combine([name.visit(visitor), ty.visit(visitor)])
            }
            ast::FunctionParameter::Lambda(decl) => decl.visit(visitor),
        }
    }
}

impl Ast for ast::Name {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([self.ident.visit(visitor), self.generics.visit(visitor)])
    }
}

impl Ast for ast::Generic {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([self.name.visit(visitor), self.kind.visit(visitor)])
    }
}

impl Ast for ast::Kind {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            ast::KindEnum::Type => V::Output::default(),
            ast::KindEnum::Constant(ty) => ty.visit(visitor),
        }
    }
}

impl Ast for ast::Type {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match &self.0 {
            ast::TypeEnum::Int => V::Output::default(),
            ast::TypeEnum::Path(path) => path.visit(visitor),
            ast::TypeEnum::Struct(struc) => struc.visit(visitor),
        }
    }
}

impl Ast for ast::Expression {
    fn visit<V: Visitor>(&self, _visitor: V) -> V::Output<'_> {
        match &self.0 {
            ast::ExpressionEnum::Block => V::Output::default(),
        }
    }
}

impl Ast for ast::TypeAlias {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([self.name.visit(visitor), self.definition.visit(visitor)])
    }
}

impl Ast for ast::Path {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        visitor.visit_path(self)
    }
}

impl Ast for ast::Struct {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        visitor.visit_struct(self)
    }
}

impl Ast for ast::StructMember {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::StructMember::Data(name, ty) => {
                V::Output::combine([name.visit(visitor), ty.visit(visitor)])
            }
        }
    }
}

impl Ast for ast::String {
    fn visit<V: Visitor>(&self, _visitor: V) -> V::Output<'_> {
        V::Output::default()
    }
}

impl Ast for ast::Ident {
    fn visit<V: Visitor>(&self, _visitor: V) -> V::Output<'_> {
        V::Output::default()
    }
}
