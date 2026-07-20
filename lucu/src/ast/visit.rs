use std::hash::Hash;

use crate::ast;
use crate::span::HasSpan;

pub trait Visitor: Copy {
    type Output<'a>: Default + Combine;
    fn visit_name(self, name: &ast::Name) -> Self::Output<'_> {
        self.visit(name)
    }
    fn visit_path(self, path: &ast::Path) -> Self::Output<'_> {
        self.visit(path)
    }
    fn visit_item(self, def: &ast::Item) -> Self::Output<'_> {
        self.visit(def)
    }
    fn visit_struct(self, struc: &ast::Struct) -> Self::Output<'_> {
        self.visit(struc)
    }
    fn visit_function_declaration(self, function: &ast::FunctionDeclaration) -> Self::Output<'_> {
        self.visit(function)
    }
    fn visit_function_definition(self, function: &ast::FunctionDefinition) -> Self::Output<'_> {
        self.visit(function)
    }
    fn visit_effect_body(self, body: &ast::EffectBody) -> Self::Output<'_> {
        self.visit(body)
    }
    fn visit_type(self, ty: &ast::Type) -> Self::Output<'_> {
        self.visit(ty)
    }
    fn visit_kind(self, kind: &ast::Kind) -> Self::Output<'_> {
        self.visit(kind)
    }
    fn visit(self, ast: &impl Ast) -> Self::Output<'_> {
        ast.visit(self)
    }
}

pub fn visit_option<'a, V: Visitor, A>(
    ast: &'a Option<A>,
    visitor: V,
    f: impl FnOnce(V, &'a A) -> V::Output<'a>,
) -> V::Output<'a> {
    match ast {
        Some(t) => f(visitor, t),
        None => V::Output::default(),
    }
}

pub fn visit_vec<'a, V: Visitor, A>(
    #[expect(clippy::ptr_arg)] ast: &'a Vec<A>,
    visitor: V,
    f: impl Fn(V, &'a A) -> V::Output<'a>,
) -> V::Output<'a> {
    V::Output::combine(ast.iter().map(|elem| f(visitor, elem)))
}

pub trait Combine {
    fn combine(iter: impl IntoIterator<Item = Self>) -> Self;
}

impl Combine for () {
    fn combine(_iter: impl IntoIterator<Item = Self>) -> Self {}
}

impl Combine for usize {
    fn combine(iter: impl IntoIterator<Item = Self>) -> Self {
        iter.into_iter().sum()
    }
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
            visit_vec(&self.imports.elements, visitor, |v, (e, _)| v.visit(e)),
            visit_vec(&self.items.elements, visitor, |v, (e, _)| v.visit_item(e)),
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

impl Ast for ast::ConstantDefinition {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::ConstantDefinition::Constant(constant) => visitor.visit(&**constant),
            ast::ConstantDefinition::Intrinsic(_) => V::Output::default(),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::RegionDefinition {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::RegionDefinition::Alias(path) => visitor.visit_path(path),
            ast::RegionDefinition::Intrinsic(_) => V::Output::default(),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::Item {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::Item::Function(fun, opt) => V::Output::combine([
                visitor.visit_function_declaration(fun),
                match opt {
                    Some((_, def)) => visitor.visit_function_definition(def),
                    None => V::Output::default(),
                },
            ]),
            ast::Item::Type(_, name, opt) => V::Output::combine([
                visitor.visit_name(name),
                visit_option(opt, visitor, |v, (_, def)| v.visit(def)),
            ]),
            ast::Item::Effect(_, name, opt) => V::Output::combine([
                visitor.visit_name(name),
                visit_option(opt, visitor, |v, (_, def)| v.visit(def)),
            ]),
            ast::Item::Region(_, name, opt) => V::Output::combine([
                visitor.visit_name(name),
                visit_option(opt, visitor, |v, (_, def)| v.visit(def)),
            ]),
            ast::Item::Constant(_, name, ty, opt) => V::Output::combine([
                visitor.visit_name(name),
                visitor.visit_type(ty),
                visit_option(opt, visitor, |v, (_, def)| v.visit(def)),
            ]),
            ast::Item::Handle(_, generics, handler) => V::Output::combine([
                visit_option(generics, visitor, |v, g| {
                    visit_vec(&g.inner.elements, v, |v, (t, _)| v.visit(t))
                }),
                visitor.visit(handler),
            ]),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::WithEffects {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        visit_vec(&self.effects, visitor, Visitor::visit_path)
    }
    fn node_name(&self) -> &'static str {
        "WithEffects"
    }
}

impl Ast for ast::Handler {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visitor.visit_path(&self.effect),
            visit_option(&self.with_effects, visitor, Visitor::visit),
            visit_vec(&self.items.inner.elements, visitor, |v, (e, _)| {
                v.visit_item(e)
            }),
        ])
    }
    fn node_name(&self) -> &'static str {
        "Handler"
    }
}

impl Ast for ast::EffectDefinition {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::EffectDefinition::Body(body) => visitor.visit_effect_body(body),
            ast::EffectDefinition::Alias(alias) => visit_vec(alias, visitor, Visitor::visit_path),
            ast::EffectDefinition::Intrinsic(_) => V::Output::default(),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::EffectBody {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        visit_vec(&self.items.inner.elements, visitor, |v, (e, _)| {
            v.visit_item(e)
        })
    }
    fn node_name(&self) -> &'static str {
        "EffectBody"
    }
}

impl Ast for ast::FunctionDefinition {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::FunctionDefinition::Expression(spanned) => visitor.visit(&**spanned),
            ast::FunctionDefinition::Intrinsic(_) => V::Output::default(),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::Parameters {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        visit_vec(&self.inner.elements, visitor, |v, (param, _)| {
            v.visit(param)
        })
    }
    fn node_name(&self) -> &'static str {
        "Parameters"
    }
}

impl Ast for ast::FunctionDeclaration {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visitor.visit_name(&self.name),
            visit_option(&self.parameters, visitor, Visitor::visit),
            visit_option(&self.returns, visitor, Visitor::visit),
            visit_option(&self.effects, visitor, Visitor::visit),
        ])
    }
    fn node_name(&self) -> &'static str {
        "FunctionDeclaration"
    }
}

impl Ast for ast::Returns {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::Returns::Path(path) => visitor.visit_path(path),
            ast::Returns::Type(ty) => visitor.visit_type(ty),
            ast::Returns::Never(_) => V::Output::default(),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::Parameter {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::Parameter::Data(_, ty) => visitor.visit_type(ty),
            ast::Parameter::Lambda(decl) => visitor.visit_function_declaration(decl),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::Name {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        visit_option(&self.generics, visitor, |v, g| {
            visit_vec(&g.inner.elements, v, |v, (t, _)| v.visit(t))
        })
    }
    fn node_name(&self) -> &'static str {
        "Name"
    }
}

impl Ast for ast::GenericParameter {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::GenericParameter::Type(name) => visitor.visit_name(name),
            ast::GenericParameter::Region(_, _) => V::Output::default(),
            ast::GenericParameter::Other(name, kind) => {
                V::Output::combine([visitor.visit_name(name), visitor.visit_kind(kind)])
            }
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::Kind {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::Kind::Type(_) => V::Output::default(),
            ast::Kind::Effect(_) => V::Output::default(),
            ast::Kind::Region(_) => V::Output::default(),
            ast::Kind::Thunk(_) => V::Output::default(),
            ast::Kind::Constant(ty) => visitor.visit_type(ty),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::RegionKind {
    fn visit<V: Visitor>(&self, _visitor: V) -> V::Output<'_> {
        match self {
            ast::RegionKind::Mutable(_) => V::Output::default(),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::PointerRegion {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::PointerRegion::At(_, region) => visitor.visit_path(region),
            ast::PointerRegion::Kind(region_kind) => visitor.visit(region_kind),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::Sentinel {
    fn visit<V: Visitor>(&self, _visitor: V) -> V::Output<'_> {
        V::Output::default()
    }
    fn node_name(&self) -> &'static str {
        "Sentinel"
    }
}

impl Ast for ast::ArrayProperties {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visit_option(&self.size, visitor, |v, c| v.visit(&**c)),
            visit_option(&self.sentinel, visitor, Visitor::visit),
        ])
    }
    fn node_name(&self) -> &'static str {
        "ArrayProperties"
    }
}

impl Ast for ast::Type {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::Type::Maybe(_, ty) => visitor.visit_type(ty),
            ast::Type::Pointer(_, region, ty) => V::Output::combine([
                visit_option(region, visitor, Visitor::visit),
                visitor.visit_type(ty),
            ]),
            ast::Type::Path(path) => visitor.visit_path(path),
            ast::Type::Array(grouped, ty) => {
                V::Output::combine([visitor.visit(&grouped.inner), visitor.visit_type(ty)])
            }
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::LambdaParameter {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        visit_option(&self.ty, visitor, |v, t| v.visit_type(t))
    }
    fn node_name(&self) -> &'static str {
        "LambdaParameter"
    }
}

impl Ast for ast::Index {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::Index::Single(expression) => visitor.visit(&**expression),
            ast::Index::Range {
                from, to, sentinel, ..
            } => V::Output::combine([
                visit_option(from, visitor, |v, e| v.visit(&**e)),
                visit_option(to, visitor, |v, e| v.visit(&**e)),
                visit_option(sentinel, visitor, Visitor::visit),
            ]),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::Call {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        V::Output::combine([
            visitor.visit_path(&self.fun),
            visit_option(&self.args, visitor, |v, g| {
                visit_vec(&g.inner.elements, v, |v, (e, _)| v.visit(&**e))
            }),
            visit_option(&self.block, visitor, |v, e| v.visit(&**e)),
            visit_option(&self.with_effects, visitor, |v, es| v.visit(es)),
        ])
    }
    fn node_name(&self) -> &'static str {
        "Call"
    }
}

impl Ast for ast::Expression {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::Expression::Constant(constant) => visitor.visit(&**constant),
            ast::Expression::Uninit(_) => V::Output::default(),
            ast::Expression::Path(path) => visitor.visit_path(path),
            ast::Expression::Block(g) => V::Output::combine([
                visit_option(&g.inner.params, visitor, |v, (params, _)| {
                    visit_vec(&params.elements, v, |v, (t, _)| v.visit(t))
                }),
                visit_vec(&g.inner.stmts.elements, visitor, |v, (e, _)| v.visit(&**e)),
            ]),
            ast::Expression::Enclosed(grouped) => visitor.visit(&*grouped.inner),
            ast::Expression::Let { ty, value, .. } => V::Output::combine([
                visit_option(ty, visitor, |v, t| v.visit_type(t)),
                visitor.visit(&**value),
            ]),
            ast::Expression::Raise { expr, .. } => {
                visit_option(expr, visitor, |v, e| v.visit(&**e))
            }
            ast::Expression::Handle { expr, .. }
            | ast::Expression::Discard { expr, .. }
            | ast::Expression::UnOp { expr, .. }
            | ast::Expression::Dereference { expr, .. }
            | ast::Expression::Cast { expr, .. } => visitor.visit(&**expr),
            ast::Expression::If {
                condition,
                branch_true,
                branch_false,
                ..
            } => V::Output::combine([
                visitor.visit(&**condition),
                visitor.visit(&*branch_true.1),
                visit_option(branch_false, visitor, |v, (_, e)| v.visit(&**e)),
            ]),
            ast::Expression::AssignOp(_, lhs, _, rhs)
            | ast::Expression::PredicateOp(_, lhs, _, rhs)
            | ast::Expression::MathOp(_, lhs, _, rhs) => {
                V::Output::combine([visitor.visit(&**lhs), visitor.visit(&**rhs)])
            }
            ast::Expression::Index { array, index } => {
                V::Output::combine([visitor.visit(&**array), visitor.visit(&index.inner)])
            }
            ast::Expression::Array(grouped) => {
                visit_vec(&grouped.inner.elements, visitor, |v, (e, _)| v.visit(&**e))
            }
            ast::Expression::Call(call) => visitor.visit(call),
            ast::Expression::Use {
                params,
                call,
                block,
                ..
            } => V::Output::combine([
                visit_option(params, visitor, |v, (_, p, _)| {
                    visit_vec(&p.elements, v, |v, (p, _)| v.visit(p))
                }),
                visitor.visit(call),
                visit_vec(&block.elements, visitor, |v, (e, _)| v.visit(&**e)),
            ]),
            ast::Expression::Member { lhs, .. } => visitor.visit(&**lhs),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::TypeDefinition {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::TypeDefinition::Type(ty) => visitor.visit_type(ty),
            ast::TypeDefinition::Intrinsic(_) => V::Output::default(),
            ast::TypeDefinition::Struct(struc) => visitor.visit_struct(struc),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::Path {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        visit_option(&self.generics, visitor, |v, g| {
            visit_vec(&g.inner.elements, v, |v, (t, _)| v.visit(t))
        })
    }
    fn node_name(&self) -> &'static str {
        "Path"
    }
}

impl Ast for ast::GenericArgument {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::GenericArgument::Path(path, effects) => V::Output::combine([
                visitor.visit_path(path),
                visit_option(effects, visitor, |v, e| v.visit(e)),
            ]),
            ast::GenericArgument::Type(ty, effects) => V::Output::combine([
                visitor.visit_type(ty),
                visit_option(effects, visitor, |v, e| v.visit(e)),
            ]),
            ast::GenericArgument::Constant(constant) => visitor.visit(&**constant),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::Constant {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::Constant::Path(path) => visitor.visit_path(path),
            ast::Constant::Integer(_) => V::Output::default(),
            ast::Constant::String(_) => V::Output::default(),
            ast::Constant::Character(_) => V::Output::default(),
            ast::Constant::Zero(_) => V::Output::default(),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}

impl Ast for ast::Struct {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        visit_vec(&self.members.inner.elements, visitor, |v, (member, _)| {
            v.visit(member)
        })
    }
    fn node_name(&self) -> &'static str {
        "Struct"
    }
}

impl Ast for ast::StructMember {
    fn visit<V: Visitor>(&self, visitor: V) -> V::Output<'_> {
        match self {
            ast::StructMember::Data(_, ty) => visitor.visit_type(ty),
        }
    }
    fn node_name(&self) -> &'static str {
        self.into()
    }
}
