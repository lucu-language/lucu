use std::borrow::Cow;
use std::collections::{HashMap, HashSet};

use crate::parser::AttributeValue;
use crate::Target;
use crate::{
    error::{Error, Errors, Ranged},
    parser::{
        self, BinOp, EffFunIdx, EffIdx, EffectIdent, ExprIdx, Expression, FunIdx, FunSign, Ident,
        PackageIdx, ParamIdx, Parsed, UnOp,
    },
    vecmap::{vecmap_index, VecMap, VecSet},
};

vecmap_index!(Val);
vecmap_index!(TypeIdx);
vecmap_index!(HandlerIdx);

impl TypeIdx {
    fn matches(self, other: TypeIdx) -> bool {
        self == TYPE_UNKNOWN || other == TYPE_UNKNOWN || self == other
    }
    fn is_view(self, ctx: &AsysContext) -> bool {
        match ctx.asys.types[self] {
            Type::Pointer(_) | Type::Slice(_) | Type::Str => true,
            Type::ConstArray(_, ty) | Type::Const(ty) if ty.is_view(ctx) => true,
            _ => false,
        }
    }
    fn is_zero_view(self, ctx: &AsysContext) -> bool {
        match ctx.asys.types[self] {
            Type::Pointer(_) => true,
            Type::ConstArray(_, ty) | Type::Const(ty) if ty.is_zero_view(ctx) => true,
            _ => false,
        }
    }
    fn join(self, other: TypeIdx) -> Option<TypeIdx> {
        if self == other {
            return Some(self);
        }
        if self == TYPE_UNKNOWN || self == TYPE_NEVER {
            return Some(other);
        }
        if other == TYPE_UNKNOWN || other == TYPE_NEVER {
            return Some(self);
        }
        None
    }
    fn to_base(self, ctx: &mut AsysContext) -> TypeIdx {
        match ctx.asys.types[self] {
            Type::Handler(effect, yeet, _) => {
                ctx.asys.insert_type(Type::Handler(effect, yeet, None))
            }
            _ => self,
        }
    }
    fn display(self, ctx: &AsysContext) -> String {
        match ctx.asys.types[self] {
            Type::FunctionLiteral(_) => "function literal".into(),
            Type::None => "none".into(),
            Type::Never => "never".into(),
            Type::Int => "int".into(),
            Type::USize => "usize".into(),
            Type::UPtr => "uptr".into(),
            Type::U8 => "u8".into(),
            Type::Str => "str".into(),
            Type::Bool => "bool".into(),
            _ => format!("'{}'", self.display_inner(ctx)),
        }
    }
    fn display_fails(self, ctx: &AsysContext) -> String {
        match ctx.asys.types[self] {
            Type::None => " fails".into(),
            Type::Never => "".into(),
            _ => format!(" fails {}", self.display_inner(ctx)),
        }
    }
    fn display_inner(self, ctx: &AsysContext) -> String {
        match ctx.asys.types[self] {
            Type::FunctionLiteral(_) => "<unknown>".into(),
            Type::PackageLiteral(_) => "<unknown>".into(),
            Type::Int => "int".into(),
            Type::UInt => "uint".into(),
            Type::USize => "usize".into(),
            Type::UPtr => "uptr".into(),
            Type::U8 => "u8".into(),
            Type::Str => "str".into(),
            Type::Bool => "bool".into(),
            Type::Handler(val, yeets, _) => yeets.display_handler(val, ctx),
            Type::None => "()".into(),
            Type::Never => "!".into(),
            Type::Unknown => "<unknown>".into(),
            Type::Pointer(ty) => format!("^{}", ty.display_inner(ctx)),
            Type::Slice(ty) => format!("[]{}", ty.display_inner(ctx)),
            Type::Const(ty) => format!("const {}", ty.display_inner(ctx)),
            Type::ConstArray(size, ty) => format!("[{}]{}", size, ty.display_inner(ctx)),
        }
    }
    fn display_handler(self, handler: Val, ctx: &AsysContext) -> String {
        let effect_name = match handler.0 {
            usize::MAX => "<unknown>".into(),
            _ => match ctx.asys.defs[handler] {
                Definition::Effect(e) => ctx.parsed.idents[ctx.parsed.effects[e].name].0.clone(),
                _ => "<unknown>".into(),
            },
        };
        format!("{}{}", effect_name, self.display_fails(ctx))
    }
    fn from_val(ctx: &mut AsysContext, val: Val) -> Self {
        match val.0 == usize::MAX {
            true => TYPE_UNKNOWN,
            false => match ctx.asys.defs[val] {
                Definition::Parameter(_, _, t) => t,
                Definition::Variable(_, _, t) => t,
                Definition::EffectFunction(_, _, _, _) => {
                    ctx.asys.insert_type(Type::FunctionLiteral(val))
                }
                Definition::Function(_, _, _) => ctx.asys.insert_type(Type::FunctionLiteral(val)),

                Definition::BuiltinType(_) => TYPE_UNKNOWN,
                Definition::Effect(_) => TYPE_UNKNOWN,
                Definition::Package(pkg) => ctx.asys.insert_type(Type::PackageLiteral(pkg)),
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum Definition {
    Parameter(bool, Ident, TypeIdx),  // parameter index in function
    Variable(bool, ExprIdx, TypeIdx), // variable defined at expr
    Effect(EffIdx),                   // effect index in ast
    EffectFunction(EffIdx, EffFunIdx, Vec<TypeIdx>, TypeIdx), // effect value, function index in effect
    Function(FunIdx, Vec<TypeIdx>, TypeIdx),                  // function index in ast

    BuiltinType(TypeIdx), // builtin type
    Package(PackageIdx),  // package
}

#[derive(Debug)]
pub struct Capture {
    pub val: Val,
    pub mutable: bool,
}

pub fn add_capture(captures: &mut Vec<Capture>, capture: Capture) {
    let idx = captures.iter().position(|c| c.val == capture.val);
    if let Some(idx) = idx {
        captures[idx].mutable |= capture.mutable
    } else {
        captures.push(capture)
    }
}

#[derive(Debug, Default)]
pub enum HandlerDef {
    Handler(ExprIdx, Vec<Capture>),
    Call(ExprIdx),
    Param(ParamIdx),
    Signature,

    #[default]
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    FunctionLiteral(Val),
    PackageLiteral(PackageIdx),
    Handler(Val, TypeIdx, Option<HandlerIdx>),

    Pointer(TypeIdx),
    Const(TypeIdx),
    ConstArray(u64, TypeIdx),
    Slice(TypeIdx),

    Int,
    UInt,
    USize,
    UPtr,
    U8,

    Str,
    Bool,
    None,
    Never,
    Unknown,
}

impl Type {
    pub fn is_int(&self) -> bool {
        matches!(
            self,
            Type::Int | Type::UInt | Type::USize | Type::UPtr | Type::U8
        )
    }
    pub fn is_ptr(&self) -> bool {
        matches!(self, Type::Pointer(_))
    }
}

pub struct Analysis {
    pub capabilities: HashMap<Val, Val>,
    pub values: VecMap<Ident, Val>,
    pub defs: VecMap<Val, Definition>,
    pub handlers: VecMap<HandlerIdx, HandlerDef>,
    pub exprs: VecMap<ExprIdx, TypeIdx>,
    pub types: VecSet<TypeIdx, Type>,
    pub main: Option<FunIdx>,
}

struct AsysContext<'a> {
    asys: Analysis,
    packages: VecMap<PackageIdx, Package>,
    parsed: &'a Parsed,
}

struct Scope<'a> {
    parent: Option<&'a Scope<'a>>,
    values: HashMap<String, Val>,

    funs: &'a HashMap<String, Val>,
    effects: &'a HashMap<String, Val>,
    scoped_effects: &'a HashSet<Val>,
    pkg: PackageIdx,
}

#[derive(Default, Clone)]
struct Package {
    effects: HashMap<String, Val>,
    values: HashMap<String, Val>,
    funs: HashMap<String, Val>,
    implied: HashSet<Val>,
}

impl<'a> Scope<'a> {
    fn get(&self, key: &str) -> Option<Val> {
        match self.values.get(key) {
            Some(&v) => Some(v),
            None => self.parent.map(|p| p.get(key)).flatten(),
        }
    }
    fn child(&self) -> Scope {
        Scope {
            parent: Some(self),
            values: HashMap::new(),
            funs: self.funs,
            effects: self.effects,
            scoped_effects: self.scoped_effects,
            pkg: self.pkg,
        }
    }
}

impl Val {
    fn definition_range(self, ctx: &AsysContext) -> Option<Ranged<()>> {
        match ctx.asys.defs[self] {
            Definition::Parameter(_, name, _) => Some(ctx.parsed.idents[name].empty()),
            Definition::Effect(e) => Some(ctx.parsed.idents[ctx.parsed.effects[e].name].empty()),
            Definition::EffectFunction(e, f, _, _) => {
                Some(ctx.parsed.idents[ctx.parsed.effects[e].functions[f].name].empty())
            }
            Definition::Function(f, _, _) => {
                Some(ctx.parsed.idents[ctx.parsed.functions[f].decl.name].empty())
            }
            Definition::Variable(_, e, _) => match ctx.parsed.exprs[e].0 {
                Expression::Let(_, name, _, _) => Some(ctx.parsed.idents[name].empty()),
                _ => None,
            },
            Definition::BuiltinType(_) => None,
            Definition::Package(_) => None,
        }
    }
}

impl Analysis {
    fn push_val(&mut self, id: Ident, def: Definition) -> Val {
        let val = self.defs.push(Val, def);
        self.values[id] = val;
        val
    }
    fn insert_type(&mut self, ty: Type) -> TypeIdx {
        self.types.insert(TypeIdx, ty).clone()
    }
}

fn analyze_assignable(
    ctx: &mut AsysContext,
    scope: &mut Scope,
    expr: ExprIdx,
    parent: ExprIdx,
    errors: &mut Errors,
) -> (TypeIdx, bool) {
    let (found_ty, mutable) = match ctx.parsed.exprs[expr].0 {
        Expression::Ident(id) => {
            let ty = analyze_expr(ctx, scope, expr, TYPE_UNKNOWN, false, errors);
            let val = ctx.asys.values[id];
            if val.0 != usize::MAX {
                match ctx.asys.defs[val] {
                    Definition::Parameter(true, _, _) => ty,
                    Definition::Variable(true, _, _) => ty,
                    _ => {
                        errors.push(
                            ctx.parsed.exprs[parent]
                                .with(Error::AssignImmutable(val.definition_range(ctx))),
                        );
                        (TYPE_UNKNOWN, false)
                    }
                }
            } else {
                (TYPE_UNKNOWN, false)
            }
        }
        Expression::BinOp(left, BinOp::Index, right) => {
            let array = analyze_assignable(ctx, scope, left, expr, errors);
            analyze_expr(ctx, scope, right, TYPE_USIZE, false, errors);

            let elem = match ctx.asys.types[array.0] {
                Type::ConstArray(_, ty) => ty,
                Type::Slice(ty) => ty,
                Type::Unknown => TYPE_UNKNOWN,
                _ => {
                    errors.push(
                        ctx.parsed.exprs[left].with(Error::ExpectedArray(array.0.display(ctx))),
                    );
                    TYPE_UNKNOWN
                }
            };

            (elem, array.1)
        }
        Expression::Error => (TYPE_UNKNOWN, false),
        _ => {
            analyze_expr(ctx, scope, expr, TYPE_UNKNOWN, false, errors);
            errors.push(ctx.parsed.exprs[parent].with(Error::AssignExpression));
            (TYPE_UNKNOWN, false)
        }
    };

    match ctx.asys.types[found_ty] {
        Type::Const(inner) => (inner, false),
        _ => (found_ty, mutable),
    }
}

fn capture_ident(
    ctx: &mut AsysContext,
    scope: &mut Scope,
    id: Ident,
    effect: Option<Val>,
    captures: &mut Vec<Capture>,
) {
    let val = ctx.asys.values[id];
    if val.0 != usize::MAX {
        match ctx.asys.defs[val] {
            Definition::EffectFunction(e, _, _, _) => {
                let e = ctx.asys.values[ctx.parsed.effects[e].name];
                if Some(e) != effect && scope.scoped_effects.contains(&e) {
                    add_capture(
                        captures,
                        Capture {
                            val: e,
                            mutable: false,
                        },
                    );
                }
            }
            Definition::Function(fun, _, _) => {
                let effects = ctx.parsed.functions[fun]
                    .decl
                    .sign
                    .effects
                    .iter()
                    .copied()
                    .map(|i| ctx.asys.values[i.effect]);
                for e in effects {
                    if Some(e) != effect && scope.scoped_effects.contains(&e) {
                        add_capture(
                            captures,
                            Capture {
                                val: e,
                                mutable: false,
                            },
                        );
                    }
                }
            }
            Definition::Parameter(mutable, _, _) => {
                if scope.get(&ctx.parsed.idents[id].0) == Some(val) {
                    add_capture(captures, Capture { val, mutable });
                }
            }
            Definition::Variable(mutable, _, _) => {
                if scope.get(&ctx.parsed.idents[id].0) == Some(val) {
                    add_capture(captures, Capture { val, mutable });
                }
            }
            Definition::Effect(_) => {
                if scope.get(&ctx.parsed.idents[id].0) == Some(val) {
                    add_capture(
                        captures,
                        Capture {
                            val,
                            mutable: false,
                        },
                    );
                }
            }
            Definition::BuiltinType(_) => {}
            Definition::Package(_) => {}
        }
    }
}

fn analyze_expr(
    ctx: &mut AsysContext,
    scope: &mut Scope,
    expr: ExprIdx,
    expected_ty: TypeIdx,
    resolve_fun: bool,
    errors: &mut Errors,
) -> (TypeIdx, bool) {
    let (found_ty, mutable) = match ctx.parsed.exprs[expr].0 {
        // analyze
        Expression::Handler(ref handler) => {
            // resolve effect
            let (effect, ident, yeet_type) = match *handler {
                parser::Handler::Full {
                    effect, fail_type, ..
                } => {
                    let yeet_type = match fail_type {
                        parser::FailType::Never => TYPE_NEVER,
                        parser::FailType::None => TYPE_NONE,
                        parser::FailType::Some(t) => {
                            let yeet_type = analyze_type(ctx, scope, t, errors);

                            if matches!(ctx.asys.types[yeet_type], Type::Handler(_, _, _)) {
                                errors.push(ctx.parsed.types[t].with(Error::NestedHandlers));
                            }

                            yeet_type
                        }
                    };
                    (
                        analyze_effect(ctx, effect, scope, errors),
                        Some(effect),
                        yeet_type,
                    )
                }
                parser::Handler::Lambda(_) => match ctx.asys.types[expected_ty] {
                    Type::Handler(effect, yeet_type, _) => {
                        // TODO: check if matches (one fun, param count)
                        (Some(effect), None, yeet_type)
                    }
                    _ => {
                        errors.push(ctx.parsed.exprs[expr].with(Error::NotEnoughInfo));
                        (None, None, TYPE_UNKNOWN)
                    }
                },
            };

            let mut captures = Vec::new();
            if let Some(effect) = effect {
                let ast_effect = match ctx.asys.defs[effect] {
                    Definition::Effect(idx) => &ctx.parsed.effects[idx],
                    _ => unreachable!(),
                };

                for (decl, body) in handler.functions(ast_effect) {
                    // match fun name to effect
                    let name = &ctx.parsed.idents[decl.name].0;
                    let effectfun = ast_effect
                        .functions
                        .values()
                        .find(|decl| ctx.parsed.idents[decl.name].0.eq(name))
                        .map(|decl| ctx.asys.values[decl.name]);
                    let Some(effectfun) = effectfun else {
                        errors.push(ctx.parsed.idents[decl.name].with(Error::UnknownEffectFun(
                            effect.definition_range(ctx),
                            ident.map(|ident| ctx.parsed.idents[ident.effect].empty()),
                        )));
                        break;
                    };
                    ctx.asys.values[decl.name] = effectfun;

                    // analyze signature
                    let (params, out) = match ctx.asys.defs[effectfun] {
                        Definition::EffectFunction(eff, fun, _, out) => {
                            let params = &ctx.parsed.effects[eff].functions[fun].sign.inputs;
                            (params, out)
                        }
                        _ => unreachable!(),
                    };

                    match decl {
                        Cow::Borrowed(_) => {
                            // TODO: check if this matches effectfun
                            analyze_return(ctx, scope, decl.sign.output, errors);
                            analyze_sign(ctx, &scope, &decl.sign, errors);
                        }
                        Cow::Owned(_) => {
                            // set param types
                            for (i, param) in decl.sign.inputs.iter(ParamIdx) {
                                let ty = match ctx.asys.defs[ctx.asys.values[params[i].name]] {
                                    Definition::Parameter(_, _, ty) => ty,
                                    _ => unreachable!(),
                                };
                                ctx.asys.push_val(
                                    param.name,
                                    Definition::Parameter(param.mutable, param.name, ty),
                                );
                            }
                        }
                    };

                    // analyze body
                    let mut child = scope.child();
                    scope_sign(ctx, &mut child, &decl.sign);

                    let mut scoped = scope.scoped_effects.clone();
                    scoped.extend(decl.sign.effects.iter().copied().filter_map(|i| {
                        let val = ctx.asys.values[i.effect];
                        if val.0 == usize::MAX {
                            None
                        } else {
                            Some(val)
                        }
                    }));
                    child.scoped_effects = &scoped;

                    analyze_expr(ctx, &mut child, body, out, false, errors).0;

                    // add captures
                    ctx.parsed.for_each(
                        body,
                        true,
                        true,
                        &mut |expr| match ctx.parsed.exprs[expr].0 {
                            Expression::Ident(id) | Expression::Member(_, id) => {
                                capture_ident(ctx, scope, id, Some(effect), &mut captures);
                            }
                            _ => {}
                        },
                    );
                }
            }

            // get handler type
            let handler_type = match effect {
                Some(val) => {
                    let handler = ctx
                        .asys
                        .handlers
                        .push(HandlerIdx, HandlerDef::Handler(expr, captures));
                    ctx.asys
                        .insert_type(Type::Handler(val, yeet_type, Some(handler)))
                }
                None => TYPE_UNKNOWN,
            };

            (handler_type, false)
        }
        Expression::Ident(ident) => {
            let name = &ctx.parsed.idents[ident].0;
            if resolve_fun {
                match scope.funs.get(name).copied() {
                    Some(val) => {
                        ctx.asys.values[ident] = val;
                        let ty = TypeIdx::from_val(ctx, val);
                        (ty, false)
                    }
                    None => {
                        errors.push(ctx.parsed.idents[ident].with(Error::UnknownFunction));
                        (TYPE_UNKNOWN, false)
                    }
                }
            } else {
                match scope.get(name) {
                    Some(val) => {
                        ctx.asys.values[ident] = val;
                        let ty = TypeIdx::from_val(ctx, val);
                        let mutable = match ctx.asys.defs[val] {
                            Definition::Parameter(true, _, _) => true,
                            Definition::Variable(true, _, _) => true,
                            _ => false,
                        };
                        (ty, mutable)
                    }
                    None => match scope.effects.get(name).copied() {
                        Some(val) => {
                            // TODO: check if in scope
                            ctx.asys.values[ident] = val;
                            let handler = ctx.asys.handlers.push(HandlerIdx, HandlerDef::Signature);
                            (
                                ctx.asys
                                    .insert_type(Type::Handler(val, TYPE_NEVER, Some(handler))),
                                false,
                            )
                        }
                        None => {
                            errors.push(ctx.parsed.idents[ident].with(Error::UnknownValue));
                            (TYPE_UNKNOWN, false)
                        }
                    },
                }
            }
        }

        // traverse downwards
        Expression::Body(ref b) => {
            let mut child = scope.child();

            for &expr in b.main.iter() {
                analyze_expr(ctx, &mut child, expr, TYPE_UNKNOWN, false, errors);
            }
            match b.last {
                Some(expr) => analyze_expr(ctx, &mut child, expr, expected_ty, false, errors),
                None => (TYPE_NONE, false),
            }
        }
        Expression::Loop(expr) => {
            analyze_expr(ctx, scope, expr, TYPE_UNKNOWN, false, errors);
            (TYPE_NEVER, false)
        }
        Expression::Call(cexpr, ref exprs) => {
            // get function
            let fun = analyze_expr(ctx, scope, cexpr, TYPE_UNKNOWN, true, errors).0;
            let fun = match ctx.asys.types[fun] {
                Type::FunctionLiteral(fun) => Some(fun),
                Type::Unknown => None,
                _ => {
                    errors.push(
                        ctx.parsed.exprs[cexpr].with(Error::ExpectedFunction(fun.display(ctx))),
                    );
                    None
                }
            };

            // get function signature
            // TODO: error on effect mismatch
            let (params, return_type) = match fun {
                Some(fun) => match ctx.asys.defs[fun] {
                    Definition::Function(fun_idx, _, return_type) => {
                        ctx.asys.exprs[cexpr] = ctx.asys.insert_type(Type::FunctionLiteral(fun));
                        (
                            Some(
                                ctx.parsed.functions[fun_idx]
                                    .decl
                                    .sign
                                    .inputs
                                    .values()
                                    .map(|param| {
                                        (
                                            TypeIdx::from_val(ctx, ctx.asys.values[param.name])
                                                .to_base(ctx),
                                            param.mutable,
                                            ctx.parsed.idents[param.name].empty(),
                                        )
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                            return_type,
                        )
                    }
                    Definition::EffectFunction(eff_idx, fun_idx, _, return_type) => {
                        ctx.asys.exprs[cexpr] = ctx.asys.insert_type(Type::FunctionLiteral(fun));
                        (
                            Some(
                                ctx.parsed.effects[eff_idx].functions[fun_idx]
                                    .sign
                                    .inputs
                                    .values()
                                    .map(|param| {
                                        (
                                            TypeIdx::from_val(ctx, ctx.asys.values[param.name])
                                                .to_base(ctx),
                                            param.mutable,
                                            ctx.parsed.idents[param.name].empty(),
                                        )
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                            return_type,
                        )
                    }
                    _ => {
                        errors.push(ctx.parsed.exprs[cexpr].with(Error::ExpectedFunction(
                            TypeIdx::from_val(ctx, fun).display(ctx),
                        )));
                        (None, TYPE_UNKNOWN)
                    }
                },
                None => (None, TYPE_UNKNOWN),
            };
            // handle return type as handler
            // this way different calls always return different handlers according to the type checker
            // leading to a type mismatch
            let return_type = match ctx.asys.types[return_type] {
                Type::Handler(val, yeet, _) => {
                    let handler = ctx.asys.handlers.push(HandlerIdx, HandlerDef::Call(expr));
                    ctx.asys
                        .insert_type(Type::Handler(val, yeet, Some(handler)))
                }
                _ => return_type,
            };
            // analyze arguments
            if let Some(params) = params {
                if params.len() != exprs.len() {
                    errors.push(
                        ctx.parsed.exprs[expr]
                            .with(Error::ParameterMismatch(params.len(), exprs.len())),
                    );
                }
                for (expr, (expected, mutable, range)) in
                    exprs.iter().copied().zip(params.into_iter())
                {
                    let param = analyze_expr(ctx, scope, expr, expected, false, errors);
                    if mutable && !param.1 && param.0.is_view(ctx) {
                        errors.push(
                            ctx.parsed.exprs[expr]
                                .with(Error::MoveImmutableView(None, Some(range))),
                        )
                    }
                }
            }
            (return_type, !return_type.is_view(ctx))
        }
        Expression::TryWith(expr, handler) => {
            let expected_return = expected_ty;

            let mut child = scope.child();
            let ty = if let Some(handler) = handler {
                let handler_type =
                    analyze_expr(ctx, &mut child, handler, TYPE_UNKNOWN, false, errors).0;

                let handler_type = match ctx.asys.types[handler_type] {
                    Type::Handler(handler, break_type, _) => Some((handler, break_type)),
                    Type::Unknown => None,
                    _ => {
                        errors.push(
                            ctx.parsed.exprs[handler]
                                .with(Error::ExpectedHandler(handler_type.display(ctx))),
                        );
                        None
                    }
                };

                if let Some((eff_val, handler_break)) = handler_type {
                    let effect = match ctx.asys.defs[eff_val] {
                        Definition::Effect(idx) => ctx.parsed.effects[idx].name,
                        _ => panic!(),
                    };

                    let expected_break = match ctx.asys.types[handler_break] {
                        Type::Never => expected_return,
                        _ => handler_break,
                    };

                    let mut scoped = child.scoped_effects.clone();
                    scoped.insert(ctx.asys.values[effect]);

                    child.scoped_effects = &scoped;
                    if !TypeIdx::matches(expected_break, expected_return) {
                        errors.push(ctx.parsed.exprs[handler].with(Error::TypeMismatch(
                            format!("'{}'", expected_return.display_handler(eff_val, ctx)),
                            format!("'{}'", expected_break.display_handler(eff_val, ctx)),
                        )));

                        analyze_expr(ctx, &mut child, expr, expected_return, false, errors)
                    } else {
                        analyze_expr(ctx, &mut child, expr, expected_break, false, errors)
                    }
                } else {
                    (TYPE_UNKNOWN, false)
                }
            } else {
                analyze_expr(ctx, &mut child, expr, expected_return, false, errors)
            };

            if matches!(ctx.asys.types[ty.0], Type::Handler(_, _, _)) {
                let expr = match &ctx.parsed.exprs[expr].0 {
                    Expression::Body(body) => body.last.unwrap(),
                    _ => expr,
                };

                errors.push(ctx.parsed.exprs[expr].with(Error::TryReturnsHandler));
            }

            ty
        }
        Expression::Member(expr, field) => {
            let handler = if let Expression::Ident(ident) = ctx.parsed.exprs[expr].0 {
                // getting a member directly with an identifier
                // when a value is not found in scope we also check within effects
                let name = &ctx.parsed.idents[ident].0;
                match scope.get(name).and_then(|_val| {
                    // TODO: currently no values can have children
                    // when structures exist, add them here
                    None
                }) {
                    Some(ty) => Some(ty),
                    None => match ctx.parsed.packages[scope.pkg].imports.get(name) {
                        Some(&pkg) => {
                            let ty = ctx.asys.insert_type(Type::PackageLiteral(pkg));
                            ctx.asys.push_val(ident, Definition::Package(pkg));
                            ctx.asys.exprs[expr] = ty;
                            Some(ty)
                        }
                        None => {
                            errors
                                .push(ctx.parsed.idents[ident].with(Error::UnknownValueOrPackage));
                            None
                        }
                    },
                }
            } else {
                // TODO: allow parent expr to be effect of package
                Some(analyze_expr(ctx, scope, expr, TYPE_UNKNOWN, false, errors).0)
            };

            if let Some(handler) = handler {
                match ctx.asys.types[handler] {
                    Type::PackageLiteral(pkg) => {
                        let name = &ctx.parsed.idents[field].0;
                        if resolve_fun {
                            match ctx.packages[pkg].funs.get(name).copied() {
                                Some(val) => {
                                    ctx.asys.values[field] = val;
                                    let ty = TypeIdx::from_val(ctx, val);
                                    (ty, false)
                                }
                                None => {
                                    errors.push(ctx.parsed.idents[field].with(
                                        Error::UnknownPackageFunction(
                                            ctx.parsed.exprs[expr].empty(),
                                        ),
                                    ));
                                    (TYPE_UNKNOWN, false)
                                }
                            }
                        } else {
                            match ctx.packages[pkg].values.get(name) {
                                Some(&val) => {
                                    ctx.asys.values[field] = val;
                                    (TypeIdx::from_val(ctx, val), false)
                                }
                                None => match ctx.packages[pkg].effects.get(name).copied() {
                                    Some(val) => {
                                        // TODO: check if in scope
                                        ctx.asys.values[field] = val;
                                        let handler = ctx
                                            .asys
                                            .handlers
                                            .push(HandlerIdx, HandlerDef::Signature);
                                        (
                                            ctx.asys.insert_type(Type::Handler(
                                                val,
                                                TYPE_NEVER,
                                                Some(handler),
                                            )),
                                            false,
                                        )
                                    }
                                    None => {
                                        errors.push(ctx.parsed.idents[field].with(
                                            Error::UnknownPackageValue(
                                                ctx.parsed.exprs[expr].empty(),
                                            ),
                                        ));
                                        (TYPE_UNKNOWN, false)
                                    }
                                },
                            }
                        }
                    }
                    Type::Handler(effect, _, _) => {
                        let name = &ctx.parsed.idents[field].0;
                        let fun = match ctx.asys.defs[effect] {
                            Definition::Effect(idx) => ctx.parsed.effects[idx]
                                .functions
                                .values()
                                .find(|decl| ctx.parsed.idents[decl.name].0.eq(name))
                                .map(|decl| ctx.asys.values[decl.name]),
                            _ => None,
                        };
                        match fun {
                            Some(fun) => {
                                ctx.asys.values[field] = fun;
                                (ctx.asys.insert_type(Type::FunctionLiteral(fun)), false)
                            }
                            None => {
                                errors.push(ctx.parsed.idents[field].with(
                                    Error::UnknownEffectFun(
                                        effect.definition_range(ctx),
                                        Some(ctx.parsed.exprs[expr].empty()),
                                    ),
                                ));
                                (TYPE_UNKNOWN, false)
                            }
                        }
                    }
                    Type::Unknown => (TYPE_UNKNOWN, false),
                    _ => {
                        // TODO: type definition
                        errors.push(ctx.parsed.idents[field].with(Error::UnknownField(
                            None,
                            Some(ctx.parsed.exprs[expr].empty()),
                        )));
                        (TYPE_UNKNOWN, false)
                    }
                }
            } else {
                (TYPE_UNKNOWN, false)
            }
        }
        Expression::IfElse(cond, no, yes) => {
            analyze_expr(ctx, scope, cond, TYPE_BOOL, false, errors);
            let yes_type = analyze_expr(ctx, scope, no, expected_ty, false, errors);
            let no_type = match yes {
                Some(expr) => analyze_expr(ctx, scope, expr, expected_ty, false, errors),
                None => (TYPE_NONE, false),
            };
            (
                TypeIdx::join(yes_type.0, no_type.0).unwrap_or(TYPE_NONE),
                yes_type.1 && no_type.1,
            )
        }
        Expression::BinOp(left, op, right) => match op {
            BinOp::Assign => {
                let left_type = analyze_assignable(ctx, scope, left, expr, errors);
                let right_type = analyze_expr(ctx, scope, right, left_type.0, false, errors);
                if left_type.1 && !right_type.1 && right_type.0.is_view(ctx) {
                    errors.push(ctx.parsed.exprs[right].with(Error::AssignImmutableView(None)));
                }
                (TYPE_NONE, false)
            }
            BinOp::Index => {
                let array = analyze_expr(ctx, scope, left, TYPE_UNKNOWN, false, errors);

                let elem = match ctx.parsed.exprs[right].0 {
                    Expression::BinOp(rleft, BinOp::Range, right) => {
                        analyze_expr(ctx, scope, rleft, TYPE_USIZE, false, errors);
                        analyze_expr(ctx, scope, right, TYPE_USIZE, false, errors);

                        match ctx.asys.types[array.0] {
                            Type::ConstArray(_, ty) => ctx.asys.insert_type(Type::Slice(ty)),
                            Type::Slice(ty) => ctx.asys.insert_type(Type::Slice(ty)),
                            Type::Unknown => TYPE_UNKNOWN,
                            _ => {
                                errors.push(
                                    ctx.parsed.exprs[left]
                                        .with(Error::ExpectedArray(array.0.display(ctx))),
                                );
                                TYPE_UNKNOWN
                            }
                        }
                    }
                    _ => {
                        analyze_expr(ctx, scope, right, TYPE_USIZE, false, errors);

                        match ctx.asys.types[array.0] {
                            Type::ConstArray(_, ty) => ty,
                            Type::Slice(ty) => ty,
                            Type::Unknown => TYPE_UNKNOWN,
                            _ => {
                                errors.push(
                                    ctx.parsed.exprs[left]
                                        .with(Error::ExpectedArray(array.0.display(ctx))),
                                );
                                TYPE_UNKNOWN
                            }
                        }
                    }
                };

                (elem, array.1)
            }
            _ => {
                let ret_ty = match op {
                    BinOp::Equals | BinOp::Less | BinOp::Greater => Some(TYPE_BOOL),
                    BinOp::Divide | BinOp::Multiply | BinOp::Subtract | BinOp::Add => None,
                    BinOp::Range => {
                        errors.push(ctx.parsed.exprs[expr].with(Error::NakedRange));
                        Some(TYPE_UNKNOWN)
                    }
                    BinOp::Assign | BinOp::Index => unreachable!(),
                };
                match ret_ty {
                    Some(ret_ty) => {
                        let op_ty = analyze_expr(ctx, scope, left, TYPE_UNKNOWN, false, errors).0;
                        analyze_expr(ctx, scope, right, op_ty, false, errors);
                        (ret_ty, false)
                    }
                    None => {
                        let op_ty = analyze_expr(ctx, scope, left, expected_ty, false, errors).0;
                        analyze_expr(ctx, scope, right, op_ty, false, errors);
                        (op_ty, false)
                    }
                }
            }
        },
        Expression::UnOp(uexpr, op) => match op {
            UnOp::PostIncrement => analyze_assignable(ctx, scope, uexpr, expr, errors),
            UnOp::Reference => {
                let ty = analyze_expr(ctx, scope, uexpr, TYPE_UNKNOWN, false, errors);
                if ty.0 == TYPE_UNKNOWN {
                    (TYPE_UNKNOWN, false)
                } else {
                    let ptr = match ctx.asys.types[expected_ty] {
                        Type::Pointer(_) => ctx.asys.insert_type(Type::Pointer(ty.0)),
                        _ => ctx.asys.insert_type(Type::Pointer(ty.0)),
                    };
                    (ptr, ty.1)
                }
            }
            UnOp::Cast => {
                let ty = analyze_expr(ctx, scope, uexpr, TYPE_UNKNOWN, false, errors);
                match (&ctx.asys.types[ty.0], &ctx.asys.types[expected_ty]) {
                    (t1, Type::UPtr) if t1.is_ptr() => (expected_ty, false),
                    (Type::UPtr, t2) if t2.is_ptr() => (expected_ty, true),
                    (t1, t2) if t1.is_int() && t2.is_int() => (expected_ty, false),
                    (Type::Str, Type::Slice(TYPE_U8)) => (expected_ty, false),
                    (_t1, _t2) => ty,
                }
            }
        },
        Expression::Yeet(val) => {
            // TODO: yeet type analysis
            if let Some(expr) = val {
                analyze_expr(ctx, scope, expr, TYPE_UNKNOWN, false, errors);
            }
            (TYPE_NEVER, false)
        }
        Expression::Let(mutable, name, ty, rexpr) => {
            let val_type = match ty {
                Some(ty) => analyze_type(ctx, scope, ty, errors),
                None => TYPE_UNKNOWN,
            };
            let val_type = analyze_expr(ctx, scope, rexpr, val_type, false, errors);
            if mutable && !val_type.1 && val_type.0.is_view(ctx) {
                errors.push(ctx.parsed.exprs[rexpr].with(Error::AssignImmutableView(None)));
            }

            let val = ctx
                .asys
                .push_val(name, Definition::Variable(mutable, expr, val_type.0));
            scope.values.insert(ctx.parsed.idents[name].0.clone(), val);
            (TYPE_NONE, false)
        }

        // these have no identifiers
        Expression::String(_) => (
            match ctx.asys.types[expected_ty] {
                Type::Str => TYPE_STR,
                Type::Slice(TYPE_U8) => expected_ty,

                // default type for literal
                _ => TYPE_STR,
            },
            false,
        ),
        Expression::Character(_) => (
            match ctx.asys.types[expected_ty] {
                // TODO: check if fits
                Type::U8 => TYPE_U8,

                // default type for literal
                // TODO: character type
                _ => TYPE_U8,
            },
            false,
        ),
        Expression::Int(n) => {
            if n == 0 && expected_ty != TYPE_UNKNOWN {
                // zero init
                if expected_ty.is_zero_view(ctx) {
                    errors.push(
                        ctx.parsed.exprs[expr].with(Error::ZeroinitView(expected_ty.display(ctx))),
                    );
                    (TYPE_UNKNOWN, false)
                } else if expected_ty == TYPE_NEVER {
                    errors.push(ctx.parsed.exprs[expr].with(Error::NeverValue));
                    (TYPE_UNKNOWN, false)
                } else {
                    (expected_ty, true)
                }
            } else {
                (
                    match ctx.asys.types[expected_ty] {
                        // TODO: check if fits
                        Type::Int => TYPE_INT,
                        Type::USize => TYPE_USIZE,
                        Type::UPtr => TYPE_UPTR,
                        Type::U8 => TYPE_U8,

                        // default type for literal
                        _ => TYPE_INT,
                    },
                    false,
                )
            }
        }
        Expression::Array(ref elems) => {
            match ctx.asys.types[expected_ty] {
                Type::ConstArray(_, elem_ty) => {
                    // TODO: error on wrong size

                    let mut mutable = true;
                    for expr in elems.iter().copied() {
                        mutable &= analyze_expr(ctx, scope, expr, elem_ty, false, errors).1;
                    }
                    (expected_ty, mutable || !elem_ty.is_view(ctx))
                }
                Type::Slice(elem_ty) => {
                    let mut mutable = true;
                    for expr in elems.iter().copied() {
                        mutable &= analyze_expr(ctx, scope, expr, elem_ty, false, errors).1;
                    }
                    (expected_ty, mutable || !elem_ty.is_view(ctx))
                }
                _ => {
                    let mut iter = elems.iter().copied();
                    match iter.next() {
                        Some(first) => {
                            let (elem_ty, mut mutable) =
                                analyze_expr(ctx, scope, first, TYPE_UNKNOWN, false, errors);
                            for expr in iter {
                                mutable &= analyze_expr(ctx, scope, expr, elem_ty, false, errors).1;
                            }
                            if elem_ty == TYPE_UNKNOWN {
                                (TYPE_UNKNOWN, false)
                            } else {
                                let arr_ty = ctx
                                    .asys
                                    .insert_type(Type::ConstArray(elems.len() as u64, elem_ty));
                                (arr_ty, mutable || !elem_ty.is_view(ctx))
                            }
                        }
                        None => {
                            errors.push(ctx.parsed.exprs[expr].with(Error::NotEnoughInfo));
                            (TYPE_UNKNOWN, false)
                        }
                    }
                }
            }
        }
        Expression::Uninit => {
            if expected_ty.is_view(ctx) {
                errors.push(
                    ctx.parsed.exprs[expr].with(Error::UndefinedView(expected_ty.display(ctx))),
                );
                (TYPE_UNKNOWN, false)
            } else if expected_ty == TYPE_NEVER {
                errors.push(ctx.parsed.exprs[expr].with(Error::NeverValue));
                (TYPE_UNKNOWN, false)
            } else if expected_ty == TYPE_UNKNOWN {
                errors.push(ctx.parsed.exprs[expr].with(Error::NotEnoughInfo));
                (TYPE_UNKNOWN, false)
            } else {
                (expected_ty, true)
            }
        }
        Expression::Error => (TYPE_UNKNOWN, false),
    };

    let (found_ty, mutable) = match ctx.asys.types[found_ty] {
        Type::Const(inner) => (inner, false),
        _ => (found_ty, mutable),
    };

    let typ = match (expected_ty, found_ty.to_base(ctx)) {
        (a, b) if TypeIdx::matches(a, b) => found_ty,
        (_, TYPE_NEVER) => expected_ty,

        (_, _) => {
            errors.push(ctx.parsed.exprs[expr].with(Error::TypeMismatch(
                expected_ty.display(ctx),
                found_ty.display(ctx),
            )));
            expected_ty
        }
    };

    ctx.asys.exprs[expr] = typ;
    (typ, mutable)
}

fn analyze_effect(
    ctx: &mut AsysContext,
    ident: EffectIdent,
    scope: &Scope,
    errors: &mut Errors,
) -> Option<Val> {
    let effects = match ident.package {
        Some(package) => {
            let name = &ctx.parsed.idents[package].0;
            match ctx.parsed.packages[scope.pkg].imports.get(name) {
                Some(&pkg) => {
                    ctx.asys.push_val(package, Definition::Package(pkg));
                    &ctx.packages[pkg].effects
                }
                None => {
                    errors.push(ctx.parsed.idents[package].with(Error::UnknownPackage));
                    return None;
                }
            }
        }
        None => &scope.effects,
    };

    let name = &ctx.parsed.idents[ident.effect].0;
    match effects.get(name) {
        Some(&val) => {
            ctx.asys.values[ident.effect] = val;
            Some(val)
        }
        None => {
            match ident.package {
                Some(package) => errors.push(ctx.parsed.idents[ident.effect].with(
                    Error::UnknownPackageEffect(ctx.parsed.idents[package].empty()),
                )),

                None => errors.push(ctx.parsed.idents[ident.effect].with(Error::UnknownEffect)),
            }
            None
        }
    }
}

fn analyze_return(
    ctx: &mut AsysContext,
    scope: &Scope,
    ty: Option<parser::TypeIdx>,
    errors: &mut Errors,
) -> TypeIdx {
    match ty {
        Some(ty) => analyze_type(ctx, scope, ty, errors),
        None => TYPE_NONE,
    }
}

fn analyze_type(
    ctx: &mut AsysContext,
    scope: &Scope,
    ty: parser::TypeIdx,
    errors: &mut Errors,
) -> TypeIdx {
    use parser::Type as T;
    let (id, fail) = match ctx.parsed.types[ty].0 {
        T::Never => return TYPE_NEVER,
        T::Error => return TYPE_UNKNOWN,
        T::Path(id) => (id, parser::FailType::Never),
        T::Handler(id, fail) => (id, fail),
        T::Pointer(ty) => {
            let inner = analyze_type(ctx, scope, ty, errors);
            return ctx.asys.insert_type(Type::Pointer(inner));
        }
        T::ConstArray(size, ty) => {
            let inner = analyze_type(ctx, scope, ty, errors);
            return ctx.asys.insert_type(Type::ConstArray(size, inner));
        }
        T::Slice(ty) => {
            let inner = analyze_type(ctx, scope, ty, errors);
            return ctx.asys.insert_type(Type::Slice(inner));
        }
        T::Const(ty) => {
            let inner = analyze_type(ctx, scope, ty, errors);
            return ctx.asys.insert_type(Type::Const(inner));
        }
    };

    let name = &ctx.parsed.idents[id].0;

    // check scope
    match scope.get(name) {
        Some(val) => {
            ctx.asys.values[id] = val;
            match ctx.asys.defs[val] {
                Definition::BuiltinType(ty) => {
                    if matches!(fail, parser::FailType::Never) {
                        ty
                    } else {
                        errors.push(ctx.parsed.idents[id].with(Error::ExpectedEffect(
                            ty.display(ctx),
                            val.definition_range(ctx),
                        )));
                        TYPE_UNKNOWN
                    }
                }
                _ => {
                    errors.push(
                        ctx.parsed.idents[id].with(Error::ExpectedType(val.definition_range(ctx))),
                    );
                    TYPE_UNKNOWN
                }
            }
        }

        // check effects
        None => match scope.effects.get(name) {
            Some(&val) => {
                ctx.asys.values[id] = val;
                let fail = match fail {
                    parser::FailType::Never => TYPE_NEVER,
                    parser::FailType::None => TYPE_NONE,
                    parser::FailType::Some(ty) => analyze_type(ctx, scope, ty, errors),
                };
                if matches!(ctx.asys.types[fail], Type::Handler(_, _, _)) {
                    errors.push(ctx.parsed.types[ty].with(Error::NestedHandlers))
                }
                ctx.asys.insert_type(Type::Handler(val, fail, None))
            }
            None => {
                if matches!(fail, parser::FailType::Never) {
                    errors.push(ctx.parsed.idents[id].with(Error::UnknownType))
                } else {
                    errors.push(ctx.parsed.idents[id].with(Error::UnknownEffect))
                }
                TYPE_UNKNOWN
            }
        },
    }
}

fn analyze_sign(
    ctx: &mut AsysContext,
    scope: &Scope,
    func: &FunSign,
    errors: &mut Errors,
) -> Vec<TypeIdx> {
    // put effects in scope
    for &effect in func.effects.iter() {
        analyze_effect(ctx, effect, scope, errors);
    }

    let mut params = Vec::new();

    // put args in scope
    for (i, param) in func.inputs.iter(ParamIdx) {
        // resolve type
        let ty = analyze_type(ctx, scope, param.ty, errors);
        let ty = match ctx.asys.types[ty] {
            Type::Handler(effect, yeet, _) => {
                let handler = ctx.asys.handlers.push(HandlerIdx, HandlerDef::Param(i));
                ctx.asys
                    .insert_type(Type::Handler(effect, yeet, Some(handler)))
            }
            _ => ty,
        };
        params.push(ty);
        ctx.asys.push_val(
            param.name,
            Definition::Parameter(param.mutable, param.name, ty),
        );
    }

    params
}

fn scope_sign(ctx: &mut AsysContext, scope: &mut Scope, func: &FunSign) {
    // put args in scope
    for param in func.inputs.values() {
        // add parameter to scope
        scope.values.insert(
            ctx.parsed.idents[param.name].0.clone(),
            ctx.asys.values[param.name],
        );
    }
}

pub const TYPE_NONE: TypeIdx = TypeIdx(1);
pub const TYPE_NEVER: TypeIdx = TypeIdx(2);

const TYPE_UNKNOWN: TypeIdx = TypeIdx(0);
const TYPE_INT: TypeIdx = TypeIdx(3);
const TYPE_STR: TypeIdx = TypeIdx(4);
const TYPE_BOOL: TypeIdx = TypeIdx(5);

const TYPE_USIZE: TypeIdx = TypeIdx(6);
const TYPE_UPTR: TypeIdx = TypeIdx(7);
const TYPE_U8: TypeIdx = TypeIdx(8);
const TYPE_UINT: TypeIdx = TypeIdx(9);

pub fn analyze(parsed: &Parsed, errors: &mut Errors, target: &Target) -> Analysis {
    let os = target.lucu_os();
    let os = os.as_str();

    let mut asys = Analysis {
        capabilities: HashMap::new(),
        values: VecMap::filled(parsed.idents.len(), Val(usize::MAX)),
        exprs: VecMap::filled(parsed.exprs.len(), TYPE_UNKNOWN),
        defs: VecMap::new(),
        main: None,
        handlers: VecMap::new(),
        types: VecSet::new(),
    };

    asys.types.insert(TypeIdx, Type::Unknown);
    asys.types.insert(TypeIdx, Type::None);
    asys.types.insert(TypeIdx, Type::Never);
    asys.types.insert(TypeIdx, Type::Int);
    asys.types.insert(TypeIdx, Type::Str);
    asys.types.insert(TypeIdx, Type::Bool);
    asys.types.insert(TypeIdx, Type::USize);
    asys.types.insert(TypeIdx, Type::UPtr);
    asys.types.insert(TypeIdx, Type::U8);
    asys.types.insert(TypeIdx, Type::UInt);

    let str = asys.defs.push(Val, Definition::BuiltinType(TYPE_STR));
    let int = asys.defs.push(Val, Definition::BuiltinType(TYPE_INT));
    let usize = asys.defs.push(Val, Definition::BuiltinType(TYPE_USIZE));
    let uptr = asys.defs.push(Val, Definition::BuiltinType(TYPE_UPTR));
    let u8 = asys.defs.push(Val, Definition::BuiltinType(TYPE_U8));
    let bool = asys.defs.push(Val, Definition::BuiltinType(TYPE_BOOL));
    let uint = asys.defs.push(Val, Definition::BuiltinType(TYPE_UINT));

    let mut packages = VecMap::filled(parsed.packages.len(), Package::default());
    let vals = &mut packages[parsed.preamble].values;
    vals.insert("str".into(), str);
    vals.insert("int".into(), int);
    vals.insert("uint".into(), uint);
    vals.insert("usize".into(), usize);
    vals.insert("uptr".into(), uptr);
    vals.insert("u8".into(), u8);
    vals.insert("bool".into(), bool);

    let mut ctx = AsysContext {
        asys,
        parsed,
        packages,
    };

    // analyze effect signatures
    for (idx, package) in parsed.packages.iter(PackageIdx) {
        // put names in scope
        // TODO: error on conflict (or overloads?)
        for (i, effect) in package
            .effects
            .iter()
            .copied()
            .map(|idx| (idx, &parsed.effects[idx]))
        {
            // add effect to scope
            let val = ctx.asys.push_val(effect.name, Definition::Effect(i));
            ctx.packages[idx]
                .effects
                .insert(parsed.idents[effect.name].0.clone(), val);
        }
        for &implied in package.implied.iter() {
            let effect = match &parsed.exprs[implied].0 {
                Expression::Handler(parser::Handler::Full { effect, .. }) => effect,
                _ => panic!(),
            };
            let name = &parsed.idents[effect.effect].0;
            if let Some(effect) = ctx.packages[idx].effects.get(name).copied() {
                ctx.packages[idx].implied.insert(effect);
            }
        }
    }

    // analyze function signatures
    for (idx, package) in parsed.packages.iter(PackageIdx) {
        let mut values = HashMap::new();
        values.extend(
            ctx.packages[parsed.preamble]
                .values
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        values.extend(
            ctx.packages[idx]
                .values
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );

        let mut funs = HashMap::new();
        funs.extend(
            ctx.packages[parsed.preamble]
                .funs
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        funs.extend(
            ctx.packages[idx]
                .funs
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );

        let mut effects = HashMap::new();
        effects.extend(
            ctx.packages[parsed.preamble]
                .effects
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        effects.extend(
            ctx.packages[idx]
                .effects
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );

        let mut scoped_effects = HashSet::new();
        scoped_effects.extend(ctx.packages[parsed.preamble].implied.iter().copied());
        scoped_effects.extend(ctx.packages[idx].implied.iter().copied());

        let global_scope = Scope {
            parent: None,
            values,
            funs: &funs,
            effects: &effects,
            scoped_effects: &scoped_effects,
            pkg: idx,
        };

        for (i, effect) in package
            .effects
            .iter()
            .copied()
            .map(|idx| (idx, &parsed.effects[idx]))
        {
            for (fi, decl) in effect.functions.iter(EffFunIdx) {
                let scope = Scope {
                    parent: Some(&global_scope),
                    values: HashMap::new(),
                    funs: &funs,
                    effects: &effects,
                    scoped_effects: &HashSet::new(),
                    pkg: idx,
                };
                let return_type = analyze_return(&mut ctx, &scope, decl.sign.output, errors);
                let params = analyze_sign(&mut ctx, &scope, &decl.sign, errors);
                let val = ctx.asys.push_val(
                    decl.name,
                    Definition::EffectFunction(i, fi, params, return_type),
                );
                ctx.packages[idx]
                    .funs
                    .insert(parsed.idents[decl.name].0.clone(), val);

                // check capability
                if let Some(attr) = decl
                    .attributes
                    .iter()
                    .find(|a| ctx.parsed.idents[a.name].0.eq("capability"))
                {
                    let effect = match ctx.asys.types[return_type] {
                        Type::Handler(effect, yeets, _) => {
                            if yeets != TYPE_NEVER {
                                // TODO: error
                                todo!()
                            }
                            effect
                        }
                        _ => {
                            // TODO: error
                            todo!()
                        }
                    };

                    let allowed = !attr.settings.iter().any(|s| {
                        ctx.parsed.idents[s.0].0.eq("os")
                            && match s.1 {
                                AttributeValue::String(ref s) => !s.0.eq(os),
                                AttributeValue::Type(_) => true,
                            }
                    });
                    if allowed {
                        // TODO: error on duplicates
                        ctx.asys.capabilities.insert(effect, val);
                    }
                }
            }
        }

        for (i, fun) in package
            .functions
            .iter()
            .copied()
            .map(|i| (i, &parsed.functions[i]))
        {
            // add function to scope
            let scope = Scope {
                parent: Some(&global_scope),
                values: HashMap::new(),
                funs: &funs,
                effects: &effects,
                scoped_effects: &HashSet::new(),
                pkg: idx,
            };
            let return_type = analyze_return(&mut ctx, &scope, fun.decl.sign.output, errors);
            let params = analyze_sign(&mut ctx, &scope, &fun.decl.sign, errors);
            let val = ctx
                .asys
                .push_val(fun.decl.name, Definition::Function(i, params, return_type));
            ctx.packages[idx]
                .funs
                .insert(parsed.idents[fun.decl.name].0.clone(), val);

            // check if main
            if parsed.idents[fun.decl.name].0 == "main" {
                ctx.asys.main = Some(i);
            }

            // check capability
            if let Some(attr) = fun
                .decl
                .attributes
                .iter()
                .find(|a| ctx.parsed.idents[a.name].0.eq("capability"))
            {
                let effect = match ctx.asys.types[return_type] {
                    Type::Handler(effect, yeets, _) => {
                        if yeets != TYPE_NEVER {
                            // TODO: error
                            todo!()
                        }
                        effect
                    }
                    _ => {
                        // TODO: error
                        todo!()
                    }
                };

                let allowed = !attr.settings.iter().any(|s| {
                    ctx.parsed.idents[s.0].0.eq("os")
                        && match s.1 {
                            AttributeValue::String(ref s) => !s.0.eq(os),
                            AttributeValue::Type(_) => true,
                        }
                });
                if allowed {
                    // TODO: error on duplicates
                    ctx.asys.capabilities.insert(effect, val);
                }
            }
        }
    }

    // analyze effect and function bodies
    for (idx, package) in parsed.packages.iter(PackageIdx) {
        let mut values = HashMap::new();
        values.extend(
            ctx.packages[parsed.preamble]
                .values
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        values.extend(
            ctx.packages[idx]
                .values
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );

        let mut funs = HashMap::new();
        funs.extend(
            ctx.packages[parsed.preamble]
                .funs
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        funs.extend(
            ctx.packages[idx]
                .funs
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );

        let mut effects = HashMap::new();
        effects.extend(
            ctx.packages[parsed.preamble]
                .effects
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        effects.extend(
            ctx.packages[idx]
                .effects
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );

        let mut scoped_effects = HashSet::new();
        scoped_effects.extend(ctx.packages[parsed.preamble].implied.iter().copied());
        scoped_effects.extend(ctx.packages[idx].implied.iter().copied());

        let global_scope = Scope {
            parent: None,
            values,
            funs: &funs,
            effects: &effects,
            scoped_effects: &scoped_effects,
            pkg: idx,
        };

        // analyze effects and functions
        for &implied in package.implied.iter() {
            let mut scope = Scope {
                parent: Some(&global_scope),
                values: HashMap::new(),
                funs: &funs,
                effects: &effects,
                scoped_effects: &scoped_effects,
                pkg: idx,
            };
            analyze_expr(&mut ctx, &mut scope, implied, TYPE_UNKNOWN, false, errors);
        }
        for effect in package
            .effects
            .iter()
            .copied()
            .map(|idx| &parsed.effects[idx])
        {
            for fun in effect.functions.values() {
                let mut scope = Scope {
                    parent: Some(&global_scope),
                    values: HashMap::new(),
                    funs: &funs,
                    effects: &effects,
                    scoped_effects: &scoped_effects,
                    pkg: idx,
                };
                scope_sign(&mut ctx, &mut scope, &fun.sign);
            }
        }
        for fun in package
            .functions
            .iter()
            .copied()
            .map(|i| &parsed.functions[i])
        {
            let mut scope = Scope {
                parent: Some(&global_scope),
                values: HashMap::new(),
                funs: &funs,
                effects: &effects,
                scoped_effects: &scoped_effects,
                pkg: idx,
            };
            let val = ctx.asys.values[fun.decl.name];
            scope_sign(&mut ctx, &mut scope, &fun.decl.sign);

            let mut scoped = scope.scoped_effects.clone();
            scoped.extend(fun.decl.sign.effects.iter().filter_map(|&i| {
                let val = ctx.asys.values[i.effect];
                if val.0 == usize::MAX {
                    None
                } else {
                    Some(val)
                }
            }));
            scope.scoped_effects = &scoped;

            let expected = match ctx.asys.defs[val] {
                Definition::Function(_, _, return_type) => return_type,
                _ => unreachable!(),
            };
            analyze_expr(&mut ctx, &mut scope, fun.body, expected, false, errors).0;
        }
    }

    ctx.asys
}
