use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use either::Either;

use crate::{
    analyzer::{self, Analysis, Definition, Val},
    ast::{self, Ast, AttributeValue, BinOp, EffFunIdx, ExprIdx, Expression, PackageIdx, UnOp},
    error::{get_lines, File, FileIdx, Range, Ranged},
    vecmap::{VecMap, VecSet},
    LucuOS, Target,
};

use super::{
    AggregateType, Block, BlockIdx, Captures, Global, HandlerIdx, HandlerType, Instruction,
    ProcForeign, ProcForeignIdx, ProcIdx, ProcImpl, ProcSign, Reg, Type, TypeIdx, Value, IR,
    TYPE_BOOL, TYPE_NEVER, TYPE_NONE, TYPE_STR_SLICE,
};

impl Value {
    fn cast(&self, ir: &mut IRCtx, block: &mut Block, ty: TypeIdx) -> Value {
        match *self {
            Value::Reg(reg, val) => {
                let new = ir.next_reg(ty);
                block.instructions.push(Instruction::Cast(new, reg));
                Value::Reg(new, val)
            }
            Value::Reference(ptr) => {
                let ty = ir.insert_type(Type::Pointer(ty));
                let new = ir.next_reg(ty);
                block.instructions.push(Instruction::Cast(new, ptr));
                Value::Reference(new)
            }
            Value::Global(glob) => {
                let t = ir.insert_type(Type::Pointer(ir.ir.globals[glob]));
                let ptr = ir.next_reg(t);
                block
                    .instructions
                    .push(Instruction::GetGlobalPtr(ptr, glob));

                let t = ir.insert_type(Type::Pointer(t));
                let new = ir.next_reg(t);
                block.instructions.push(Instruction::Cast(new, ptr));
                Value::Reference(new)
            }
        }
    }
    fn non_global(&self) -> Option<&Value> {
        match self {
            Value::Global(_) => None,
            _ => Some(self),
        }
    }
    fn value(&self, ir: &mut IRCtx, block: &mut Block) -> Reg {
        match *self {
            Value::Reg(reg, _) => reg,
            Value::Reference(ptr) => {
                let reg = ir.next_reg(self.get_type(&ir.ir));
                block.instructions.push(Instruction::Load(reg, ptr));
                reg
            }
            Value::Global(glob) => {
                let reg = ir.next_reg(self.get_type(&ir.ir));
                block.instructions.push(Instruction::GetGlobal(reg, glob));
                reg
            }
        }
    }
    fn reference(&self, ir: &mut IRCtx, scope: &mut Scope, block: &mut Block) -> Reg {
        match *self {
            Value::Reg(reg, val) => {
                let ty = ir.insert_type(Type::Pointer(self.get_type(&ir.ir)));
                let ptr = ir.next_reg(ty);
                block.instructions.push(Instruction::Reference(ptr, reg));
                if let Some(val) = val {
                    scope.insert(val, Value::Reference(ptr));
                }
                ptr
            }
            Value::Reference(ptr) => ptr,
            Value::Global(glob) => {
                let ty = ir.insert_type(Type::Pointer(self.get_type(&ir.ir)));
                let reg = ir.next_reg(ty);
                block
                    .instructions
                    .push(Instruction::GetGlobalPtr(reg, glob));
                reg
            }
        }
    }
    fn register(&self) -> Reg {
        match *self {
            Value::Reg(r, _) => r,
            _ => unreachable!(),
        }
    }
}

type ResolvedGenerics = HashMap<Val, TypeIdx>;

impl TypeIdx {
    fn fill_generic(self, ir: &IRCtx, ty: analyzer::TypeIdx, gen: &mut ResolvedGenerics) {
        use analyzer::Type as T;
        match ir.asys.types[ty] {
            T::FunctionLiteral(_) => {}
            T::PackageLiteral(_) => {}

            T::Handler(eff, ty, _) => {
                if matches!(ir.asys.defs[eff], Definition::Generic(_)) {
                    // TODO: this should be the effect, not the handler
                    gen.insert(eff, self);
                }
                self.inner(&ir.ir).fill_generic(ir, ty, gen);
            }
            T::Const(ty) => {
                self.fill_generic(ir, ty, gen);
            }
            T::Pointer(ty) | T::ConstArray(_, ty) | T::Slice(ty) => {
                self.inner(&ir.ir).fill_generic(ir, ty, gen);
            }
            T::Generic(val) => {
                gen.insert(val, self);
            }

            T::Int => {}
            T::UInt => {}
            T::USize => {}
            T::UPtr => {}
            T::U8 => {}
            T::U16 => {}
            T::U32 => {}
            T::Str => {}
            T::Bool => {}
            T::None => {}
            T::Never => {}
            T::Unknown => {}
        }
    }
    fn from_type(ir: &mut IRCtx, ty: analyzer::TypeIdx, gen: &ResolvedGenerics) -> TypeIdx {
        use analyzer::Type as T;
        match ir.asys.types[ty] {
            T::Int | T::UInt => ir.insert_type(Type::Int),
            T::USize => ir.insert_type(Type::IntSize),
            T::UPtr => ir.insert_type(Type::IntPtr),
            T::U8 => ir.insert_type(Type::Int8),
            T::U16 => ir.insert_type(Type::Int16),
            T::U32 => ir.insert_type(Type::Int32),
            T::Str => {
                let u8 = ir.insert_type(Type::Int8);
                ir.insert_type(Type::Slice(u8))
            }
            T::Bool => ir.insert_type(Type::Bool),
            T::None => ir.insert_type(Type::None),
            T::Never => ir.insert_type(Type::Never),
            T::Pointer(ty) => {
                let inner = TypeIdx::from_type(ir, ty, gen);
                ir.insert_type(Type::Pointer(inner))
            }
            T::ConstArray(size, ty) => {
                let inner = TypeIdx::from_type(ir, ty, gen);
                ir.insert_type(Type::ConstArray(size, inner))
            }
            T::Slice(ty) => {
                let inner = TypeIdx::from_type(ir, ty, gen);
                ir.insert_type(Type::Slice(inner))
            }
            T::Const(ty) => TypeIdx::from_type(ir, ty, gen),
            T::Generic(val) => gen.get(&val).copied().expect("unresolved generic found"),
            T::FunctionLiteral(_) => todo!(),
            T::PackageLiteral(_) => todo!(),

            // Supposed to be handled on a case-by-case basis
            T::Handler(_, _, _) => unreachable!(),
            T::Unknown => unreachable!(),
        }
    }
    fn from_return_type(ir: &mut IRCtx, typ: analyzer::TypeIdx, gen: &ResolvedGenerics) -> TypeIdx {
        use analyzer::Type as T;
        match ir.asys.types[typ] {
            T::Handler(eff, fail, _) => {
                let fail = TypeIdx::from_type(ir, fail, gen);
                ir.insert_type(Type::HandlerOutput(eff, fail))
            }
            _ => TypeIdx::from_type(ir, typ, gen),
        }
    }
    fn from_capture(
        ir: &mut IRCtx,
        typ: analyzer::TypeIdx,
        defs: &[(ExprIdx, Option<HandlerIdx>)],
        gen: &ResolvedGenerics,
        scope: &Scope,
    ) -> TypeIdx {
        use analyzer::Type as T;
        match ir.asys.types[typ] {
            T::Handler(eff, _, Some(idx)) => match ir.asys.handlers[idx] {
                analyzer::HandlerDef::Handler(def, _) | analyzer::HandlerDef::Call(def) => {
                    let idx = defs.iter().find(|&&(expr, _)| expr == def).unwrap().1;
                    match idx {
                        Some(idx) => ir.insert_type(Type::NakedHandler(idx)),
                        None => TYPE_NEVER,
                    }
                }
                analyzer::HandlerDef::Signature => {
                    let val = scope.get(eff).expect("signature handler not in scope");
                    match ir.ir.types[val.get_type(&ir.ir)] {
                        Type::Handler(idx) => ir.insert_type(Type::Handler(idx)),
                        _ => unreachable!(),
                    }
                }
                analyzer::HandlerDef::Param(_) => unreachable!(),
                analyzer::HandlerDef::Error => unreachable!(),
            },

            _ => TypeIdx::from_type(ir, typ, gen),
        }
    }
    fn from_capture_val(
        ir: &mut IRCtx,
        val: Val,
        defs: &[(ExprIdx, Option<HandlerIdx>)],
        gen: &ResolvedGenerics,
        scope: &Scope,
    ) -> TypeIdx {
        match ir.asys.defs[val] {
            Definition::Parameter(_, _, t) => TypeIdx::from_capture(ir, t, defs, gen, scope),
            Definition::Variable(_, _, t) => TypeIdx::from_capture(ir, t, defs, gen, scope),
            Definition::EffectFunction(_, _, _) => todo!(),
            Definition::Function(_, _) => todo!(),

            // TODO: type type
            Definition::BuiltinType(_) => todo!(),
            Definition::Package(_) => todo!(),
            Definition::Generic(_) => todo!(),
            Definition::Effect(idx) => {
                todo!("{:?}", ir.parsed.idents[ir.parsed.effects[idx].name].0)
            }
        }
    }
    fn from_expr(ir: &IRCtx, expr: ExprIdx) -> analyzer::TypeIdx {
        ir.asys.exprs[expr]
    }
    fn into_result(self, ir: &mut IRCtx) -> ExprResult {
        match self {
            TYPE_NEVER => Err(Never),
            TYPE_NONE => Ok(None),
            _ => {
                let reg = ir.next_reg(self);
                Ok(Some(Value::Reg(reg, None)))
            }
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct ProcIdent {
    fun: Either<Val, (HandlerIdx, EffFunIdx)>,
    handlers: Vec<HandlerIdx>,
    handler_params: Vec<TypeIdx>,
    generics: Vec<TypeIdx>,
}

#[derive(Debug, Clone)]
struct HandlerCtx {
    effect: Val,
    global: Option<Global>,
    definition: Option<ExprIdx>,
    captures: Vec<(Val, TypeIdx, bool)>,
}

struct IRCtx<'a> {
    ir: IR,

    proc_map: HashMap<ProcIdent, Either<ProcIdx, ProcForeignIdx>>,
    implied_handlers: HashMap<Val, HandlerIdx>,
    srcloc: Option<(Val, HandlerIdx)>,
    linker: Option<(Val, HandlerIdx)>,

    handlers: VecMap<HandlerIdx, HandlerCtx>,
    foreign: HashMap<Val, HandlerIdx>,

    len: Val,

    parsed: &'a Ast,
    asys: &'a Analysis,
    files: &'a VecMap<FileIdx, File>,
}

impl<'a> IRCtx<'a> {
    fn copy_reg(&mut self, reg: Reg) -> Reg {
        let typ = self.ir.regs[reg];
        self.next_reg(typ)
    }
    fn next_handler_reg(&mut self, handler: HandlerIdx) -> Reg {
        let ty = self.insert_type(Type::NakedHandler(handler));
        self.next_reg(ty)
    }
    fn next_reg(&mut self, typ: TypeIdx) -> Reg {
        self.ir.regs.push(Reg, typ)
    }
    fn insert_type(&mut self, ty: Type) -> TypeIdx {
        *self.ir.types.insert(TypeIdx, ty)
    }
    fn get_or_implicit(
        &mut self,
        val: Val,
        scope: &Scope,
        block: &mut Block,
        loc: Range,
    ) -> Option<Value> {
        match scope.get(val) {
            Some(r) => Some(r.clone()),
            None => {
                match self.srcloc.and_then(|(v, idx)| {
                    if v == val {
                        let (start, _end) = get_lines(&self.files[loc.3].content, loc);

                        let src = self.next_reg(TYPE_STR_SLICE);
                        block.instructions.push(Instruction::InitString(
                            src,
                            format!(
                                "{}:{}:{}",
                                self.files[loc.3].name,
                                start.line + 1,
                                start.column + 1
                            ),
                        ));
                        let handler_ty = self.insert_type(Type::NakedHandler(idx));
                        let handler = self.next_reg(handler_ty);
                        block
                            .instructions
                            .push(Instruction::Handler(handler, vec![src]));
                        Some(Value::Reg(handler, None))
                    } else {
                        None
                    }
                }) {
                    Some(r) => Some(r),
                    None => match self.implied_handlers.get(&val).copied() {
                        Some(idx) => {
                            let ty = self.insert_type(Type::NakedHandler(idx));
                            let reg = self.next_reg(ty);
                            Some(Value::Reg(reg, None))
                        }
                        None => None,
                    },
                }
            }
        }
    }
    fn new_handler(
        &mut self,
        handler_defs: &[(ExprIdx, Option<HandlerIdx>)],
        eff_val: Val,
        global: bool,
        break_type: TypeIdx,
        definition: ExprIdx,
        scope: &Scope,
    ) -> HandlerIdx {
        let captures = match self.asys.types[self.asys.exprs[definition]] {
            analyzer::Type::Handler(_, _, def) => match def.map(|h| &self.asys.handlers[h]) {
                Some(analyzer::HandlerDef::Handler(_, captures)) => captures
                    .iter()
                    .map(|c| {
                        let ty = match scope.get(c.val) {
                            Some(reg) => reg.get_type(&self.ir),
                            None => TypeIdx::from_capture_val(
                                self,
                                c.val,
                                handler_defs,
                                &scope.generics,
                                scope,
                            ),
                        };
                        let ty = match c.mutable {
                            true => self.insert_type(Type::Pointer(ty)),
                            false => ty,
                        };
                        (c.val, ty, c.mutable)
                    })
                    .collect(),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };

        // generate handler
        let global = match global {
            true => {
                let ty = self.insert_type(Type::Handler(HandlerIdx(self.handlers.len())));
                Some(self.ir.globals.push(Global, ty))
            }
            false => None,
        };
        let handler_idx = self.handlers.push(
            HandlerIdx,
            HandlerCtx {
                global,
                effect: eff_val,
                definition: Some(definition),
                captures,
            },
        );
        self.ir.handler_type.push_value(HandlerType {
            captures: self.handlers[handler_idx]
                .captures
                .iter()
                .copied()
                .map(|(_, t, _)| t)
                .collect(),
            break_ty: break_type,
        });

        handler_idx
    }
}

#[derive(Debug, Default)]
struct Scope<'a> {
    parent: Option<&'a Scope<'a>>,
    values: HashMap<Val, Value>,
    generics: Rc<ResolvedGenerics>,
}

impl<'a> Scope<'a> {
    fn insert(&mut self, k: Val, v: Value) {
        self.values.insert(k, v);
    }
    fn get(&self, k: Val) -> Option<&Value> {
        match self.values.get(&k) {
            Some(v) => Some(v),
            None => self.parent.map(|p| p.get(k)).unwrap_or_default(),
        }
    }
}

#[derive(Debug)]
struct ProcCtx<'a> {
    proc_idx: ProcIdx,
    expr: ExprIdx,
    inside_handler: Option<HandlerIdx>,
    scope: Scope<'a>,
    handler_defs: Rc<[(ExprIdx, Option<HandlerIdx>)]>,
}

impl<'a> ProcCtx<'a> {
    fn with_expr(&mut self, expr: ExprIdx) -> &mut Self {
        self.expr = expr;
        self
    }
    fn child<T>(
        &'a self,
        expr: ExprIdx,
        f: impl FnOnce(&mut Self) -> T,
    ) -> (HashMap<Val, Value>, T) {
        let mut child = Self {
            proc_idx: self.proc_idx,
            expr,
            inside_handler: self.inside_handler,
            scope: Scope {
                parent: Some(&self.scope),
                values: HashMap::new(),
                generics: Rc::clone(&self.scope.generics),
            },
            handler_defs: Rc::clone(&self.handler_defs),
        };

        let t = f(&mut child);

        let mut values = child.scope.values;
        values.retain(|k, _| self.scope.values.contains_key(k));
        (values, t)
    }
}
type ProcTodo = Vec<ProcCtx<'static>>;

fn define_function(
    ir: &mut IRCtx,
    fun: Either<Val, (HandlerIdx, EffFunIdx)>,
    handlers: Vec<HandlerIdx>,
    debug_name: String,
    inputs: Vec<Reg>,
    output: TypeIdx,
    instructions: Vec<Instruction>,
) -> ProcIdx {
    let proc = ir.ir.proc_sign.push(
        ProcIdx,
        ProcSign {
            inputs,
            captures: None,
            output,
            debug_name,
            unhandled: Vec::new(),
            handled: Vec::new(),
            redirect: Vec::new(),
        },
    );
    ir.ir.proc_impl.push_value(ProcImpl {
        blocks: vec![Block {
            instructions,
            next: None,
        }]
        .into(),
    });
    ir.proc_map.insert(
        ProcIdent {
            fun,
            handlers,
            handler_params: Vec::new(),
            generics: Vec::new(),
        },
        Either::Left(proc),
    );
    proc
}

pub fn generate_ir(
    ctx: &Ast,
    asys: &Analysis,
    target: &Target,
    files: &VecMap<FileIdx, File>,
) -> IR {
    let mut ir = IRCtx {
        proc_map: HashMap::new(),
        handlers: VecMap::new(),
        implied_handlers: HashMap::new(),
        parsed: ctx,
        asys,
        files,
        srcloc: None,
        linker: None,
        ir: IR {
            proc_sign: VecMap::new(),
            proc_impl: VecMap::new(),
            proc_foreign: VecMap::new(),
            entry: ProcIdx(0),

            regs: VecMap::new(),
            globals: VecMap::new(),

            types: VecSet::new(),
            handler_type: VecMap::new(),
            aggregates: VecMap::new(),

            links: HashSet::new(),
        },
        len: Val(0),
        foreign: HashMap::new(),
    };
    ir.insert_type(Type::Never);
    ir.insert_type(Type::None);

    let byte = ir.insert_type(Type::Int8);
    let byteptr = ir.insert_type(Type::Pointer(byte));
    let arrsize = ir.insert_type(Type::IntSize);

    ir.ir.aggregates.push_value(AggregateType {
        children: vec![byteptr, arrsize],
        debug_name: "str".into(),
    });
    ir.insert_type(Type::Slice(byte));
    ir.insert_type(Type::Int);
    ir.insert_type(Type::Bool);

    // capabilities
    let mut capabilities: HashMap<Val, Reg> = HashMap::new();
    let mut start_instructions = Vec::new();

    // define linker effect
    let linker_effect = get_effect(ctx, ctx.preamble, "foreign").unwrap();
    let linker = ir.handlers.push(
        HandlerIdx,
        HandlerCtx {
            effect: asys.values[linker_effect.name],
            global: None,
            definition: None,
            captures: Vec::new(),
        },
    );
    ir.ir.handler_type.push_value(HandlerType {
        captures: Vec::new(),
        break_ty: TYPE_NEVER,
    });
    let linker_reg = ir.next_handler_reg(linker);
    start_instructions.push(Instruction::Handler(linker_reg, vec![]));
    capabilities.insert(asys.values[linker_effect.name], linker_reg);
    ir.linker = Some((asys.values[linker_effect.name], linker));

    // define system effect
    let sys_effect = get_effect(ctx, ctx.system, "sys");
    if let Some(sys_effect) = sys_effect {
        let sys = ir.handlers.push(
            HandlerIdx,
            HandlerCtx {
                effect: asys.values[sys_effect.name],
                global: None,
                definition: None,
                captures: Vec::new(),
            },
        );
        ir.ir.handler_type.push_value(HandlerType {
            captures: Vec::new(),
            break_ty: TYPE_NEVER,
        });
        let sys_reg = ir.next_handler_reg(sys);
        start_instructions.push(Instruction::Handler(sys_reg, vec![]));
        capabilities.insert(asys.values[sys_effect.name], sys_reg);

        let intptr = ir.insert_type(Type::IntPtr);
        match target.lucu_os() {
            LucuOS::Linux => {
                for n in 0..=6 {
                    let nr = ir.next_reg(intptr);
                    let inputs = (0..n).map(|_| ir.next_reg(intptr)).collect::<Vec<_>>();
                    let output = ir.next_reg(intptr);

                    define_function(
                        &mut ir,
                        Either::Right((sys, EffFunIdx(n))),
                        vec![],
                        format!("syscall{}", n),
                        std::iter::once(nr).chain(inputs.iter().copied()).collect(),
                        intptr,
                        vec![
                            Instruction::Syscall(Some(output), nr, inputs),
                            Instruction::Return(Some(output)),
                        ],
                    );
                }
            }
            LucuOS::Windows => {
                for (i, n) in vec![2, 9].into_iter().enumerate() {
                    let nr = ir.next_reg(intptr);
                    let inputs = (0..n).map(|_| ir.next_reg(intptr)).collect::<Vec<_>>();
                    let output = ir.next_reg(intptr);

                    define_function(
                        &mut ir,
                        Either::Right((sys, EffFunIdx(i))),
                        vec![],
                        format!("syscall{}", n),
                        std::iter::once(nr).chain(inputs.iter().copied()).collect(),
                        intptr,
                        vec![
                            Instruction::Syscall(Some(output), nr, inputs),
                            Instruction::Return(Some(output)),
                        ],
                    );
                }

                let output_ty = ir.insert_type(Type::ConstArray(3, intptr));
                let output = ir.next_reg(output_ty);

                let intptr_ptr = ir.insert_type(Type::Pointer(intptr));
                let peb_int = ir.next_reg(intptr);
                let peb_ptr = ir.next_reg(intptr_ptr);

                let params_int_ptr = ir.next_reg(intptr_ptr);
                let params_int = ir.next_reg(intptr);
                let params_ptr = ir.next_reg(intptr_ptr);

                let stdio_ptr_ty = ir.insert_type(Type::Pointer(output_ty));
                let stdio_int_ptr = ir.next_reg(intptr_ptr);
                let stdio_ptr = ir.next_reg(stdio_ptr_ty);

                let four = ir.next_reg(arrsize);

                define_function(
                    &mut ir,
                    Either::Right((sys, EffFunIdx(2))),
                    vec![],
                    "stdio".into(),
                    vec![],
                    output_ty,
                    vec![
                        Instruction::Init(four, 4),
                        // get PEB*
                        Instruction::GS(peb_int, 0x60),
                        Instruction::Cast(peb_ptr, peb_int),
                        // get RTL_USER_PROCESS_PARAMETERS*
                        Instruction::AdjacentPtr(params_int_ptr, peb_ptr, four),
                        Instruction::Load(params_int, params_int_ptr),
                        Instruction::Cast(params_ptr, params_int),
                        // get HANDLE[3]*
                        Instruction::AdjacentPtr(stdio_int_ptr, params_ptr, four),
                        Instruction::Cast(stdio_ptr, stdio_int_ptr),
                        // get HANDLE[3]
                        Instruction::Load(output, stdio_ptr),
                        Instruction::Return(Some(output)),
                    ],
                );
            }
            _ => {}
        }
    }

    // define srcloc
    let srcloc_effect = get_effect(ctx, ctx.preamble, "srcloc").unwrap();
    let srcloc = ir.handlers.push(
        HandlerIdx,
        HandlerCtx {
            effect: asys.values[srcloc_effect.name],
            global: None,
            definition: None,
            captures: Vec::new(),
        },
    );
    ir.ir.handler_type.push_value(HandlerType {
        captures: vec![TYPE_STR_SLICE],
        break_ty: TYPE_NEVER,
    });
    ir.srcloc = Some((asys.values[srcloc_effect.name], srcloc));

    let srcloc_ty = ir.insert_type(Type::Handler(srcloc));
    let input = ir.next_reg(srcloc_ty);
    let output = ir.next_reg(TYPE_STR_SLICE);
    let srcloc_proc = define_function(
        &mut ir,
        Either::Right((srcloc, EffFunIdx(0))),
        vec![],
        "source_location".into(),
        vec![input],
        TYPE_STR_SLICE,
        vec![
            Instruction::Member(output, input, 0),
            Instruction::Return(Some(output)),
        ],
    );

    // define unreachable
    // TODO: differ depending on settings (debug/release)
    let unreachable_fun = get_function(ctx, ctx.preamble, "unreachable");
    define_function(
        &mut ir,
        Either::Left(asys.values[unreachable_fun.decl.name]),
        vec![],
        "unreachable".into(),
        vec![],
        TYPE_NEVER,
        vec![Instruction::Unreachable],
    );

    // define trap
    let trap_fun = get_function(ctx, ctx.preamble, "trap");
    let input = ir.next_reg(srcloc_ty);
    let str1 = ir.next_reg(TYPE_STR_SLICE);
    let str2 = ir.next_reg(TYPE_STR_SLICE);
    let str3 = ir.next_reg(TYPE_STR_SLICE);
    define_function(
        &mut ir,
        Either::Left(asys.values[trap_fun.decl.name]),
        vec![srcloc],
        "trap".into(),
        vec![input],
        TYPE_NEVER,
        vec![
            Instruction::InitString(str1, "trapped at ".into()),
            Instruction::Call(srcloc_proc, Some(str2), vec![input]),
            Instruction::InitString(str3, "\n".into()),
            Instruction::Trace(str1),
            Instruction::Trace(str2),
            Instruction::Trace(str3),
            Instruction::Trap,
            Instruction::Unreachable,
        ],
    );

    // define trace
    let trace_fun = get_function(ctx, ctx.preamble, "trace");
    let input = ir.next_reg(TYPE_STR_SLICE);
    define_function(
        &mut ir,
        Either::Left(asys.values[trace_fun.decl.name]),
        vec![],
        "trace".into(),
        vec![input],
        TYPE_NONE,
        vec![Instruction::Trace(input), Instruction::Return(None)],
    );

    // find main function
    let mut proc_todo = Vec::new();
    let main = asys.main.expect("no main function");
    let fun = &ir.parsed.functions[main];

    ir.len = asys.values[get_function(ctx, ctx.preamble, "len").decl.name];

    // generate foreign effects
    for eff in ctx.effects.values() {
        if let Some(attr) = eff
            .attributes
            .iter()
            .find(|a| ctx.idents[a.name].0.eq("foreign"))
        {
            let val = asys.values[eff.name];

            // get handler type
            let ty = attr
                .settings
                .iter()
                .find(|a| ctx.idents[a.0].0.eq("handler"))
                .and_then(|a| match a.1 {
                    AttributeValue::String(_) => None,
                    AttributeValue::Type(ty) => match ctx.types[ty].0 {
                        // TODO: support all types
                        ast::Type::Path(ref id) if ctx.idents[id.ident.ident].0.eq("uptr") => {
                            Some(ir.insert_type(Type::IntPtr))
                        }
                        _ => None,
                    },
                });

            // define handler
            let handler = ir.handlers.push(
                HandlerIdx,
                HandlerCtx {
                    effect: val,
                    global: None,
                    definition: None,
                    captures: Vec::new(),
                },
            );
            ir.ir.handler_type.push_value(HandlerType {
                captures: ty.into_iter().collect(),
                break_ty: TYPE_NEVER,
            });
            let handler_ty = ir.insert_type(Type::Handler(handler));
            ir.foreign.insert(val, handler);

            // get prefix
            let prefix = attr
                .settings
                .iter()
                .find(|a| ctx.idents[a.0].0.eq("prefix"))
                .and_then(|a| match a.1 {
                    AttributeValue::String(ref s) => Some(s.0.as_str()),
                    AttributeValue::Type(_) => None,
                })
                .unwrap_or("");

            // define functions
            for (idx, fun) in eff.functions.iter(EffFunIdx) {
                let sign = match asys.defs[asys.values[fun.name]] {
                    Definition::EffectFunction(_, _, ref sign) => sign,
                    _ => unreachable!(),
                };
                use analyzer::Type as T;
                let output = match ir.asys.types[sign.return_type] {
                    T::Handler(eff, analyzer::TYPE_NEVER, _) => {
                        ir.insert_type(Type::NakedHandler(ir.foreign[&eff]))
                    }
                    _ => TypeIdx::from_type(&mut ir, sign.return_type, &HashMap::new()),
                };
                let foreign = ProcForeign {
                    inputs: Iterator::chain(
                        std::iter::once(handler_ty),
                        sign.params
                            .iter()
                            .copied()
                            .map(|ty| TypeIdx::from_type(&mut ir, ty, &HashMap::new())),
                    )
                    .collect(),
                    output,
                    symbol: format!("{}{}", prefix, ctx.idents[fun.name].0),
                };

                let foreign = ir.ir.proc_foreign.push(ProcForeignIdx, foreign);
                ir.proc_map.insert(
                    ProcIdent {
                        fun: Either::Right((handler, idx)),
                        handlers: Vec::new(),
                        handler_params: Vec::new(),
                        generics: Vec::new(),
                    },
                    Either::Right(foreign),
                );
            }
        }
    }

    // generate all capabilities
    let mut capabilities_todo = HashMap::new();

    let mut effects = fun
        .decl
        .sign
        .effects
        .iter()
        .map(|i| asys.values[i.ident.ident])
        .collect::<Vec<_>>();
    while let Some(val) = effects.pop() {
        // we already have this capability defined
        if capabilities.contains_key(&val) || capabilities_todo.contains_key(&val) {
            continue;
        }

        // this has a capability definition
        match asys.capabilities.get(&val).copied() {
            Some(fun) => {
                // add function effects to used capabilities
                // TODO: support typeclass effects
                match asys.defs[fun] {
                    Definition::EffectFunction(idx, fun, _) => {
                        effects.extend(
                            ctx.effects[idx].functions[fun]
                                .sign
                                .effects
                                .iter()
                                .map(|i| asys.values[i.ident.ident]),
                        );
                    }
                    Definition::Function(fun, _) => {
                        effects.extend(
                            ctx.functions[fun]
                                .decl
                                .sign
                                .effects
                                .iter()
                                .map(|i| asys.values[i.ident.ident]),
                        );
                    }
                    _ => unreachable!(),
                }
                // add function to capabilities todo
                capabilities_todo.insert(val, fun);
            }
            None => unreachable!(),
        }
    }

    while !capabilities_todo.is_empty() {
        let len = capabilities_todo.len();
        capabilities_todo.retain(|&effect, &mut fun| {
            // get function signature
            let (sign, handler) = match asys.defs[fun] {
                Definition::EffectFunction(eff, fun, _) => {
                    let eff_val = asys.values[ctx.effects[eff].name];
                    let Some(handler) = capabilities.get(&eff_val).copied() else {
                        return true;
                    };
                    (&ctx.effects[eff].functions[fun].sign, Some(handler))
                }
                Definition::Function(fun, _) => (&ctx.functions[fun].decl.sign, None),
                _ => unreachable!(),
            };

            // get function handlers
            let Some(mut handlers) = sign
                .effects
                .iter()
                .map(|e| {
                    let effect = ir.asys.values[e.ident.ident];
                    capabilities.get(&effect).copied()
                })
                .collect::<Option<Vec<_>>>()
            else {
                return true;
            };
            if let Some(handler) = handler {
                handlers.push(handler);
            }

            // get function
            let mut handler_tys = handlers
                .iter()
                .copied()
                .map(|r| match ir.ir.types[ir.ir.regs[r]] {
                    Type::NakedHandler(ty) => ty,
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>();

            let proc = match asys.defs[fun] {
                Definition::EffectFunction(_, fun, ref sign) => {
                    let output =
                        TypeIdx::from_return_type(&mut ir, sign.return_type, &HashMap::new());
                    let handler = handler_tys.pop().unwrap();
                    let def = ir.handlers[handler].definition;
                    gen_handler_proc(
                        &mut ir,
                        ProcIdent {
                            fun: Either::Right((handler, fun)),
                            handlers: handler_tys,
                            handler_params: Vec::new(),
                            generics: Vec::new(),
                        },
                        def,
                        &[],
                        output,
                        Rc::new(HashMap::new()),
                        &mut proc_todo,
                    )
                }
                Definition::Function(fun, ref sign) => {
                    let output =
                        TypeIdx::from_return_type(&mut ir, sign.return_type, &HashMap::new());
                    let val = asys.values[ctx.functions[fun].decl.name];
                    gen_proc(
                        &mut ir,
                        ProcIdent {
                            fun: Either::Left(val),
                            handlers: handler_tys,
                            handler_params: Vec::new(),
                            generics: Vec::new(),
                        },
                        &ctx.functions[fun],
                        &[],
                        output,
                        Rc::new(HashMap::new()),
                        &mut proc_todo,
                    )
                }
                _ => unreachable!(),
            };

            // call function
            let out = ir.next_reg(ir.ir.proc_sign[proc].output);
            start_instructions.push(Instruction::Call(proc, Some(out), handlers));

            let out = match ir.ir.types[ir.ir.regs[out]] {
                Type::NakedHandler(_) => out,
                Type::RawHandler(h, _) => {
                    let unraw = ir.next_handler_reg(h);
                    start_instructions.push(Instruction::UnrawHandler(unraw, out));
                    unraw
                }
                Type::Never => {
                    // TODO: error in analyzer
                    panic!("capability never returns");
                }
                _ => unreachable!(),
            };

            capabilities.insert(effect, out);
            false
        });
        if capabilities_todo.len() == len {
            // TODO: error in analyzer
            panic!("could not define capabilities: {:?}", capabilities_todo);
        }
    }

    // generate main signature
    let handlers = fun
        .decl
        .sign
        .effects
        .iter()
        .map(|i| capabilities[&asys.values[i.ident.ident]])
        .collect::<Vec<_>>();
    let handler_tys = handlers
        .iter()
        .copied()
        .map(|r| match ir.ir.types[ir.ir.regs[r]] {
            Type::NakedHandler(ty) => ty,
            _ => unreachable!(),
        })
        .collect::<Vec<_>>();

    let val = ir.asys.values[fun.decl.name];
    let main = generate_proc_sign(
        &mut ir,
        Some(Either::Left(val)),
        Cow::Owned(handler_tys),
        &[],
        &Vec::new(),
        TYPE_NONE,
        Rc::new(HashMap::new()),
        "main".into(),
        fun.body,
        None,
        &mut proc_todo,
    );

    // generate implied handlers
    for expr in ctx
        .packages
        .values()
        .flat_map(|p| p.implied.iter())
        .copied()
    {
        let (eff_val, break_type) = match ir.asys.types[ir.asys.exprs[expr]] {
            analyzer::Type::Handler(e, t, _) => {
                // TODO: generic break types
                (e, TypeIdx::from_type(&mut ir, t, &HashMap::new()))
            }
            _ => unreachable!(),
        };

        let handler_idx = ir.new_handler(&[], eff_val, false, break_type, expr, &Scope::default());

        // add handler to implied
        ir.implied_handlers.insert(eff_val, handler_idx);
    }

    // generate
    while !proc_todo.is_empty() {
        let ctx = proc_todo.remove(0);
        let proc = generate_proc_impl(&mut ir, ctx, &mut proc_todo);
        ir.ir.proc_impl.push_value(proc);
    }

    // bubble up unhandled
    let mut done = false;
    while !done {
        done = true;
        for callee in ir.ir.proc_sign.keys(ProcIdx) {
            for called in ir.ir.proc_impl[callee].calls() {
                if let Some((callee, called)) = ir.ir.proc_sign.get_mut2(callee, called) {
                    for handler in called.unhandled.iter().cloned() {
                        let handler = callee
                            .redirect
                            .iter()
                            .copied()
                            .find(|&(clone, _)| clone == handler)
                            .map(|(_, original)| original)
                            .unwrap_or(handler);
                        if !callee.handled.contains(&handler)
                            && !callee.unhandled.contains(&handler)
                        {
                            callee.unhandled.push(handler);
                            done = false;
                        }
                    }
                }
            }
        }
    }

    // generate entry
    start_instructions.push(Instruction::Call(main, None, handlers));
    start_instructions.push(Instruction::Return(None));
    ir.ir.entry = ir.ir.proc_sign.push(
        ProcIdx,
        ProcSign {
            inputs: Vec::new(),
            captures: None,
            output: TYPE_NONE,
            debug_name: "_entry".into(),
            unhandled: Vec::new(),
            handled: Vec::new(),
            redirect: Vec::new(),
        },
    );
    ir.ir.proc_impl.push_value(ProcImpl {
        blocks: vec![Block {
            instructions: start_instructions,
            next: None,
        }]
        .into(),
    });

    // return ir
    ir.ir
}

fn get_effect<'a>(ctx: &'a Ast, package: PackageIdx, name: &str) -> Option<&'a ast::Effect> {
    ctx.packages[package]
        .effects
        .iter()
        .copied()
        .map(|i| &ctx.effects[i])
        .find(|e| ctx.idents[e.name].0.eq(name))
}

fn get_function<'a>(ctx: &'a Ast, package: PackageIdx, name: &str) -> &'a ast::Function {
    ctx.packages[package]
        .functions
        .iter()
        .copied()
        .map(|i| &ctx.functions[i])
        .find(|f| ctx.idents[f.decl.name].0.eq(name))
        .unwrap()
}

fn get_proc(
    ir: &mut IRCtx,
    val: Val,
    proc_idx: ProcIdx,
    scope: &Scope,
    param_types: Box<[TypeIdx]>,
    output: TypeIdx,
    reg_args: Option<(&mut Vec<Value>, &mut Block, Range)>,
    proc_todo: &mut ProcTodo,
) -> Either<ProcIdx, ProcForeignIdx> {
    match ir.asys.defs[val] {
        Definition::EffectFunction(eff_idx, eff_fun_idx, ref sign) => {
            // get generics
            let generics = Rc::new(get_generics(ir, sign, &param_types, output));

            if let Some((reg_args, block, loc)) = reg_args {
                // get handler
                let eff_val = ir.asys.values[ir.parsed.effects[eff_idx].name];
                let handler_val = ir
                    .get_or_implicit(eff_val, scope, block, loc)
                    .unwrap_or_else(|| {
                        panic!(
                            "effect {:?} not in scope when finding effect function in {}. scope: {:?}",
                            eff_val, ir.ir.proc_sign[proc_idx].debug_name, scope
                        )
                    });
                let handler_idx = match ir.ir.types[handler_val.get_type(&ir.ir)] {
                    Type::NakedHandler(handler_idx) => {
                        let proc = &mut ir.ir.proc_sign[proc_idx];
                        if !proc.handled.contains(&handler_idx) {
                            proc.handled.push(handler_idx);
                        }
                        handler_idx
                    }
                    Type::Handler(handler_idx) => handler_idx,
                    _ => panic!(),
                };

                // get closure
                let len = reg_args.len();
                let proc = get_handler_proc(
                    ir,
                    handler_idx,
                    eff_fun_idx,
                    proc_idx,
                    scope,
                    param_types,
                    output,
                    generics,
                    Some((reg_args, block, loc)),
                    proc_todo,
                );
                if let Some(reg) = handler_val.non_global().cloned() {
                    match proc {
                        Either::Left(_) => reg_args.insert(len, reg),

                        // for foreign functions, insert handler at the start
                        Either::Right(_) => reg_args.insert(0, reg),
                    }
                }
                proc
            } else {
                // get handler
                let eff_val = ir.asys.values[ir.parsed.effects[eff_idx].name];
                let handler_val = ir
                    .get_or_implicit(
                        eff_val,
                        scope,
                        &mut Block::default(),
                        Ranged((), 0, 0, FileIdx(0)),
                    )
                    .unwrap_or_else(|| {
                        panic!(
                            "effect {:?} not in scope when finding effect function in {}. scope: {:?}",
                            eff_val, ir.ir.proc_sign[proc_idx].debug_name, scope
                        )
                    });
                let handler_idx = match ir.ir.types[handler_val.get_type(&ir.ir)] {
                    Type::NakedHandler(handler_idx) => {
                        let proc = &mut ir.ir.proc_sign[proc_idx];
                        if !proc.handled.contains(&handler_idx) {
                            proc.handled.push(handler_idx);
                        }
                        handler_idx
                    }
                    Type::Handler(handler_idx) => handler_idx,
                    _ => panic!(),
                };

                get_handler_proc(
                    ir,
                    handler_idx,
                    eff_fun_idx,
                    proc_idx,
                    scope,
                    param_types,
                    output,
                    generics,
                    None,
                    proc_todo,
                )
            }
        }
        Definition::Function(func_idx, ref sign) => {
            // get generics
            let generics = Rc::new(get_generics(ir, sign, &param_types, output));
            let mut sorted = generics.iter().map(|(&k, &v)| (k, v)).collect::<Vec<_>>();
            sorted.sort_unstable_by_key(|v| v.0 .0);
            let sorted = sorted.into_iter().map(|(_, v)| v).collect::<Vec<_>>();

            // create proc identity
            let fun = &ir.parsed.functions[func_idx];

            let effects = fun
                .decl
                .sign
                .effects
                .iter()
                .map(|e| {
                    let effect = ir.asys.values[e.ident.ident];

                    // TODO: this doesn't need block/loc info
                    let handler_val = ir
                        .get_or_implicit(
                            effect,
                            scope,
                            &mut Block::default(),
                            Ranged((), 0, 0, FileIdx(0)),
                        )
                        .unwrap_or_else(|| {
                            panic!(
                                "effect not in scope when finding call handlers for '{}' in {}",
                                ir.parsed.idents[fun.decl.name].0,
                                ir.ir.proc_sign[proc_idx].debug_name
                            )
                        });

                    match ir.ir.types[handler_val.get_type(&ir.ir)] {
                        Type::NakedHandler(handler_idx) => {
                            let proc = &mut ir.ir.proc_sign[proc_idx];
                            if !proc.handled.contains(&handler_idx) {
                                proc.handled.push(handler_idx);
                            }
                            handler_idx
                        }
                        Type::Handler(handler_idx) => handler_idx,
                        _ => panic!(),
                    }
                })
                .collect();

            let procident = ProcIdent {
                fun: Either::Left(val),
                handlers: effects,
                handler_params: param_types
                    .iter()
                    .copied()
                    .filter(|t| t.is_handler(&ir.ir))
                    .collect(),
                generics: sorted,
            };

            if let Some((reg_args, block, loc)) = reg_args {
                reg_args.extend(procident.handlers.iter().filter_map(|&idx| {
                    ir.get_or_implicit(ir.handlers[idx].effect, scope, block, loc)
                        .unwrap()
                        .non_global()
                        .cloned()
                }));
            }

            // get proc
            if !ir.proc_map.contains_key(&procident) {
                Either::Left(gen_proc(
                    ir,
                    procident,
                    fun,
                    &param_types,
                    output,
                    generics,
                    proc_todo,
                ))
            } else {
                ir.proc_map[&procident]
            }
        }
        _ => todo!(),
    }
}

fn get_generics(
    ir: &IRCtx,
    sign: &analyzer::FunSign,
    param_types: &[TypeIdx],
    output: TypeIdx,
) -> ResolvedGenerics {
    let mut generics = HashMap::new();

    for (sign, param) in sign.params.iter().copied().zip(param_types.iter().copied()) {
        param.fill_generic(ir, sign, &mut generics);
    }
    output.fill_generic(ir, sign.return_type, &mut generics);

    generics
}

fn gen_proc(
    ir: &mut IRCtx,
    procident: ProcIdent,
    fun: &ast::Function,
    param_types: &[TypeIdx],
    output: TypeIdx,
    generics: Rc<ResolvedGenerics>,
    proc_todo: &mut ProcTodo,
) -> ProcIdx {
    let val = procident.fun.unwrap_left();
    if val == ir.len {
        // len definition
        let output = ir.insert_type(Type::IntSize);
        let input = ir.next_reg(param_types[0]);
        let proc_idx = ir.ir.proc_sign.push(
            ProcIdx,
            ProcSign {
                inputs: vec![input],
                captures: None,
                output,
                debug_name: "len".into(),
                unhandled: Vec::new(),
                handled: Vec::new(),
                redirect: Vec::new(),
            },
        );
        proc_todo.push(ProcCtx {
            proc_idx,
            expr: fun.body,
            inside_handler: None,
            scope: Scope {
                parent: None,
                values: HashMap::new(),
                generics,
            },
            handler_defs: Rc::new([]),
        });
        ir.proc_map.insert(procident, Either::Left(proc_idx));

        return proc_idx;
    }

    let handlers = &procident.handlers;

    // get params
    let params = fun
        .decl
        .sign
        .inputs
        .values()
        .map(|param| ir.asys.values[param.name])
        .zip(param_types.iter().copied())
        .map(|(a, b)| (a, b, false))
        .collect::<Vec<_>>();

    // generate debug name
    let mut debug_name = ir.parsed.idents[fun.decl.name].0.clone();

    if !handlers.is_empty() {
        debug_name += ".";

        for &handler in handlers.iter() {
            let eff_val = ir.handlers[handler].effect;
            let eff_name = ir
                .parsed
                .effects
                .values()
                .find(|e| ir.asys.values[e.name] == eff_val)
                .map(|e| ir.parsed.idents[e.name].0.as_str())
                .unwrap_or("debug");

            debug_name += eff_name;
            debug_name += ".";
            debug_name += usize::from(handler).to_string().as_str();
            debug_name += ".";
        }

        debug_name.pop();
    }

    // generate func
    let output = match ir.asys.types[ir.asys.exprs[fun.body]] {
        analyzer::Type::Never => TYPE_NEVER,
        _ => output,
    };

    generate_proc_sign(
        ir,
        Some(procident.fun),
        Cow::Owned(procident.handlers),
        &[],
        &params,
        output,
        generics,
        debug_name,
        fun.body,
        None,
        proc_todo,
    )
}

fn get_handler_proc(
    ir: &mut IRCtx,
    handler_idx: HandlerIdx,
    eff_fun_idx: EffFunIdx,
    proc_idx: ProcIdx,
    scope: &Scope,
    param_types: Box<[TypeIdx]>,
    output: TypeIdx,
    generics: Rc<ResolvedGenerics>,
    reg_args: Option<(&mut Vec<Value>, &mut Block, Range)>,
    proc_todo: &mut ProcTodo,
) -> Either<ProcIdx, ProcForeignIdx> {
    let def = ir.handlers[handler_idx].definition;

    let eff_val = ir.handlers[handler_idx].effect;
    let effects = match ir.asys.defs[eff_val] {
        Definition::Effect(eff_idx) => {
            let decl = &ir.parsed.effects[eff_idx].functions[eff_fun_idx];
            decl.sign
                .effects
                .iter()
                .map(|e| {
                    let effect = ir.asys.values[e.ident.ident];

                    // TODO: this doesn't need block/loc info
                    let handler_val = ir
                        .get_or_implicit(
                            effect,
                            scope,
                            &mut Block::default(),
                            Ranged((), 0, 0, FileIdx(0)),
                        )
                        .expect("effect not in scope when finding effect function call handlers");

                    match ir.ir.types[handler_val.get_type(&ir.ir)] {
                        Type::NakedHandler(handler_idx) => {
                            let proc = &mut ir.ir.proc_sign[proc_idx];
                            if !proc.handled.contains(&handler_idx) {
                                proc.handled.push(handler_idx);
                            }
                            handler_idx
                        }
                        Type::Handler(handler_idx) => handler_idx,
                        _ => panic!(),
                    }
                })
                .collect()
        }
        _ => unreachable!(),
    };

    let mut sorted = generics.iter().map(|(&k, &v)| (k, v)).collect::<Vec<_>>();
    sorted.sort_unstable_by_key(|v| v.0 .0);
    let sorted = sorted.into_iter().map(|(_, v)| v).collect::<Vec<_>>();

    let procident = ProcIdent {
        fun: Either::Right((handler_idx, eff_fun_idx)),
        handlers: effects,
        handler_params: param_types
            .iter()
            .copied()
            .filter(|t| t.is_handler(&ir.ir))
            .collect(),
        generics: sorted,
    };

    if let Some((reg_args, block, loc)) = reg_args {
        reg_args.extend(procident.handlers.iter().filter_map(|&idx| {
            ir.get_or_implicit(ir.handlers[idx].effect, scope, block, loc)
                .unwrap()
                .non_global()
                .cloned()
        }));
    }

    // get proc
    if !ir.proc_map.contains_key(&procident) {
        Either::Left(gen_handler_proc(
            ir,
            procident,
            def,
            &param_types,
            output,
            generics,
            proc_todo,
        ))
    } else {
        ir.proc_map[&procident]
    }
}

fn gen_handler_proc(
    ir: &mut IRCtx<'_>,
    procident: ProcIdent,
    def: Option<ExprIdx>,
    param_types: &[TypeIdx],
    output: TypeIdx,
    generics: Rc<ResolvedGenerics>,
    proc_todo: &mut ProcTodo,
) -> ProcIdx {
    let (handler_idx, eff_fun_idx) = procident.fun.unwrap_right();

    if ir.linker.is_some_and(|(_, idx)| handler_idx == idx) {
        // link_effect definition
        let eff = match ir.ir.types[output] {
            Type::HandlerOutput(eff, _) => eff,
            _ => unreachable!(),
        };
        let foreign = ir.foreign[&eff];
        let output = ir.insert_type(Type::NakedHandler(foreign));

        let input = ir.next_reg(TYPE_STR_SLICE);
        let proc_idx = ir.ir.proc_sign.push(
            ProcIdx,
            ProcSign {
                inputs: vec![input],
                captures: None,
                output,
                debug_name: "link_effect".into(),
                unhandled: Vec::new(),
                handled: Vec::new(),
                redirect: Vec::new(),
            },
        );

        // use len_fun as the body (also unreachable)
        let len_fun = get_function(ir.parsed, ir.parsed.preamble, "len");
        proc_todo.push(ProcCtx {
            proc_idx,
            expr: len_fun.body,
            inside_handler: None,
            scope: Scope {
                parent: None,
                values: HashMap::new(),
                generics,
            },
            handler_defs: Rc::new([]),
        });
        ir.proc_map.insert(procident, Either::Left(proc_idx));

        return proc_idx;
    }

    let handler = match &ir.parsed.exprs[def.unwrap()].0 {
        Expression::Handler(handler) => handler,
        _ => unreachable!(),
    };

    let eff_val = ir.handlers[handler_idx].effect;
    let effect = match ir.asys.defs[eff_val] {
        Definition::Effect(idx) => &ir.parsed.effects[idx],
        _ => unreachable!(),
    };

    let val = ir.asys.values[effect.functions[eff_fun_idx].name];
    let (decl, body) = handler
        .functions(effect)
        .find(|(decl, _)| ir.asys.values[decl.name] == val)
        .unwrap();

    // get params
    let params = decl
        .sign
        .inputs
        .values()
        .map(|param| ir.asys.values[param.name])
        .zip(param_types.iter().copied())
        .map(|(a, b)| (a, b, false))
        .collect::<Vec<_>>();

    // generate debug name
    let eff_name = ir.parsed.idents[effect.name].0.as_str();
    let proc_name = ir.parsed.idents[effect.functions[eff_fun_idx].name]
        .0
        .as_str();
    let mut debug_name = format!("{}.{}.{}", proc_name, eff_name, usize::from(handler_idx));

    let handlers = &procident.handlers;
    if !handlers.is_empty() {
        debug_name += ".";

        for &handler in handlers.iter() {
            let eff_val = ir.handlers[handler].effect;
            let eff_name = ir
                .parsed
                .effects
                .values()
                .find(|e| ir.asys.values[e.name] == eff_val)
                .map(|e| ir.parsed.idents[e.name].0.as_str())
                .unwrap_or("debug");

            debug_name += eff_name;
            debug_name += ".";
            debug_name += usize::from(handler).to_string().as_str();
            debug_name += ".";
        }

        debug_name.pop();
    }

    // generate handler proc
    let output = match ir.asys.types[ir.asys.exprs[body]] {
        analyzer::Type::Never => TYPE_NEVER,
        _ => output,
    };

    generate_proc_sign(
        ir,
        Some(procident.fun),
        Cow::Owned(procident.handlers),
        &[],
        &params,
        output,
        generics,
        debug_name,
        body,
        Some(handler_idx),
        proc_todo,
    )
}

fn generate_proc_sign(
    ir: &mut IRCtx,
    ident: Option<Either<Val, (HandlerIdx, EffFunIdx)>>,
    unhandled: Cow<[HandlerIdx]>,
    handled: &[HandlerIdx],
    params: &[(Val, TypeIdx, bool)],
    output: TypeIdx,
    generics: Rc<ResolvedGenerics>,
    debug_name: String,
    body: ExprIdx,
    inside_handler: Option<HandlerIdx>,
    proc_todo: &mut ProcTodo,
) -> ProcIdx {
    // get inputs
    let mut inputs = Vec::new();
    let mut scope = Scope {
        parent: None,
        values: HashMap::new(),
        generics,
    };
    for (val, ty, reference) in params.iter().copied() {
        let reg = ir.next_reg(ty);
        if reference {
            scope.insert(val, Value::Reference(reg));
        } else {
            scope.insert(val, Value::Reg(reg, Some(val)));
        }
        inputs.push(reg);
    }

    for idx in unhandled.iter().copied().chain(handled.iter().copied()) {
        let handler = &ir.handlers[idx];
        let global = handler.global;
        let effect = handler.effect;

        match global {
            Some(glob) => {
                scope.insert(effect, Value::Global(glob));
            }
            None => {
                let ty = ir.insert_type(Type::Handler(idx));
                let reg = ir.next_reg(ty);
                inputs.push(reg);
                scope.insert(effect, Value::Reg(reg, None));
            }
        }
    }

    let captures = if let Some(idx) = inside_handler {
        let handler = &ir.handlers[idx];
        let global = handler.global;
        let effect = handler.effect;

        let mut members = Vec::new();
        for (val, ty, reference) in handler.captures.iter().copied() {
            scope.insert(
                val,
                if reference {
                    let reg = ir.ir.regs.push(Reg, ty);
                    members.push(reg);
                    Value::Reference(reg)
                } else {
                    let reg = ir.ir.regs.push(Reg, ty);
                    members.push(reg);
                    Value::Reg(reg, None)
                },
            );
        }

        Some(Captures {
            input: match global {
                Some(glob) => {
                    scope.insert(effect, Value::Global(glob));
                    Value::Global(glob)
                }
                None => {
                    let ty = ir.insert_type(Type::Handler(idx));
                    let reg = ir.next_reg(ty);
                    inputs.push(reg);
                    scope.insert(effect, Value::Reg(reg, None));
                    Value::Reg(reg, None)
                }
            },
            members,
        })
    } else {
        None
    };

    // create signature
    let proc_idx = ir.ir.proc_sign.push(
        ProcIdx,
        ProcSign {
            inputs,
            output,
            debug_name,
            captures,
            unhandled: inside_handler
                .iter()
                .copied()
                .filter(|_| ir.parsed.yeets(body))
                .collect(),
            handled: handled
                .iter()
                .copied()
                .filter(|&h| !ir.ir.handler_type[h].break_ty.is_never())
                .collect(),
            redirect: Vec::new(),
        },
    );
    let todo_idx = proc_todo.len();
    proc_todo.push(ProcCtx {
        proc_idx,
        expr: body,
        inside_handler,
        scope: Scope {
            parent: None,
            values: scope.values.clone(),
            generics: Rc::clone(&scope.generics),
        },
        handler_defs: Rc::new([]),
    });

    // add procident if this is a function
    if let Some(fun) = ident {
        let mut sorted = scope
            .generics
            .iter()
            .map(|(&k, &v)| (k, v))
            .collect::<Vec<_>>();
        sorted.sort_unstable_by_key(|v| v.0 .0);
        let sorted = sorted.into_iter().map(|(_, v)| v).collect::<Vec<_>>();

        ir.proc_map.insert(
            ProcIdent {
                fun,
                handlers: unhandled.into_owned(),
                handler_params: params
                    .iter()
                    .copied()
                    .filter_map(|(_, t, _)| if t.is_handler(&ir.ir) { Some(t) } else { None })
                    .collect(),
                generics: sorted,
            },
            Either::Left(proc_idx),
        );
    }

    // create handlers
    let mut handler_defs = Vec::new();
    ir.parsed.for_each(body, false, false, &mut |expr| {
        match ir.parsed.exprs[expr].0 {
            Expression::Handler(_) => {
                // get break type
                let (eff_val, break_type) = match ir.asys.types[ir.asys.exprs[expr]] {
                    analyzer::Type::Handler(e, t, _) => {
                        (e, TypeIdx::from_type(ir, t, &scope.generics))
                    }
                    _ => unreachable!(),
                };

                // create handler
                let handler =
                    ir.new_handler(&handler_defs, eff_val, false, break_type, expr, &scope);

                handler_defs.push((expr, Some(handler)));
            }
            Expression::Call(fun, ref exprs) => {
                if !matches!(
                    ir.asys.types[ir.asys.exprs[expr]],
                    analyzer::Type::Handler(_, _, _)
                ) {
                    return;
                }

                // get function
                let fun = match ir.asys.types[ir.asys.exprs[fun]] {
                    analyzer::Type::FunctionLiteral(fun) => fun,
                    _ => unreachable!(),
                };

                // get handler
                let param_types = exprs
                    .iter()
                    .copied()
                    .map(|expr| match ir.asys.types[ir.asys.exprs[expr]] {
                        analyzer::Type::Handler(effect, _, def) => {
                            // recursive call!
                            handler_type(ir, effect, def, proc_idx, &handler_defs, &scope)
                        }
                        _ => TypeIdx::from_type(ir, ir.asys.exprs[expr], &scope.generics),
                    })
                    .collect();

                // recursive call!
                let (eff, fail) = match ir.asys.types[ir.asys.exprs[expr]] {
                    analyzer::Type::Handler(eff, fail, _) => {
                        (eff, TypeIdx::from_type(ir, fail, &scope.generics))
                    }
                    _ => unreachable!(),
                };
                let ty = ir.insert_type(Type::HandlerOutput(eff, fail));

                let proc = get_proc(ir, fun, proc_idx, &scope, param_types, ty, None, proc_todo);
                let output = match proc {
                    Either::Left(idx) => ir.ir.proc_sign[idx].output,
                    Either::Right(idx) => ir.ir.proc_foreign[idx].output,
                };
                match ir.ir.types[output] {
                    Type::NakedHandler(handler)
                    | Type::RawHandler(handler, _)
                    | Type::Handler(handler) => handler_defs.push((expr, Some(handler))),
                    Type::Never => handler_defs.push((expr, None)),
                    _ => unreachable!("{:?}", ir.ir.types[output]),
                }
            }
            _ => (),
        }
    });

    // set handler information
    if let analyzer::Type::Handler(effect, _, def) = ir.asys.types[ir.asys.exprs[body]] {
        let handler = handler_type(ir, effect, def, proc_idx, &handler_defs, &scope);
        ir.ir.proc_sign[proc_idx].output = handler;
    }
    proc_todo[todo_idx].handler_defs = handler_defs.into();

    // output
    proc_idx
}

fn handler_type(
    ir: &mut IRCtx,
    effect: Val,
    def: Option<analyzer::HandlerIdx>,
    proc_idx: ProcIdx,
    defs: &[(ExprIdx, Option<HandlerIdx>)],
    scope: &Scope,
) -> TypeIdx {
    match ir.asys.handlers[def.expect("function return handler type not filled in")] {
        analyzer::HandlerDef::Handler(expr, _) => {
            let Some(handler_idx) = defs
                .iter()
                .find(|&&(e, _)| expr == e)
                .unwrap_or_else(|| {
                    panic!(
                        "function {} returns handler not defined by self",
                        ir.ir.proc_sign[proc_idx].debug_name
                    )
                })
                .1
            else {
                return TYPE_NEVER;
            };
            let mems = ir.handlers[handler_idx]
                .captures
                .iter()
                .copied()
                .enumerate()
                .filter_map(|(i, (val, _, reference))| {
                    // it is a reference at was not given as a parameter
                    if reference && scope.get(val).is_none() {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect::<Rc<_>>();
            if mems.is_empty() {
                ir.insert_type(Type::NakedHandler(handler_idx))
            } else {
                ir.insert_type(Type::RawHandler(handler_idx, mems))
            }
        }
        analyzer::HandlerDef::Call(expr) => {
            let Some(handler_idx) = defs
                .iter()
                .find(|&&(e, _)| expr == e)
                .unwrap_or_else(|| {
                    panic!(
                        "function {} returns handler not defined by self",
                        ir.ir.proc_sign[proc_idx].debug_name
                    )
                })
                .1
            else {
                return TYPE_NEVER;
            };
            ir.insert_type(Type::NakedHandler(handler_idx))
        }
        analyzer::HandlerDef::Param(p) => {
            ir.ir.regs[ir.ir.proc_sign[proc_idx].inputs[usize::from(p)]]
        }
        analyzer::HandlerDef::Signature => ir
            .get_or_implicit(
                effect,
                scope,
                &mut Block::default(),
                Ranged((), 0, 0, FileIdx(0)),
            )
            .expect("effect not in scope when finding naked handler")
            .get_type(&ir.ir),
        analyzer::HandlerDef::Error => unreachable!(),
    }
}

fn generate_proc_impl(ir: &mut IRCtx, mut ctx: ProcCtx, proc_todo: &mut ProcTodo) -> ProcImpl {
    let mut blocks = VecMap::new();
    let start = blocks.push(BlockIdx, Block::default());

    let mut end = start;
    let ret = generate_expr(ir, &mut ctx, &mut blocks, &mut end, proc_todo);

    if let Ok(ret) = ret {
        if !matches!(
            blocks[end].instructions.last(),
            Some(Instruction::Return(_) | Instruction::Yeet(_, _))
        ) {
            // add return if we haven't already
            let ret = ret.map(|ret| {
                let r = ret.value(ir, &mut blocks[end]);
                let output = ir.ir.proc_sign[ctx.proc_idx].output;

                // create raw handler if required
                if let Type::RawHandler(_, _) = ir.ir.types[output] {
                    let raw = ir.next_reg(output);
                    blocks[end]
                        .instructions
                        .push(Instruction::RawHandler(raw, r));
                    raw
                } else {
                    r
                }
            });
            blocks[end].instructions.push(Instruction::Return(ret));
        }
    }

    ProcImpl { blocks }
}

#[derive(Clone, Copy)]
struct Never;
type ExprResult = Result<Option<Value>, Never>;

fn get_captures(
    ir: &mut IRCtx,
    scope: &mut Scope,
    block: &mut Block,
    expr: ExprIdx,
    exception: Option<Val>,
) -> Vec<(Val, Reg, bool)> {
    let mut captures = Vec::new();
    ir.parsed.for_each(expr, true, true, &mut |expr| {
        if let Expression::Ident(i) | Expression::Member(_, i) = ir.parsed.exprs[expr].0 {
            let val = ir.asys.values[i];

            // capture effects from (effect) functions
            let vals = match ir.asys.defs[val] {
                Definition::EffectFunction(eff_idx, eff_fun_idx, _) => {
                    let eff_val = ir.asys.values[ir.parsed.effects[eff_idx].name];
                    let iter = ir.parsed.effects[eff_idx].functions[eff_fun_idx]
                        .sign
                        .effects
                        .iter()
                        .filter_map(|i| {
                            let effect = ir.asys.values[i.ident.ident];
                            if Some(effect) == exception {
                                None
                            } else {
                                Some((effect, false))
                            }
                        });

                    if Some(eff_val) == exception {
                        iter.collect()
                    } else {
                        std::iter::once((eff_val, false)).chain(iter).collect()
                    }
                }
                Definition::Function(fun, _) => ir.parsed.functions[fun]
                    .decl
                    .sign
                    .effects
                    .iter()
                    .filter_map(|i| {
                        let effect = ir.asys.values[i.ident.ident];
                        if Some(effect) == exception {
                            None
                        } else {
                            Some((effect, false))
                        }
                    })
                    .collect(),
                Definition::Parameter(mutable, _, _) => {
                    if Some(val) == exception {
                        vec![]
                    } else {
                        vec![(val, mutable)]
                    }
                }
                Definition::Variable(mutable, _, _) => {
                    if Some(val) == exception {
                        vec![]
                    } else {
                        vec![(val, mutable)]
                    }
                }
                Definition::Effect(_) => {
                    if Some(val) == exception {
                        vec![]
                    } else {
                        vec![(val, false)]
                    }
                }
                Definition::BuiltinType(_) => vec![],
                Definition::Package(_) => vec![],
                Definition::Generic(_) => vec![],
            };

            // capture vals
            for (val, mutable) in vals {
                if let Some(e) = scope.get(val).cloned() {
                    if !captures.iter().any(|&(v, _, _)| v == val) {
                        if mutable {
                            let reg = e.reference(ir, scope, block);
                            captures.push((val, reg, true));
                        } else {
                            let reg = e.value(ir, block);
                            captures.push((val, reg, false));
                        }
                    }
                }
            }
        }
    });
    captures
}

fn generate_expr(
    ir: &mut IRCtx,
    ctx: &mut ProcCtx,
    blocks: &mut VecMap<BlockIdx, Block>,
    block: &mut BlockIdx,
    proc_todo: &mut ProcTodo,
) -> ExprResult {
    use Expression as E;
    match ir.parsed.exprs[ctx.expr].0 {
        E::Body(ref body) => {
            for &expr in body.main.iter() {
                generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo)?;
            }
            body.last
                .map(|expr| generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo))
                .unwrap_or(Ok(None))
        }
        E::Let(_, name, _, expr) => {
            let val = ir.asys.values[name];
            let reg = generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo)?
                .expect("let value does not return a value")
                .value(ir, &mut blocks[*block]);
            ctx.scope.insert(val, Value::Reg(reg, Some(val)));
            Ok(None)
        }
        E::Call(func, ref args) => {
            let range = ir.parsed.exprs[ctx.expr].empty();
            let output = ir.asys.exprs[ctx.expr];
            let output = TypeIdx::from_return_type(ir, output, &ctx.scope.generics);

            // get base registers
            let mut reg_args = args
                .iter()
                .map(|&expr| {
                    generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo)
                        .map(|r| r.expect("call argument does not return a value"))
                })
                .collect::<Result<Vec<_>, _>>()?;

            // TODO: currently we assume func is an Ident expr or Effect Member expr
            let res = match ir.parsed.exprs[func].0 {
                E::Member(handler, id) => {
                    let val = ir.asys.values[id];
                    match ir.asys.types[ir.asys.exprs[handler]] {
                        analyzer::Type::PackageLiteral(_) => {
                            // function of package
                            let proc_idx = get_proc(
                                ir,
                                val,
                                ctx.proc_idx,
                                &ctx.scope,
                                reg_args.iter().map(|r| r.get_type(&ir.ir)).collect(),
                                output,
                                Some((&mut reg_args, &mut blocks[*block], range)),
                                proc_todo,
                            );

                            let out = match proc_idx {
                                Either::Left(idx) => ir.ir.proc_sign[idx].output,
                                Either::Right(idx) => ir.ir.proc_foreign[idx].output,
                            };
                            let output = out.into_result(ir);

                            // execute function
                            let collect = reg_args
                                .into_iter()
                                .map(|r| r.value(ir, &mut blocks[*block]))
                                .collect::<Vec<_>>();

                            match proc_idx {
                                Either::Left(idx) => {
                                    let is_linker = ir.linker.is_some_and(|(eff_val, idx)| {
                                        let effect = match ir.asys.defs[eff_val] {
                                            Definition::Effect(idx) => &ir.parsed.effects[idx],
                                            _ => unreachable!(),
                                        };
                                        ir.asys.values[effect.functions[EffFunIdx(0)].name] == val
                                            && ctx.scope.get(eff_val).is_some_and(|v| {
                                                v.get_type(&ir.ir).is_handler_of(&ir.ir, idx)
                                            })
                                    });
                                    if is_linker {
                                        // get library name
                                        match ir.parsed.exprs[args[0]].0 {
                                            E::String(ref lib) => ir.ir.links.insert(lib.clone()),
                                            _ => unreachable!("not a constant string"),
                                        };

                                        // create handler
                                        if let Some(output) =
                                            output.clone().unwrap_or(None).map(|v| v.register())
                                        {
                                            blocks[*block]
                                                .instructions
                                                .push(Instruction::Handler(output, vec![]));
                                        }
                                    } else if val == ir.len {
                                        // get len
                                        if let Some(output) =
                                            output.clone().unwrap_or(None).map(|v| v.register())
                                        {
                                            blocks[*block]
                                                .instructions
                                                .push(Instruction::Member(output, collect[0], 1));
                                        }
                                    } else {
                                        blocks[*block].instructions.push(Instruction::Call(
                                            idx,
                                            output.clone().unwrap_or(None).map(|v| v.register()),
                                            collect,
                                        ));
                                    }
                                }
                                Either::Right(idx) => {
                                    blocks[*block].instructions.push(Instruction::CallForeign(
                                        idx,
                                        output.clone().unwrap_or(None).map(|v| v.register()),
                                        collect,
                                    ));
                                }
                            }

                            if out.is_never() {
                                blocks[*block].instructions.push(Instruction::Unreachable);
                            }
                            output
                        }
                        _ => todo!(),
                    }
                }
                E::Ident(id) => {
                    // function of current package
                    let val = ir.asys.values[id];
                    let proc_idx = get_proc(
                        ir,
                        val,
                        ctx.proc_idx,
                        &ctx.scope,
                        reg_args.iter().map(|r| r.get_type(&ir.ir)).collect(),
                        output,
                        Some((&mut reg_args, &mut blocks[*block], range)),
                        proc_todo,
                    );

                    let out = match proc_idx {
                        Either::Left(idx) => ir.ir.proc_sign[idx].output,
                        Either::Right(idx) => ir.ir.proc_foreign[idx].output,
                    };
                    let output = out.into_result(ir);

                    // execute function
                    let collect = reg_args
                        .into_iter()
                        .map(|r| r.value(ir, &mut blocks[*block]))
                        .collect::<Vec<_>>();

                    match proc_idx {
                        Either::Left(idx) => {
                            let is_linker = ir.linker.is_some_and(|(eff_val, idx)| {
                                let effect = match ir.asys.defs[eff_val] {
                                    Definition::Effect(idx) => &ir.parsed.effects[idx],
                                    _ => unreachable!(),
                                };
                                ir.asys.values[effect.functions[EffFunIdx(0)].name] == val
                                    && ctx.scope.get(eff_val).is_some_and(|v| {
                                        v.get_type(&ir.ir).is_handler_of(&ir.ir, idx)
                                    })
                            });
                            if is_linker {
                                // get library name
                                match ir.parsed.exprs[args[0]].0 {
                                    E::String(ref lib) => ir.ir.links.insert(lib.clone()),
                                    _ => unreachable!("not a constant string"),
                                };

                                // create handler
                                if let Some(output) =
                                    output.clone().unwrap_or(None).map(|v| v.register())
                                {
                                    blocks[*block]
                                        .instructions
                                        .push(Instruction::Handler(output, vec![]));
                                }
                            } else if val == ir.len {
                                // get len
                                if let Some(output) =
                                    output.clone().unwrap_or(None).map(|v| v.register())
                                {
                                    blocks[*block]
                                        .instructions
                                        .push(Instruction::Member(output, collect[0], 1));
                                }
                            } else {
                                blocks[*block].instructions.push(Instruction::Call(
                                    idx,
                                    output.clone().unwrap_or(None).map(|v| v.register()),
                                    collect,
                                ));
                            }
                        }
                        Either::Right(idx) => {
                            blocks[*block].instructions.push(Instruction::CallForeign(
                                idx,
                                output.clone().unwrap_or(None).map(|v| v.register()),
                                collect,
                            ));
                        }
                    }

                    if out.is_never() {
                        blocks[*block].instructions.push(Instruction::Unreachable);
                    }
                    output
                }
                _ => todo!(),
            };

            if let Ok(Some(Value::Reg(r, _))) = res {
                if let Type::RawHandler(idx, _) = ir.ir.types[ir.ir.regs[r]] {
                    let ty = ir.insert_type(Type::NakedHandler(idx));
                    let unraw = ir.next_reg(ty);
                    blocks[*block]
                        .instructions
                        .push(Instruction::UnrawHandler(unraw, r));
                    Ok(Some(Value::Reg(unraw, None)))
                } else {
                    res
                }
            } else {
                res
            }
        }
        E::Member(_, _) => todo!(),
        E::Loop(expr) => {
            let loop_init = blocks.push(BlockIdx, Block::default());
            let loop_start = blocks.push(BlockIdx, Block::default());
            let mut loop_end = loop_start;

            let mut phis = HashMap::new();
            let mut values = HashMap::new();
            let mut optscope = Some(&ctx.scope);
            while let Some(scope) = optscope {
                values.extend(
                    scope
                        .values
                        .iter()
                        .filter_map(|(&val, value)| match *value {
                            Value::Reg(r, o) => {
                                let copy = ir.copy_reg(r);
                                phis.insert(val, (r, Value::Reg(copy, o)));
                                Some((val, Value::Reg(copy, o)))
                            }
                            Value::Reference(r) => {
                                let copy = ir.copy_reg(r);
                                phis.insert(val, (r, Value::Reference(copy)));
                                Some((val, Value::Reference(copy)))
                            }
                            Value::Global(_) => None,
                        }),
                );
                optscope = scope.parent;
            }

            let mut parent = Scope {
                parent: Some(&ctx.scope),
                values,
                generics: Rc::clone(&ctx.scope.generics),
            };
            let mut child = ProcCtx {
                proc_idx: ctx.proc_idx,
                expr,
                inside_handler: ctx.inside_handler,
                scope: Scope {
                    parent: Some(&parent),
                    values: HashMap::new(),
                    generics: Rc::clone(&parent.generics),
                },
                handler_defs: Rc::clone(&ctx.handler_defs),
            };
            let _ = generate_expr(ir, &mut child, blocks, &mut loop_end, proc_todo);

            blocks[*block].next = Some(loop_init);
            blocks[loop_init].next = Some(loop_start);
            blocks[loop_end].next = Some(loop_init);

            // add phi instructions for changed values
            for (r, value) in child.scope.values.into_iter() {
                if let Some((original, copy)) = phis.remove(&r) {
                    match copy {
                        Value::Reg(copy, _) => {
                            let new = value.value(ir, &mut blocks[loop_end]);
                            blocks[loop_init].instructions.push(Instruction::Phi(
                                copy,
                                vec![(original, *block), (new, loop_end)],
                            ));
                        }
                        Value::Reference(copy) => {
                            let new = value.reference(ir, &mut parent, &mut blocks[loop_end]);
                            blocks[loop_init].instructions.push(Instruction::Phi(
                                copy,
                                vec![(original, *block), (new, loop_end)],
                            ));
                        }
                        Value::Global(_) => unreachable!(),
                    }
                }
            }

            // remaining are just copies
            for (original, copy) in phis.into_values() {
                match copy {
                    Value::Reg(copy, _) => {
                        blocks[loop_init]
                            .instructions
                            .push(Instruction::Copy(copy, original));
                    }
                    Value::Reference(copy) => {
                        blocks[loop_init]
                            .instructions
                            .push(Instruction::Copy(copy, original));
                    }
                    Value::Global(_) => unreachable!(),
                }
            }

            Err(Never)
        }
        E::IfElse(cond, yes, no) => {
            let cond = generate_expr(ir, ctx.with_expr(cond), blocks, block, proc_todo)?
                .expect("condition has no value")
                .value(ir, &mut blocks[*block]);

            match no {
                Some(no) => {
                    let no_start = blocks.push(BlockIdx, Block::default());

                    let mut no_end = no_start;
                    let (no_changed, no_reg) = ctx.child(no, |child| {
                        generate_expr(ir, child, blocks, &mut no_end, proc_todo)
                    });

                    let yes_start = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::Branch(cond, yes_start, no_start));

                    let mut yes_end = yes_start;
                    let (yes_changed, yes_reg) = ctx.child(yes, |child| {
                        generate_expr(ir, child, blocks, &mut yes_end, proc_todo)
                    });

                    let end = blocks.push(BlockIdx, Block::default());

                    blocks[*block].next = Some(no_start);
                    blocks[yes_end].next = Some(end);
                    blocks[no_end].next = Some(end);

                    // add phi instructions for changed values
                    generate_phi(
                        ir,
                        blocks,
                        end,
                        &mut ctx.scope,
                        &[
                            Path {
                                changed: yes_changed,
                                block_end: yes_end,
                            },
                            Path {
                                changed: no_changed,
                                block_end: no_end,
                            },
                        ],
                    );
                    *block = end;

                    match (yes_reg, no_reg) {
                        (Ok(Some(yes)), Ok(Some(no))) => {
                            let yes = yes.value(ir, &mut blocks[yes_end]);
                            let no = no.value(ir, &mut blocks[no_end]);
                            if ir.ir.regs[yes] == ir.ir.regs[no] {
                                let out = ir.copy_reg(yes);
                                blocks[*block].instructions.push(Instruction::Phi(
                                    out,
                                    vec![(yes, yes_end), (no, no_end)],
                                ));
                                Ok(Some(Value::Reg(out, None)))
                            } else {
                                Ok(None)
                            }
                        }
                        (Err(Never), Err(Never)) => Err(Never),
                        (Err(Never), Ok(Some(no))) => Ok(Some(no)),
                        (Ok(Some(yes)), Err(Never)) => Ok(Some(yes)),
                        _ => Ok(None),
                    }
                }
                None => {
                    let yes_start = blocks.push(BlockIdx, Block::default());
                    let end = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::Branch(cond, yes_start, end));

                    let mut yes_end = yes_start;
                    let (yes_changed, _) = ctx.child(yes, |child| {
                        generate_expr(ir, child, blocks, &mut yes_end, proc_todo)
                    });

                    blocks[*block].next = Some(end);
                    blocks[yes_end].next = Some(end);

                    // add phi instructions for changed values
                    generate_phi(
                        ir,
                        blocks,
                        end,
                        &mut ctx.scope,
                        &[
                            Path {
                                changed: yes_changed,
                                block_end: yes_end,
                            },
                            Path {
                                changed: HashMap::new(),
                                block_end: *block,
                            },
                        ],
                    );
                    *block = end;

                    Ok(None)
                }
            }
        }
        E::UnOp(uexpr, op) => match op {
            UnOp::PostIncrement => {
                let left = generate_expr(ir, ctx.with_expr(uexpr), blocks, block, proc_todo)?
                    .expect("operand has no value");

                let value = left.value(ir, &mut blocks[*block]);
                let one = ir.copy_reg(value);
                let incremented = ir.copy_reg(value);
                blocks[*block].instructions.push(Instruction::Init(one, 1));
                blocks[*block]
                    .instructions
                    .push(Instruction::Add(incremented, value, one));

                match left {
                    Value::Reg(_, val) => {
                        ctx.scope.insert(
                            val.expect("left operand not tied to variable"),
                            Value::Reg(incremented, val),
                        );
                    }
                    Value::Reference(ptr) => {
                        blocks[*block]
                            .instructions
                            .push(Instruction::Store(ptr, incremented));
                    }
                    Value::Global(_) => unreachable!(),
                }

                Ok(Some(Value::Reg(value, None)))
            }
            UnOp::Reference => {
                let ty = TypeIdx::from_expr(ir, ctx.expr);
                let ty = TypeIdx::from_type(ir, ty, &ctx.scope.generics);

                let right = generate_expr(ir, ctx.with_expr(uexpr), blocks, block, proc_todo)?
                    .expect("operand has no value");
                let right = right.reference(ir, &mut ctx.scope, &mut blocks[*block]);
                let right = Value::Reg(right, None).cast(ir, &mut blocks[*block], ty);

                Ok(Some(right))
            }
            UnOp::Cast => {
                let ty = TypeIdx::from_expr(ir, ctx.expr);
                let ty = TypeIdx::from_type(ir, ty, &ctx.scope.generics);

                let right = generate_expr(ir, ctx.with_expr(uexpr), blocks, block, proc_todo)?
                    .expect("operand has no value");
                let right = right.cast(ir, &mut blocks[*block], ty);

                Ok(Some(right))
            }
        },
        E::BinOp(left, op, right) => match op {
            BinOp::Assign => {
                let left = generate_expr(ir, ctx.with_expr(left), blocks, block, proc_todo)?
                    .expect("left operand has no value");

                let right = generate_expr(ir, ctx.with_expr(right), blocks, block, proc_todo)?
                    .expect("right operand has no value")
                    .value(ir, &mut blocks[*block]);

                match left {
                    Value::Reg(_, val) => {
                        ctx.scope.insert(
                            val.expect("left operand not tied to variable"),
                            Value::Reg(right, val),
                        );
                    }
                    Value::Reference(ptr) => {
                        blocks[*block]
                            .instructions
                            .push(Instruction::Store(ptr, right));
                    }
                    Value::Global(_) => unreachable!(),
                }
                Ok(None)
            }
            BinOp::Index => {
                let array = generate_expr(ir, ctx.with_expr(left), blocks, block, proc_todo)?
                    .expect("left operand has no value");

                match ir.parsed.exprs[right].0 {
                    E::BinOp(left, BinOp::Range, right) => {
                        // get range
                        let left =
                            generate_expr(ir, ctx.with_expr(left), blocks, block, proc_todo)?
                                .expect("range left has no value")
                                .value(ir, &mut blocks[*block]);

                        let right =
                            generate_expr(ir, ctx.with_expr(right), blocks, block, proc_todo)?
                                .expect("range right has no value")
                                .value(ir, &mut blocks[*block]);

                        // get array pointer
                        let adjacent = match ir.ir.types[array.get_type(&ir.ir)] {
                            Type::Pointer(_) => {
                                let ptr = array.value(ir, &mut blocks[*block]);

                                let adjacent = ir.copy_reg(ptr);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::AdjacentPtr(adjacent, ptr, left));

                                adjacent
                            }
                            Type::ConstArray(_, elem_ty) => {
                                let ptr = array.reference(ir, &mut ctx.scope, &mut blocks[*block]);

                                let adjacent_ty = ir.insert_type(Type::Pointer(elem_ty));
                                let adjacent = ir.next_reg(adjacent_ty);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::ElementPtr(adjacent, ptr, left));

                                adjacent
                            }
                            Type::Slice(elem_ty) => {
                                let slice = array.value(ir, &mut blocks[*block]);

                                let ptr_ty = ir.insert_type(Type::Pointer(elem_ty));
                                let ptr = ir.next_reg(ptr_ty);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::Member(ptr, slice, 0));

                                let adjacent = ir.copy_reg(ptr);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::AdjacentPtr(adjacent, ptr, left));

                                adjacent
                            }
                            _ => unreachable!(),
                        };

                        // get slice length
                        let len = ir.copy_reg(left);
                        blocks[*block]
                            .instructions
                            .push(Instruction::Sub(len, right, left));

                        // create slice
                        let elem_ty = ir.ir.regs[adjacent].inner(&ir.ir);
                        let slice_ty = ir.insert_type(Type::Slice(elem_ty));
                        let slice = ir.next_reg(slice_ty);
                        blocks[*block]
                            .instructions
                            .push(Instruction::Aggregate(slice, vec![adjacent, len]));

                        Ok(Some(Value::Reg(slice, None)))
                    }
                    _ => {
                        let right =
                            generate_expr(ir, ctx.with_expr(right), blocks, block, proc_todo)?
                                .expect("right operand has no value")
                                .value(ir, &mut blocks[*block]);

                        match ir.ir.types[array.get_type(&ir.ir)] {
                            Type::Pointer(_) => {
                                let ptr = array.value(ir, &mut blocks[*block]);
                                let adjacent = ir.copy_reg(ptr);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::AdjacentPtr(adjacent, ptr, right));
                                Ok(Some(Value::Reference(adjacent)))
                            }
                            Type::ConstArray(_, elem_ty) => {
                                let ptr = array.reference(ir, &mut ctx.scope, &mut blocks[*block]);
                                let elem_ptr_ty = ir.insert_type(Type::Pointer(elem_ty));
                                let elem_ptr = ir.next_reg(elem_ptr_ty);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::ElementPtr(elem_ptr, ptr, right));
                                Ok(Some(Value::Reference(elem_ptr)))
                            }
                            Type::Slice(elem_ty) => {
                                let slice = array.value(ir, &mut blocks[*block]);

                                let ptr_ty = ir.insert_type(Type::Pointer(elem_ty));
                                let ptr = ir.next_reg(ptr_ty);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::Member(ptr, slice, 0));

                                let adjacent = ir.copy_reg(ptr);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::AdjacentPtr(adjacent, ptr, right));
                                Ok(Some(Value::Reference(adjacent)))
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }
            _ => {
                let left = generate_expr(ir, ctx.with_expr(left), blocks, block, proc_todo)?
                    .expect("left operand has no value")
                    .value(ir, &mut blocks[*block]);

                let right = generate_expr(ir, ctx.with_expr(right), blocks, block, proc_todo)?
                    .expect("right operand has no value")
                    .value(ir, &mut blocks[*block]);

                let out = ir.next_reg(match op {
                    BinOp::Equals | BinOp::Less | BinOp::Greater => TYPE_BOOL,
                    BinOp::Divide | BinOp::Multiply | BinOp::Subtract | BinOp::Add => {
                        ir.ir.regs[left]
                    }
                    BinOp::Range => unreachable!(),
                    BinOp::Assign | BinOp::Index => unreachable!(),
                });

                let instr = match op {
                    BinOp::Equals => Instruction::Equals(out, left, right),
                    BinOp::Divide => Instruction::Div(out, left, right),
                    BinOp::Multiply => Instruction::Mul(out, left, right),
                    BinOp::Subtract => Instruction::Sub(out, left, right),
                    BinOp::Add => Instruction::Add(out, left, right),
                    BinOp::Less => Instruction::Less(out, left, right),
                    BinOp::Greater => Instruction::Greater(out, left, right),
                    BinOp::Range => unreachable!(),
                    BinOp::Assign | BinOp::Index => unreachable!(),
                };
                blocks[*block].instructions.push(instr);

                Ok(Some(Value::Reg(out, None)))
            }
        },
        E::Yeet(value) => {
            // get break value
            let reg = value
                .map(|expr| generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo))
                .unwrap_or(Ok(None))?;

            // TODO: we assume this is top level inside a handler
            let yeet = reg.map(|v| v.value(ir, &mut blocks[*block]));
            blocks[*block]
                .instructions
                .push(Instruction::Yeet(yeet, ctx.inside_handler.unwrap()));

            // break returns any type
            Err(Never)
        }
        E::Handler(_) => {
            // get handler
            let Some(handler_idx) = ctx
                .handler_defs
                .iter()
                .find(|&&(e, _)| ctx.expr == e)
                .expect("handler not generated beforehand")
                .1
            else {
                return Err(Never);
            };
            let handler = &ir.handlers[handler_idx];
            let captures = handler
                .definition
                .map(|def| match ir.asys.types[ir.asys.exprs[def]] {
                    analyzer::Type::Handler(_, _, def) => match def.map(|h| &ir.asys.handlers[h]) {
                        Some(analyzer::HandlerDef::Handler(_, captures)) => captures
                            .iter()
                            .map(|c| {
                                let reg = ctx
                                    .scope
                                    .get(c.val)
                                    .expect("handler capture not in scope")
                                    .clone();
                                if c.mutable {
                                    reg.reference(ir, &mut ctx.scope, &mut blocks[*block])
                                } else {
                                    reg.value(ir, &mut blocks[*block])
                                }
                            })
                            .collect(),
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                })
                .unwrap_or(Vec::new());

            // create handler closure
            let ty = ir.insert_type(Type::NakedHandler(handler_idx));
            let closure_reg = ir.next_reg(ty);

            blocks[*block]
                .instructions
                .push(Instruction::Handler(closure_reg, captures));

            Ok(Some(Value::Reg(closure_reg, None)))
        }
        E::TryWith(body, handler) => {
            if let Some(handler) = handler {
                // get handler
                let closure_reg =
                    generate_expr(ir, ctx.with_expr(handler), blocks, block, proc_todo)?
                        .expect("try handler does not return a value");
                let ty = &ir.ir.types[closure_reg.get_type(&ir.ir)];
                let handler_idx = match ty {
                    &Type::NakedHandler(handler_idx) | &Type::Handler(handler_idx) => handler_idx,
                    _ => panic!(),
                };
                let naked = matches!(ty, Type::NakedHandler(_));
                let eff_val = ir.handlers[handler_idx].effect;
                let global = ir.handlers[handler_idx].global;

                // generate reset
                let reset_captures =
                    get_captures(ir, &mut ctx.scope, &mut blocks[*block], body, Some(eff_val));
                let reset_params = reset_captures
                    .iter()
                    .map(|&(v, r, m)| (v, ir.ir.regs[r], m))
                    .collect::<Vec<_>>();

                // add handler to handler list
                let proc_sign = &ir.ir.proc_sign[ctx.proc_idx];
                let debug_name = format!(
                    "{}__reset.{}",
                    proc_sign.debug_name,
                    usize::from(handler_idx)
                );

                let handlers = &[handler_idx];
                let (unhandled, handled): (Cow<[HandlerIdx]>, &[HandlerIdx]) = if naked {
                    (Cow::Borrowed(&[]), handlers)
                } else {
                    (Cow::Borrowed(handlers), &[])
                };

                let output = TypeIdx::from_expr(ir, body);
                let output = TypeIdx::from_return_type(ir, output, &ctx.scope.generics);
                let proc_idx = generate_proc_sign(
                    ir,
                    None,
                    unhandled,
                    handled,
                    &reset_params,
                    output,
                    Rc::clone(&ctx.scope.generics),
                    debug_name,
                    body,
                    None,
                    proc_todo,
                );

                let input_regs: Vec<Reg> = reset_captures.into_iter().map(|(_, r, _)| r).collect();

                // execute proc
                let output = ir.ir.proc_sign[proc_idx].output.into_result(ir);

                match global {
                    Some(glob) => {
                        let next = blocks.push(BlockIdx, Block::default());

                        let v = closure_reg.value(ir, &mut blocks[*block]);
                        blocks[*block]
                            .instructions
                            .push(Instruction::SetScopedGlobal(glob, v, next));

                        blocks[*block].instructions.push(Instruction::Call(
                            proc_idx,
                            output.clone().unwrap_or(None).map(|v| v.register()),
                            input_regs,
                        ));

                        blocks[*block].next = Some(next);
                        *block = next;
                    }
                    None => {
                        let mut input_regs = input_regs;
                        input_regs.push(closure_reg.value(ir, &mut blocks[*block]));

                        blocks[*block].instructions.push(Instruction::Call(
                            proc_idx,
                            output.clone().unwrap_or(None).map(|v| v.register()),
                            input_regs,
                        ));
                    }
                }

                if ir.ir.proc_sign[proc_idx].output.is_never() {
                    blocks[*block].instructions.push(Instruction::Unreachable);
                }
                Ok(output.unwrap_or_default())
            } else {
                // generate reset
                let reset_captures =
                    get_captures(ir, &mut ctx.scope, &mut blocks[*block], body, None);
                let reset_params = reset_captures
                    .iter()
                    .copied()
                    .map(|(v, r, m)| (v, ir.ir.regs[r], m))
                    .collect::<Vec<_>>();

                // add handler to handler list
                let proc_sign = &ir.ir.proc_sign[ctx.proc_idx];
                let debug_name = format!("{}__reset", proc_sign.debug_name);

                let output = TypeIdx::from_expr(ir, body);
                let output = TypeIdx::from_return_type(ir, output, &ctx.scope.generics);
                let proc_idx = generate_proc_sign(
                    ir,
                    None,
                    Cow::Borrowed(&[]),
                    &[],
                    &reset_params,
                    output,
                    Rc::clone(&ctx.scope.generics),
                    debug_name,
                    body,
                    None,
                    proc_todo,
                );

                let input_regs: Vec<Reg> = reset_captures.into_iter().map(|(_, r, _)| r).collect();

                // execute proc
                let output = ir.ir.proc_sign[proc_idx].output.into_result(ir);

                blocks[*block].instructions.push(Instruction::Call(
                    proc_idx,
                    output.clone().unwrap_or(None).map(|v| v.register()),
                    input_regs,
                ));
                Ok(output.unwrap_or_default())
            }
        }
        E::String(ref s) => {
            let reg = ir.next_reg(TYPE_STR_SLICE);

            blocks[*block]
                .instructions
                .push(Instruction::InitString(reg, s.clone()));

            Ok(Some(Value::Reg(reg, None)))
        }
        E::Character(ref s) => {
            let ty = TypeIdx::from_expr(ir, ctx.expr);
            let ty = TypeIdx::from_type(ir, ty, &ctx.scope.generics);
            let reg = ir.next_reg(ty);

            match ir.ir.types[ty] {
                Type::Int8 => {
                    let byte = s.bytes().next().unwrap();
                    blocks[*block]
                        .instructions
                        .push(Instruction::Init(reg, byte as u64));
                }
                _ => unreachable!(),
            }

            Ok(Some(Value::Reg(reg, None)))
        }

        E::Int(i) => {
            let ty = TypeIdx::from_expr(ir, ctx.expr);
            if ir.asys.types[ty].is_int() {
                let ty = TypeIdx::from_type(ir, ty, &ctx.scope.generics);
                let reg = ir.next_reg(ty);

                blocks[*block].instructions.push(Instruction::Init(reg, i));

                Ok(Some(Value::Reg(reg, None)))
            } else {
                // zero init
                let ty = TypeIdx::from_type(ir, ty, &ctx.scope.generics);
                let reg = ir.next_reg(ty);

                blocks[*block].instructions.push(Instruction::Zeroinit(reg));

                Ok(Some(Value::Reg(reg, None)))
            }
        }

        E::Array(ref exprs) => {
            let ty = TypeIdx::from_expr(ir, ctx.expr);
            let ty = TypeIdx::from_type(ir, ty, &ctx.scope.generics);

            let regs = exprs
                .iter()
                .copied()
                .map(|expr| {
                    let opt = generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo)?;
                    match opt {
                        Some(val) => Ok(val.value(ir, &mut blocks[*block])),
                        None => {
                            let reg = ir.next_reg(TYPE_NONE);
                            blocks[*block].instructions.push(Instruction::Uninit(reg));
                            Ok(reg)
                        }
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;

            match ir.ir.types[ty] {
                Type::ConstArray(_, _) => {
                    let array = ir.next_reg(ty);
                    blocks[*block]
                        .instructions
                        .push(Instruction::Aggregate(array, regs));

                    Ok(Some(Value::Reg(array, None)))
                }
                Type::Slice(elem_ty) => {
                    let array_len = regs.len() as u64;
                    let array_ty = ir.insert_type(Type::ConstArray(array_len, elem_ty));
                    let array = ir.next_reg(array_ty);
                    blocks[*block]
                        .instructions
                        .push(Instruction::Aggregate(array, regs));

                    let ptr =
                        Value::Reg(array, None).reference(ir, &mut ctx.scope, &mut blocks[*block]);

                    let len_ty = ir.insert_type(Type::IntSize);
                    let len = ir.next_reg(len_ty);
                    blocks[*block]
                        .instructions
                        .push(Instruction::Init(len, array_len));

                    let slice = ir.next_reg(ty);
                    blocks[*block]
                        .instructions
                        .push(Instruction::Aggregate(slice, vec![ptr, len]));

                    Ok(Some(Value::Reg(slice, None)))
                }
                _ => unreachable!(),
            }
        }

        E::Ident(id) => {
            let val = ir.asys.values[id];
            let mut reg = ir
                .get_or_implicit(
                    val,
                    &ctx.scope,
                    &mut blocks[*block],
                    ir.parsed.exprs[ctx.expr].empty(),
                )
                .unwrap_or_else(|| {
                    panic!(
                        "value '{}' not in scope in {}",
                        ir.parsed.idents[id].0, ir.ir.proc_sign[ctx.proc_idx].debug_name
                    )
                });
            if let Type::Handler(idx) = ir.ir.types[reg.get_type(&ir.ir)] {
                if let analyzer::Type::Handler(_, _, Some(def)) =
                    ir.asys.types[ir.asys.exprs[ctx.expr]]
                {
                    if matches!(ir.asys.handlers[def], analyzer::HandlerDef::Signature)
                        && !ir.ir.handler_type[idx].break_ty.is_never()
                    {
                        // we clone the handler if we got it from the signature
                        // this is so the cloned handler will always be attached to the same try block
                        // no need to clone if the handler never breaks, this is only for correcting breaks
                        let cloned = ir.handlers[idx].clone();
                        let cloned = ir.handlers.push(HandlerIdx, cloned);
                        let ty = ir.ir.handler_type[idx].clone();
                        ir.ir.handler_type.push_value(ty);

                        let ty = ir.insert_type(Type::Handler(cloned));
                        reg = reg.cast(ir, &mut blocks[*block], ty);

                        // add redirect to current proc
                        let proc = &mut ir.ir.proc_sign[ctx.proc_idx];
                        if proc.handled.contains(&idx) {
                            proc.handled.push(cloned);
                        } else {
                            proc.redirect.push((cloned, idx));
                        }
                    }
                }
            }
            Ok(Some(reg))
        }
        E::Uninit => {
            let ty = TypeIdx::from_expr(ir, ctx.expr);
            let ty = TypeIdx::from_type(ir, ty, &ctx.scope.generics);
            let reg = ir.next_reg(ty);
            blocks[*block].instructions.push(Instruction::Uninit(reg));
            Ok(Some(Value::Reg(reg, None)))
        }
        E::Error => unreachable!(),
    }
}

struct Path {
    changed: HashMap<Val, Value>,
    block_end: BlockIdx,
}

fn generate_phi(
    ir: &mut IRCtx,
    blocks: &mut VecMap<BlockIdx, Block>,
    block: BlockIdx,
    scope: &mut Scope,
    paths: &[Path],
) {
    let mut keys = HashSet::<Val>::new();
    for path in paths.iter() {
        keys.extend(path.changed.keys());
    }

    for val in keys.into_iter() {
        let values = paths
            .iter()
            .map(|path| match path.changed.get(&val) {
                Some(v) => v,
                None => scope.get(val).unwrap(),
            })
            .collect::<Vec<_>>();

        if values.iter().all(|v| matches!(v, Value::Reg(_, _))) {
            let regs = values
                .into_iter()
                .zip(paths.iter().map(|p| p.block_end))
                .map(|(v, e)| (v.value(ir, &mut blocks[e]), e))
                .collect::<Vec<_>>();
            let new = ir.copy_reg(regs[0].0);
            blocks[block].instructions.push(Instruction::Phi(new, regs));
            scope.insert(val, Value::Reg(new, Some(val)))
        } else {
            let regs = values
                .into_iter()
                .zip(paths.iter().map(|p| p.block_end))
                .map(|(v, e)| (v.reference(ir, &mut Scope::default(), &mut blocks[e]), e))
                .collect::<Vec<_>>();
            let new = ir.copy_reg(regs[0].0);
            blocks[block].instructions.push(Instruction::Phi(new, regs));
            scope.insert(val, Value::Reference(new))
        }
    }
}
