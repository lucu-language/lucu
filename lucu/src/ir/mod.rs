use std::collections::HashMap;
use std::ops;
use std::sync::{Arc, RwLock};

use asta_handle_map::xar::Xar;
use compact_str::CompactString;

use crate::ast::BinOp;
use crate::header::HandlerDecl;
use crate::module::Module;
use crate::type_table::substitute::Substitute;
use crate::type_table::{
    Constant, Effect, FunctionSignature, GenericArgument, Kind, Type, TypeTable,
};

#[derive(Default)]
pub struct IR {
    pub function_map: RwLock<HashMap<(Module, CompactString), Function>>,
    pub handler_map: RwLock<HashMap<(Module, u32), Handler>>,

    pub functions: Xar<FunctionDefinition>,
    pub handlers: Xar<HandlerDefinition>,
}

impl IR {
    pub fn push_function(&self, fun: FunctionDefinition) -> Function {
        Function(self.functions.push(fun))
    }
    pub fn push_handler(&self, handler: HandlerDefinition) -> Handler {
        Handler(self.handlers.push(handler))
    }
}

impl ops::Index<Function> for IR {
    type Output = FunctionDefinition;

    fn index(&self, index: Function) -> &Self::Output {
        unsafe { self.functions.get_unchecked(index.0) }
    }
}

impl ops::Index<Handler> for IR {
    type Output = HandlerDefinition;

    fn index(&self, index: Handler) -> &Self::Output {
        unsafe { self.handlers.get_unchecked(index.0) }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Function(u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Handler(u32);

pub struct FunctionDefinition {
    pub name: CompactString,
    pub type_params: Arc<[Kind]>,
    pub sig: FunctionSignature,
    pub closure: Arc<[ClosureParameter]>,
    pub blocks: Vec<Block>,
}

pub struct HandlerDefinition {
    pub decl: HandlerDecl,
    pub closure: Arc<[ClosureParameter]>,
    pub functions: Vec<Function>,
}

impl FunctionDefinition {
    pub fn type_of(&self, reg: Reg) -> Type {
        self.blocks
            .iter()
            .flat_map(|b| b.instructions.iter())
            .nth(reg as usize)
            .unwrap()
            .0
    }
}

type Reg = u32;
type Vec<T> = Box<[T]>;

pub struct Block {
    pub instructions: Vec<(Type, Instruction)>,
    pub next: Option<u32>,
}

impl Block {
    pub fn catches_returns(&self) -> bool {
        self.instructions
            .last()
            .is_some_and(|(_, i)| matches!(i, Instruction::Perform(_)))
    }
}

#[derive(Clone, Copy)]
pub enum ClosureParameter {
    Data(Type),
    Lambda(FunctionSignature),
    /// A non-row effect
    Effect(Effect),
}

impl Substitute for ClosureParameter {
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        match self {
            ClosureParameter::Data(ty) => ClosureParameter::Data(ty.subst(tt, start, args)),
            ClosureParameter::Lambda(sig) => ClosureParameter::Lambda(sig.subst(tt, start, args)),
            ClosureParameter::Effect(effect) => {
                ClosureParameter::Effect(effect.subst(tt, start, args))
            }
        }
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        match self {
            ClosureParameter::Data(ty) => ClosureParameter::Data(ty.shift(tt, start, offset)),
            ClosureParameter::Lambda(sig) => ClosureParameter::Lambda(sig.shift(tt, start, offset)),
            ClosureParameter::Effect(effect) => {
                ClosureParameter::Effect(effect.shift(tt, start, offset))
            }
        }
    }
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
        start: usize,
        args: &mut std::vec::Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        match (self, from) {
            (ClosureParameter::Data(a), ClosureParameter::Data(b)) => a.infer(b, tt, start, args),
            (ClosureParameter::Lambda(a), ClosureParameter::Lambda(b)) => {
                a.infer(b, tt, start, args)
            }
            (ClosureParameter::Effect(a), ClosureParameter::Effect(b)) => {
                a.infer(b, tt, start, args)
            }
            _ => panic!(),
        }
    }
}

pub enum Instruction {
    // any
    Parameter(Reg),
    ClosureParameter(Reg),

    // function
    FunctionTop {
        module: Module,
        name: CompactString,
    },
    FunctionNew {
        function: Function,
        type_args: Arc<[GenericArgument]>,
        closure_args: Vec<Reg>,
    },
    FunctionHandler {
        effect: Reg,
        handler: u32,
        function: u32,
    },

    // handler
    EffectParameter(Reg),
    HandlerTop {
        module: Module,
        handler: u32,
        type_args: Arc<[GenericArgument]>,
    },
    HandlerNew {
        handler: Handler,
        type_args: Arc<[GenericArgument]>,
        closure_args: Vec<Reg>,
    },

    // data
    Local(Reg),
    Syscall {
        nr: Reg,
        args: Vec<Reg>,
    },
    BinOp {
        lhs: Reg,
        op: BinOp,
        rhs: Reg,
    },
    UnOp {
        op: BinOp,
        rhs: Reg,
    },
    Index {
        array: Reg,
        index: Reg,
    },
    IndexRange {
        array: Reg,
        from: Option<Reg>,
        to: Option<Reg>,
    },
    Constant(Constant),
    Uninit,
    Truncate(Reg),
    Extend(Reg),
    Transmute(Reg),
    If {
        condition: Reg,
        block: Reg,
    },
    Load {
        address: Reg,
    },
    Store {
        address: Reg,
        value: Reg,
    },
    Array(Vec<Reg>),
    Call {
        function: Reg,
        type_args: Arc<[GenericArgument]>,
        args: Vec<Reg>,
        effects: Vec<Reg>,
    },
    /// MUST be the last instruction of the block.
    /// Signifies that the block catches Returns.
    Perform(Reg),
    Return {
        outer: Function,
        value: Reg,
    },
}
