use std::cell::OnceCell;
use std::collections::HashMap;
use std::ops::Index;

use compact_str::{CompactString, ToCompactString};

use crate::type_table::{Effect, FunctionSignature, Kind, Term, Type, TypeTable};

pub mod display;

#[derive(Default, Debug)]
pub struct IR {
    functions: Vec<OnceCell<FunctionBodyDefinition>>,
    handlers: Vec<OnceCell<HandlerBodyDefinition>>,
    structs: Vec<OnceCell<StructDefinition>>,
    effects: Vec<OnceCell<EffectDefinition>>,
    items: HashMap<CompactString, ItemDef>,
    global_handlers: Vec<HandlerDef>,
}

impl IR {
    pub fn get(&self, name: &str) -> Option<ItemDef> {
        self.items.get(name).copied()
    }
    pub fn insert(&mut self, name: &str, item: ItemDef) {
        self.items.insert(name.to_compact_string(), item);
    }
    pub fn insert_global_handler(&mut self, handler: HandlerDef) {
        self.global_handlers.push(handler);
    }
    pub fn push_function_body(&mut self) -> FunctionBody {
        let idx = self.functions.len();
        self.functions.push(OnceCell::new());
        FunctionBody(idx)
    }
    pub fn push_handler_body(&mut self) -> HandlerBody {
        let idx = self.handlers.len();
        self.handlers.push(OnceCell::new());
        HandlerBody(idx)
    }
    pub fn push_struct(&mut self) -> StructDef {
        let idx = self.structs.len();
        self.structs.push(OnceCell::new());
        StructDef(idx)
    }
    pub fn push_effect(&mut self) -> EffectDef {
        let idx = self.effects.len();
        self.effects.push(OnceCell::new());
        EffectDef(idx)
    }
    pub fn realize_function_body(&self, fun: FunctionBody, value: FunctionBodyDefinition) {
        self.functions[fun.0]
            .set(value)
            .expect("ICE: function already realized");
    }
    pub fn realize_handler_body(&self, handler: HandlerBody, value: HandlerBodyDefinition) {
        self.handlers[handler.0]
            .set(value)
            .expect("ICE: handler already realized")
    }
    pub fn realize_struct(&self, struc: StructDef, value: StructDefinition) {
        self.structs[struc.0]
            .set(value)
            .expect("ICE: struct already realized");
    }
    pub fn realize_effect(&self, effect: EffectDef, value: EffectDefinition) {
        self.effects[effect.0]
            .set(value)
            .expect("ICE: effect already realized")
    }
}

impl Index<FunctionBody> for IR {
    type Output = FunctionBodyDefinition;

    fn index(&self, index: FunctionBody) -> &Self::Output {
        self.functions[index.0]
            .get()
            .expect("ICE: function not yet realized")
    }
}

impl Index<HandlerBody> for IR {
    type Output = HandlerBodyDefinition;

    fn index(&self, index: HandlerBody) -> &Self::Output {
        self.handlers[index.0]
            .get()
            .expect("ICE: handler not yet realized")
    }
}

impl Index<StructDef> for IR {
    type Output = StructDefinition;

    fn index(&self, index: StructDef) -> &Self::Output {
        self.structs[index.0]
            .get()
            .expect("ICE: struct not yet realized")
    }
}

impl Index<EffectDef> for IR {
    type Output = EffectDefinition;

    fn index(&self, index: EffectDef) -> &Self::Output {
        self.effects[index.0]
            .get()
            .expect("ICE: effect not yet realized")
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct HandlerBody(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct FunctionBody(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct StructDef(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct EffectDef(usize);

// TODO
pub type Body = ();

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntrinsicFunction {
    // regions
    Local,
    Alloca,
    // slices
    Len,
    // Div-related functions
    Loop,
    Unfounded,
    // debug printing
    PrintStr,
}

#[derive(Debug)]
pub enum FunctionBodyDefinition {
    Expression {
        /// The amount of outer variables this function captures.
        /// Top level functions and default effect functions have a value of 0.
        captures: usize,
        body: Body,
    },
    Intrinsic(IntrinsicFunction),
}

#[derive(Debug)]
pub struct HandlerBodyDefinition {
    /// Corresponds 1-1 with effect members, None if missing
    pub members: Vec<Option<HandlerMember>>,
}

#[derive(Debug)]
pub struct StructDefinition {
    pub members: Vec<StructMember>,
}

#[derive(Debug)]
pub enum EffectDefinition {
    Body {
        members: Vec<EffectMember>,
    },
    /// Does not allow user-defined handlers
    Intrinsic,
}

#[derive(Debug, Clone, Copy)]
pub enum ItemDef {
    Alias(Kind, Term),
    Struct(Kind, StructDef),
    Effect(Kind, EffectDef),
    Function(FunctionSignature, Parent<FunctionBody>),
}

impl ItemDef {
    pub fn resolve(self, ir: &IR) -> ItemDefinition {
        match self {
            ItemDef::Alias(kind, term) => ItemDefinition::Alias(kind, term),
            ItemDef::Struct(kind, struct_def) => ItemDefinition::Struct(kind, &ir[struct_def]),
            ItemDef::Effect(kind, effect_def) => ItemDefinition::Effect(kind, &ir[effect_def]),
            ItemDef::Function(function_signature, parent) => ItemDefinition::Function(
                function_signature,
                match parent {
                    Parent::TopLevel(body) => Parent::TopLevel(&ir[body]),
                    Parent::Effect(effect) => Parent::Effect(effect),
                },
            ),
        }
    }
}

#[derive(Debug)]
pub enum ItemDefinition<'a> {
    Alias(Kind, Term),
    Struct(Kind, &'a StructDefinition),
    Effect(Kind, &'a EffectDefinition),
    Function(FunctionSignature, Parent<&'a FunctionBodyDefinition>),
}

#[derive(Clone, Copy, Debug)]
pub struct HandlerDef {
    pub kind: Kind, // should be a ... -> EFFECT kind
    pub effect: Effect,
    pub body: HandlerBody,
}

#[derive(Debug, Clone, Copy)]
pub enum Parent<T> {
    TopLevel(T),
    Effect(Effect),
}

#[derive(Debug)]
pub struct EffectMember {
    pub name: CompactString,
    pub signature: FunctionSignature,
}

#[derive(Debug)]
pub struct HandlerMember {
    pub function: FunctionBody,
}

#[derive(Debug)]
pub struct StructMember {
    pub name: CompactString,
    pub ty: Type,
}
