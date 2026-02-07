use std::collections::HashMap;
use std::ops::Index;
use std::sync::{Arc, OnceLock};

use compact_str::{CompactString, ToCompactString};

use crate::type_table::{Effect, FunctionSignature, Kind, Term, Type, TypeTable};

pub mod display;

#[derive(Default, Debug)]
pub struct IR {
    handlers: Vec<OnceLock<HandlerBodyDefinition>>,
    structs: Vec<OnceLock<StructDefinition>>,
    effects: Vec<OnceLock<EffectDefinition>>,
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
    pub fn push_handler_body(&mut self) -> HandlerBody {
        let idx = self.handlers.len() as u32;
        self.handlers.push(OnceLock::new());
        HandlerBody(idx)
    }
    pub fn push_struct(&mut self) -> StructDef {
        let idx = self.structs.len() as u32;
        self.structs.push(OnceLock::new());
        StructDef(idx)
    }
    pub fn push_effect(&mut self) -> EffectDef {
        let idx = self.effects.len() as u32;
        self.effects.push(OnceLock::new());
        EffectDef(idx)
    }
    pub fn realize_handler_body(&self, handler: HandlerBody, value: HandlerBodyDefinition) {
        self.handlers[handler.0 as usize]
            .set(value)
            .expect("ICE: handler already realized")
    }
    pub fn realize_struct(&self, struc: StructDef, value: StructDefinition) {
        self.structs[struc.0 as usize]
            .set(value)
            .expect("ICE: struct already realized");
    }
    pub fn realize_effect(&self, effect: EffectDef, value: EffectDefinition) {
        self.effects[effect.0 as usize]
            .set(value)
            .expect("ICE: effect already realized")
    }
}

impl Index<HandlerBody> for IR {
    type Output = HandlerBodyDefinition;

    fn index(&self, index: HandlerBody) -> &Self::Output {
        self.handlers[index.0 as usize]
            .get()
            .expect("ICE: handler not yet realized")
    }
}

impl Index<StructDef> for IR {
    type Output = StructDefinition;

    fn index(&self, index: StructDef) -> &Self::Output {
        self.structs[index.0 as usize]
            .get()
            .expect("ICE: struct not yet realized")
    }
}

impl Index<EffectDef> for IR {
    type Output = EffectDefinition;

    fn index(&self, index: EffectDef) -> &Self::Output {
        self.effects[index.0 as usize]
            .get()
            .expect("ICE: effect not yet realized")
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct HandlerBody(u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct StructDef(u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct EffectDef(u32);

#[derive(Debug)]
pub struct HandlerBodyDefinition {
    /// Corresponds 1-1 with effect members
    pub members: Vec<HandlerMember>,
}

#[derive(Debug)]
pub struct StructDefinition {
    pub members: Vec<StructMember>,
}

#[derive(Debug)]
pub struct EffectDefinition {
    pub members: Vec<EffectMember>,
}

#[derive(Debug, Clone, Copy)]
pub enum ItemDef {
    Alias(Kind, Term),
    Struct(Kind, StructDef),
    Effect(Kind, EffectDef),
    Function(FunctionSignature, Option<Effect>),
}

impl ItemDef {
    pub fn resolve<'a>(self, ir: &'a IR) -> ItemDefinition<'a> {
        match self {
            ItemDef::Alias(kind, term) => ItemDefinition::Alias(kind, term),
            ItemDef::Struct(kind, struct_def) => ItemDefinition::Struct(kind, &ir[struct_def]),
            ItemDef::Effect(kind, effect_def) => ItemDefinition::Effect(kind, &ir[effect_def]),
            ItemDef::Function(function_signature, parent) => {
                ItemDefinition::Function(function_signature, parent)
            }
        }
    }
}

#[derive(Debug)]
pub enum ItemDefinition<'a> {
    Alias(Kind, Term),
    Struct(Kind, &'a StructDefinition),
    Effect(Kind, &'a EffectDefinition),
    Function(FunctionSignature, Option<Effect>),
}

#[derive(Debug, Clone)]
pub struct HandlerDef {
    pub type_params: Option<Arc<[Kind]>>,
    pub implicit_regions: usize,

    pub effect: Effect,
    pub with_effect: Effect,
    pub body: HandlerBody,
}

#[derive(Debug, Clone)]
pub struct EffectMember {
    pub name: CompactString,
    pub signature: FunctionSignature,
}

#[derive(Debug)]
pub struct HandlerMember {
    pub name: CompactString,
    pub signature: FunctionSignature,
}

#[derive(Debug)]
pub struct StructMember {
    pub name: CompactString,
    pub ty: Type,
}
