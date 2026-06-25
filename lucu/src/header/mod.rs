use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use compact_str::CompactString;
use petgraph::graph::NodeIndex;

use crate::type_table::{Effect, FunctionSignature, Kind, Term, Type};

pub mod display;

#[derive(Default, Debug)]
pub struct Header {
    items: HashMap<CompactString, ItemDecl>,
    global_handlers: Vec<HandlerDecl>,
}

impl Header {
    pub fn get(&self, name: &str) -> Option<&ItemDecl> {
        self.items.get(name)
    }
    pub fn insert(&mut self, name: CompactString, item: ItemDecl) {
        self.items.insert(name, item);
    }
    pub fn insert_global_handler(&mut self, handler: HandlerDecl) {
        self.global_handlers.push(handler);
    }
}

#[derive(Debug)]
pub struct StructDecl {
    pub members: Vec<StructMember>,
}

#[derive(Debug)]
pub struct EffectDecl {
    pub members: Vec<EffectMember>,
}

#[derive(Debug, Clone)]
pub enum ItemDecl {
    Alias(Kind, Term),
    Struct(Kind, Arc<OnceLock<StructDecl>>),
    Effect(Kind, Arc<OnceLock<EffectDecl>>),
    Function(FunctionSignature, Option<Effect>, NodeIndex),
}

#[derive(Debug, Clone)]
pub struct HandlerDecl {
    pub type_params: Option<Arc<[Kind]>>,
    pub implicit_regions: usize,

    pub effect: Effect,
    pub with_effect: Effect,
}

#[derive(Debug, Clone)]
pub struct EffectMember {
    pub name: CompactString,
    pub signature: FunctionSignature,
}

#[derive(Debug)]
pub struct StructMember {
    pub name: CompactString,
    pub ty: Type,
}
