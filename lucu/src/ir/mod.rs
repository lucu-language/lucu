use std::cell::OnceCell;
use std::collections::HashMap;
use std::ops::Index;

use compact_str::{CompactString, ToCompactString};

use crate::type_table::{FunctionSignature, Kind, Term, Type, TypeTable};

pub mod display;

#[derive(Default, Debug)]
pub struct IR {
    functions: Vec<OnceCell<FunctionDefinition>>,
    structs: Vec<OnceCell<StructDefinition>>,
    effects: Vec<OnceCell<EffectDefinition>>,
    items: HashMap<CompactString, ItemDef>,
}

impl IR {
    pub fn get(&self, name: &str) -> Option<ItemDef> {
        self.items.get(name).copied()
    }
    pub fn insert(&mut self, name: &str, item: ItemDef) {
        self.items.insert(name.to_compact_string(), item);
    }
    pub fn push_function(&mut self) -> FunctionDef {
        let idx = self.functions.len();
        self.functions.push(OnceCell::new());
        FunctionDef(idx)
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
    pub fn realize_function(&self, fun: FunctionDef, value: FunctionDefinition) {
        self.functions[fun.0]
            .set(value)
            .expect("ICE: function already realized");
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

impl Index<FunctionDef> for IR {
    type Output = FunctionDefinition;

    fn index(&self, index: FunctionDef) -> &Self::Output {
        self.functions[index.0]
            .get()
            .expect("ICE: function not yet realized")
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
pub struct FunctionDef(usize);

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
pub enum FunctionDefinition {
    Expression {
        /// The amount of outer variables this function captures.
        /// Top level functions and default effect functions have a value of 0.
        captures: usize,
        body: Body,
    },
    Intrinsic(IntrinsicFunction),
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
    Function(FunctionSignature, Parent<FunctionDef>),
}

#[derive(Debug, Clone, Copy)]
pub enum Parent<T> {
    TopLevel(T),
    Effect(EffectDef),
}

#[derive(Debug)]
pub struct EffectMember {
    pub name: CompactString,
    pub signature: FunctionSignature,
}

#[derive(Debug)]
pub struct StructMember {
    pub name: CompactString,
    pub ty: Type,
}
