use std::collections::HashMap;
use std::iter;
use std::sync::{Arc, OnceLock};

use compact_str::CompactString;
use petgraph::graph::NodeIndex;

use crate::span::Span;
use crate::type_table::substitute::Substitute;
use crate::type_table::{
    Effect, EffectEnum, FunctionSignature, GenericArgument, Kind, Term, Type, TypeTable,
};

pub mod display;

#[derive(Default, Debug)]
pub struct Header {
    named_items: HashMap<CompactString, NamedItemDecl>,
    global_handlers: Vec<HandlerDecl>,
}

impl Header {
    pub fn get_named(&self, name: &str) -> Option<&NamedItemDecl> {
        self.named_items.get(name)
    }
    pub fn insert_named(&mut self, name: CompactString, item: NamedItemDecl) {
        self.named_items.insert(name, item);
    }
    pub fn insert_global_handler(&mut self, handler: HandlerDecl) {
        self.global_handlers.push(handler);
    }
    pub fn named_items(&self) -> impl Iterator<Item = (&str, &NamedItemDecl)> {
        self.named_items.iter().map(|(c, d)| (c.as_str(), d))
    }
    pub fn global_handlers(&self) -> impl Iterator<Item = &HandlerDecl> {
        self.global_handlers.iter()
    }
    pub fn find_global_handlers(
        &self,
        effect: Effect,
        tt: &TypeTable,
    ) -> impl Iterator<Item = (&HandlerDecl, Arc<[GenericArgument]>)> {
        self.global_handlers()
            .filter_map(move |decl| match (&tt[decl.effect], &tt[effect]) {
                (EffectEnum::Item(a), EffectEnum::Item(b))
                    if a.module == b.module && a.name == b.name =>
                {
                    let arity = decl.implicit_regions
                        + decl.type_params.as_deref().map(<[_]>::len).unwrap_or(0);
                    let mut args = iter::repeat_n(GenericArgument::Hole, arity).collect::<Box<_>>();
                    let inferred = decl.effect.infer(effect, tt, 0, &mut args);
                    let args = Arc::<[_]>::from(args);
                    // FIXME: also check if substituted with args we get the exact same effect
                    (inferred && args.clone().no_holes(tt)).then_some((decl, args))
                }
                _ => None,
            })
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
pub enum NamedItemDecl {
    Alias(Kind, Term),
    Struct(Kind, Arc<OnceLock<StructDecl>>),
    Effect(Kind, Arc<OnceLock<EffectDecl>>),
    Function(
        FunctionSignature,
        Option<Effect>,
        NodeIndex,
        FunctionDefinition,
    ),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntrinsicFunction {
    Ref,
    Alloca,
    LinkLibrary,
    Declare,
    Asm,
    AsmPure,
    Len,
    SliceFromRawParts,
    Unreachable,
    Loop,
    Unfounded,
    Trace,
    Trap,
    None,
    Some,
    ForEach,
    TryOr,
}

#[derive(Debug, Clone, Copy)]
pub enum FunctionDefinition {
    Intrinsic(IntrinsicFunction),
    Other,
}

#[derive(Debug, Clone)]
pub struct HandlerDecl {
    pub type_params: Option<Arc<[Kind]>>,
    pub implicit_regions: usize,

    pub effect: Effect,
    pub with_effect: Effect,

    pub node: NodeIndex,
}

#[derive(Debug, Clone)]
pub struct EffectMember {
    pub name: CompactString,
    pub signature: FunctionSignature,
    pub span: Span,
}

#[derive(Debug)]
pub struct StructMember {
    pub name: CompactString,
    pub ty: Type,
}
