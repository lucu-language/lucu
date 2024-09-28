use std::collections::HashMap;
use std::iter::Iterator;
use std::num::NonZeroU32;

use string_interner::symbol::SymbolU32;

use crate::parser::Constant;
use crate::parser::Constraint;
use crate::parser::Definition;
use crate::parser::Expression;
use crate::parser::Identifier;
use crate::parser::List;
use crate::parser::NodeVariant;
use crate::parser::NodeVariant::*;
use crate::parser::Nodes;
use crate::parser::Type;
use crate::untyped_ir::Instruction;

use super::File;
use super::Reg;

macro_rules! get {
    ($left:ident, $right:ident = $node:expr => $variant:expr) => {
        let ($left, $right) = {
            let data = &$node;
            assert_eq!($node.variant, $variant);
            (data.left.unwrap().get(), data.right.unwrap().get())
        };
    };
    ($left:ident ?, $right:ident = $node:expr => $variant:expr) => {
        let ($left, $right) = {
            let data = &$node;
            assert_eq!($node.variant, $variant);
            (
                data.left.map(std::num::NonZeroU32::get),
                data.right.unwrap().get(),
            )
        };
    };
    ($left:ident, $right:ident ? = $node:expr => $variant:expr) => {
        let ($left, $right) = {
            let data = &$node;
            assert_eq!($node.variant, $variant);
            (
                data.left.unwrap().get(),
                data.right.map(std::num::NonZeroU32::get),
            )
        };
    };
    ($left:ident ?, $right:ident ? = $node:expr => $variant:expr) => {
        let ($left, $right) = {
            let data = &$node;
            assert_eq!($node.variant, $variant);
            (
                data.left.map(std::num::NonZeroU32::get),
                data.right.map(std::num::NonZeroU32::get),
            )
        };
    };
    ($left:ident = $node:expr => $variant:expr) => {
        let $left = {
            let data = &$node;
            assert_eq!($node.variant, $variant);
            data.left.unwrap().get()
        };
    };
    ($left:ident ? = $node:expr => $variant:expr) => {
        let $left = {
            let data = &$node;
            assert_eq!($node.variant, $variant);
            data.left.map(std::num::NonZeroU32::get)
        };
    };
}

struct Codegen<'a> {
    file: File,
    scope: Vec<HashMap<SymbolU32, Reg>>,
    breakable: Vec<Reg>,
    ast: &'a Nodes,
    src: &'a str,
}

fn import_name(import: &str) -> &str {
    let path = match import.split_once(':') {
        Some((lib, path)) => {
            if path.is_empty() {
                return lib;
            }
            path
        }
        None => import,
    };
    path.split('/').last().unwrap()
}

macro_rules! block {
    ($me:ident => $($s:stmt)*) => {{
        let block = $me.file.push(crate::untyped_ir::Instruction::Block);
        $me.push_scope();
        let value = { $($s)* };
        $me.pop_scope();
        $me.file.push(crate::untyped_ir::Instruction::BreakBlock { block, value: Some(value) });
        block
    }};
}
macro_rules! block_breakable {
    ($me:ident => $($s:stmt)*) => {{
        let block = $me.file.push(crate::untyped_ir::Instruction::Block);
        $me.push_scope();
        $me.breakable.push(block);
        let value = { $($s)* };
        $me.breakable.pop();
        $me.pop_scope();
        $me.file.push(crate::untyped_ir::Instruction::BreakBlock { block, value: Some(value) });
        block
    }};
}
macro_rules! list {
    (for $elem:ident in $iter:expr; $me:ident => $($s:stmt)*) => {{
        let list = $me.file.push(crate::untyped_ir::Instruction::List);
        for $elem in $iter {
            let block = $me.file.push(crate::untyped_ir::Instruction::Block);
            let value = { $($s)* };
            $me.file.push(crate::untyped_ir::Instruction::BreakBlock { block, value: Some(value) });
        }
        $me.file.push(crate::untyped_ir::Instruction::BreakList { list });
        list
    }};
}
macro_rules! wrap_block {
    ($me:ident, $expr:expr) => {
        if matches!(
            $me.ast[$expr].variant,
            crate::parser::NodeVariant::Expression(crate::parser::Expression::Block)
        ) {
            $me.block($expr, false)
        } else {
            block! { $me => $me.expression($expr) }
        }
    };
}
macro_rules! wrap_block_breakable {
    ($me:ident, $expr:expr) => {
        if matches!(
            $me.ast[$expr].variant,
            crate::parser::NodeVariant::Expression(crate::parser::Expression::Block)
        ) {
            $me.block($expr, true)
        } else {
            block_breakable! { $me => $me.expression($expr) }
        }
    };
}

impl<'a> Codegen<'a> {
    fn text(&self, node: u32) -> &'a str {
        self.ast[node].text(self.src)
    }
    fn push_scope(&mut self) {
        self.scope.push(HashMap::new());
    }
    fn pop_scope(&mut self) {
        self.scope.pop();
    }
    fn get(&self, s: &str) -> Option<Reg> {
        self.file
            .get_interned(s)
            .and_then(|s| self.scope.iter().rev().find_map(|h| h.get(&s).copied()))
    }
    fn set(&mut self, s: &str, r: Reg) {
        let sym = self.file.intern(s);
        self.scope.last_mut().unwrap().insert(sym, r);
    }
    fn lucu(&mut self, node: u32) {
        get!(imports, definitions = self.ast[node] => Lucu);

        // codegen imports
        for import in self.ast.children_rev(imports) {
            get!(string, name? = self.ast[import] => Import);

            let path = self.text(string);
            let name = name
                .map(|n| self.text(n))
                .unwrap_or_else(|| import_name(path));

            let path = self.file.intern(path);
            let reg = self.file.push(Instruction::Import { path });

            self.file.export(reg, name);
        }

        // codegen definitions
        for def in self.ast.children_rev(definitions) {
            get!(constraints?, def = self.ast[def] => ConstrainedDefinition);

            let name = match self.ast[def].variant {
                NodeVariant::List(List::ConstrainedDefinitions) => todo!("codegen 'with' block"),
                NodeVariant::Definition(Definition::Default) => {
                    return self.default(constraints, def);
                }
                NodeVariant::Definition(Definition::Effect) => {
                    self.effect_definitions(constraints, def);
                    self.ast[def].left.unwrap().get()
                }
                NodeVariant::Definition(Definition::Type) => self.ast[def].left.unwrap().get(),
                NodeVariant::Definition(Definition::Function) => {
                    let named_sig = self.ast[def].left.unwrap().get();
                    get!(name = self.ast[named_sig] => NamedSignature);
                    name
                }
                NodeVariant::Definition(Definition::Constant) => {
                    let typed_name = self.ast[def].left.unwrap().get();
                    get!(name = self.ast[typed_name] => TypedName);
                    name
                }
                _ => panic!(),
            };

            get!(ident, generics? = self.ast[name] => Name);
            let generics = generics
                .map(|g| self.ast.children_rev(g).collect::<Box<_>>())
                .unwrap_or_default();
            let constraints = constraints
                .map(|c| self.ast.children_rev(c).collect::<Box<_>>())
                .unwrap_or_default();

            let def = block! {
                self =>
                for generic in generics.iter().copied().rev() {
                    self.generic(generic);
                }
                for constraint in constraints.iter().copied().rev() {
                    self.constraint(constraint);
                }
                self.definition(def)
            };

            self.file.export(def, self.text(ident));
        }
    }
    fn default(&mut self, constraints: Option<u32>, default: u32) {
        let generic_ident = self.ast[default].left.unwrap().get();
        let defs = self.ast[default].right.map(NonZeroU32::get);

        get!(generics?, ident = self.ast[generic_ident] => GenericIdentifier);
        let generics = generics
            .map(|g| self.ast.children_rev(g).collect::<Box<_>>())
            .unwrap_or_default();
        let constraints = constraints
            .map(|c| self.ast.children_rev(c).collect::<Box<_>>())
            .unwrap_or_default();

        block! {
            self =>
            for generic in generics.iter().copied().rev() {
                self.generic(generic);
            }
            for constraint in constraints.iter().copied().rev() {
                self.constraint(constraint);
            }

            let effect = self.ident(ident)
            if let Some(_defs) = defs {
                todo!()
            } else {
                self.file.push(Instruction::Handler { effect, defs: None })
            }
        };
    }
    fn effect_definitions(&mut self, parent_constraints: Option<u32>, def: u32) {
        let Some(defs) = self.ast[def].right.map(NonZeroU32::get).filter(|&defs| {
            matches!(
                self.ast[defs].variant,
                NodeVariant::List(List::ConstrainedDefinitions)
            )
        }) else {
            return;
        };

        let name = self.ast[def].left.unwrap().get();

        get!(parent_ident, parent_generics? = self.ast[name] => Name);
        let parent_ident = self.file.intern(self.text(parent_ident));
        let parent_generics = parent_generics
            .map(|g| self.ast.children_rev(g).collect::<Box<_>>())
            .unwrap_or_default();
        let parent_constraints = parent_constraints
            .map(|c| self.ast.children_rev(c).collect::<Box<_>>())
            .unwrap_or_default();

        for def in self.ast.children_rev(defs) {
            get!(constraints?, def = self.ast[def] => ConstrainedDefinition);

            let name = match self.ast[def].variant {
                NodeVariant::List(List::ConstrainedDefinitions) => todo!("codegen 'with' block"),
                NodeVariant::Definition(Definition::Default) => continue,
                NodeVariant::Definition(Definition::Effect) => self.ast[def].left.unwrap().get(),
                NodeVariant::Definition(Definition::Type) => self.ast[def].left.unwrap().get(),
                NodeVariant::Definition(Definition::Function) => {
                    let named_sig = self.ast[def].left.unwrap().get();
                    get!(name = self.ast[named_sig] => NamedSignature);
                    name
                }
                NodeVariant::Definition(Definition::Constant) => {
                    let typed_name = self.ast[def].left.unwrap().get();
                    get!(name = self.ast[typed_name] => TypedName);
                    name
                }
                _ => panic!(),
            };

            get!(ident, generics? = self.ast[name] => Name);
            let generics = generics
                .map(|g| self.ast.children_rev(g).collect::<Box<_>>())
                .unwrap_or_default();
            let constraints = constraints
                .map(|c| self.ast.children_rev(c).collect::<Box<_>>())
                .unwrap_or_default();

            let def = block! {
                self =>

                // generics
                let mut generic_types = Vec::new()
                for parent_generic in parent_generics.iter().copied().rev() {
                    generic_types.push(self.generic(parent_generic));
                }
                for generic in generics.iter().copied().rev() {
                    self.generic(generic);
                }

                // parent effect constraint
                let mut parent = self.file.push(Instruction::Identifier { package: None, name: parent_ident })
                if !generic_types.is_empty() {
                    let list = list! {
                        for typ in generic_types;
                        self => typ
                    };
                    parent = self.file.push(Instruction::Resolve { higher: parent, args: list });
                }
                let handler = self.file.push(Instruction::Constraint { constant: parent })

                // constraints
                for parent_constraint in parent_constraints.iter().copied().rev() {
                    self.constraint(parent_constraint);
                }
                for constraint in constraints.iter().copied().rev() {
                    self.constraint(constraint);
                }

                // definition
                let def = self.definition(def)
                self.file.push(Instruction::HandlerDefinition { def, handler })
            };

            self.file.export(def, self.text(ident));
        }
    }
    fn definition(&mut self, def: u32) -> Reg {
        match self.ast[def].variant {
            NodeVariant::Definition(Definition::Effect) => {
                if let Some(defs) = self.ast[def].right.map(NonZeroU32::get) {
                    match self.ast[defs].variant {
                        NodeVariant::List(List::Constraints) => todo!(),
                        NodeVariant::List(List::ConstrainedDefinitions) => {
                            let start = self.file.push(Instruction::Block);
                            self.push_scope();

                            let names = self.ast.children_rev(defs).filter_map(|n| {
                                get!(_constraints?, def = self.ast[n] => ConstrainedDefinition);
                                Some(match self.ast[def].variant {
                                    NodeVariant::List(List::ConstrainedDefinitions) => {
                                        todo!("codegen 'with' block")
                                    }
                                    NodeVariant::Definition(Definition::Default) => None?,
                                    NodeVariant::Definition(Definition::Effect) => {
                                        self.ast[def].left.unwrap().get()
                                    }
                                    NodeVariant::Definition(Definition::Type) => {
                                        self.ast[def].left.unwrap().get()
                                    }
                                    NodeVariant::Definition(Definition::Function) => {
                                        let named_sig = self.ast[def].left.unwrap().get();
                                        get!(name = self.ast[named_sig] => NamedSignature);
                                        name
                                    }
                                    NodeVariant::Definition(Definition::Constant) => {
                                        let typed_name = self.ast[def].left.unwrap().get();
                                        get!(name = self.ast[typed_name] => TypedName);
                                        name
                                    }
                                    _ => panic!(),
                                })
                            });
                            for name in names {
                                get!(ident = self.ast[name] => Name);
                                let ident = self.text(ident);
                                let sym = self.file.intern(ident);
                                let def = self.file.push(Instruction::EffectDefinition(sym));
                                self.set(ident, def);
                            }

                            let defaults = self.ast.children_rev(defs).filter_map(|n| {
                                get!(_constraints?, def = self.ast[n] => ConstrainedDefinition);
                                if matches!(
                                    self.ast[def].variant,
                                    NodeVariant::Definition(Definition::Default)
                                ) {
                                    Some(def)
                                } else {
                                    None
                                }
                            });
                            for default in defaults {
                                let generic_ident = self.ast[default].left.unwrap().get();
                                get!(typed_names?, full_ident = self.ast[generic_ident] => GenericIdentifier);
                                assert_eq!(typed_names, None); // TODO: error
                                let ident = self.ident(full_ident);
                                self.file.push(Instruction::Constraint { constant: ident });
                            }

                            self.pop_scope();
                            self.file.push(Instruction::BreakBlock {
                                block: start,
                                value: None,
                            });

                            self.file
                                .push(Instruction::DefinitionEffect { defs: Some(start) })
                        }
                        _ => panic!(),
                    }
                } else {
                    self.file.push(Instruction::DefinitionEffect { defs: None })
                }
            }
            NodeVariant::Definition(Definition::Type) => {
                let typ = self.file.push(Instruction::Type);
                if let Some(value) = self.ast[def].right {
                    let value = self.type_(value.get());
                    self.file.push(Instruction::DefinitionConstant {
                        kind: Some(typ),
                        value: Some(value),
                    })
                } else {
                    self.file.push(Instruction::DefinitionConstant {
                        kind: Some(typ),
                        value: None,
                    })
                }
            }
            NodeVariant::Definition(Definition::Constant) => {
                let typed_name = self.ast[def].left.unwrap().get();
                let value = self.ast[def].right;

                get!(_name, typ? = self.ast[typed_name] => TypedName);

                let typ = typ.map(|typ| self.type_(typ));
                let value = value.map(|value| self.constant(value.get()));
                self.file
                    .push(Instruction::DefinitionConstant { kind: typ, value })
            }
            NodeVariant::Definition(Definition::Function) => {
                let named_sig = self.ast[def].left.unwrap().get();
                let expr = self.ast[def].right;
                get!(_name, sig = self.ast[named_sig] => NamedSignature);
                get!(params, ret? = self.ast[sig] => FunctionSignature);
                get!(params?, blocks? = self.ast[params] => FunctionParameters);

                let params = params
                    .into_iter()
                    .flat_map(|n| self.ast.children_rev(n))
                    .collect::<Box<[_]>>();
                let blocks = blocks
                    .into_iter()
                    .flat_map(|n| self.ast.children_rev(n))
                    .collect::<Box<[_]>>();

                for param in params.iter().copied().rev() {
                    match self.ast[param].variant {
                        NodeVariant::Parameter { mutable } => {
                            let ident = self.ast[param].left.unwrap().get();
                            let typ = self.ast[param].right.unwrap().get();

                            let ident = self.text(ident);
                            let typ = self.type_(typ);
                            let param = self.file.push(Instruction::Param {
                                mutable,
                                typed: typ,
                            });
                            self.set(ident, param);
                        }
                        _ => panic!(),
                    }
                }
                for block in blocks.iter().copied().rev() {
                    get!(named_sig, constraints? = self.ast[block] => BlockParameter);
                    get!(name, sig = self.ast[named_sig] => NamedSignature);
                    get!(params, ret? = self.ast[sig] => FunctionSignature);
                    get!(params?, blocks? = self.ast[params] => FunctionParameters);
                    assert_eq!(blocks, None); // TODO: error

                    get!(ident, generics? = self.ast[name] => Name);
                    let generics = generics
                        .map(|g| self.ast.children_rev(g).collect::<Box<_>>())
                        .unwrap_or_default();
                    let constraints = constraints
                        .map(|c| self.ast.children_rev(c).collect::<Box<_>>())
                        .unwrap_or_default();
                    let params = params
                        .into_iter()
                        .flat_map(|n| self.ast.children_rev(n))
                        .collect::<Box<[_]>>();

                    let def = block! {
                        self =>
                        for generic in generics.iter().copied().rev() {
                            self.generic(generic);
                        }
                        for constraint in constraints.iter().copied().rev() {
                            self.constraint(constraint);
                        }
                        for param in params.iter().copied().rev() {
                            get!(ident, typ = self.ast[param] => Parameter { mutable: false }); // TODO: error (mutable)

                            let ident = self.text(ident);
                            let typ = self.type_(typ);
                            let param = self.file.push(Instruction::Param {
                                mutable: false,
                                typed: typ,
                            });
                            self.set(ident, param);
                        }

                        let ret = ret.map(|n| self.type_(n))
                        self.file.push(Instruction::DefinitionFunction { ret, body: None })
                    };

                    let ident = self.text(ident);
                    let param = self.file.push(Instruction::BlockParam { def });
                    self.set(ident, param);
                }

                let ret = ret.map(|n| self.type_(n));
                let body = expr.map(|n| wrap_block!(self, n.get()));
                self.file
                    .push(Instruction::DefinitionFunction { ret, body })
            }
            _ => panic!(),
        }
    }
    fn generic(&mut self, typed_name: u32) -> Reg {
        get!(name, typ? = self.ast[typed_name] => TypedName);
        get!(ident, names? = self.ast[name] => Name);

        if let Some(_names) = names {
            todo!()
        }

        let kind = match typ {
            Some(typ) => self.type_(typ),
            None => self.file.push(Instruction::Type),
        };

        let ident = self.text(ident);
        let generic = self.file.push(Instruction::Generic { kind });
        self.set(ident, generic);

        generic
    }
    fn expression(&mut self, expr: u32) -> Reg {
        match self.ast[expr].variant {
            NodeVariant::Expression(e) => match e {
                Expression::TryWith => todo!(),
                Expression::If => {
                    let cond = self.ast[expr].left.unwrap().get();
                    let body = self.ast[expr].right.unwrap().get();

                    match self.ast[body].variant {
                        NodeVariant::Lambda => todo!(),
                        NodeVariant::Expression(_) => {
                            let cond = self.expression(cond);
                            let body = wrap_block!(self, body);
                            self.file.push(Instruction::If { cond, body })
                        }
                        _ => panic!(),
                    }
                }
                Expression::Else => {
                    let if_ = self.ast[expr].left.unwrap().get();
                    let body = self.ast[expr].right.unwrap().get();

                    let if_ = self.expression(if_);
                    let body = wrap_block!(self, body);
                    self.file.push(Instruction::Else { if_, body })
                }
                Expression::Loop => {
                    let body = self.ast[expr].left.unwrap().get();
                    let body = wrap_block_breakable!(self, body);
                    self.file.push(Instruction::Loop { body })
                }
                Expression::Case => todo!(),
                Expression::Break => {
                    let block = self.breakable.last().copied().unwrap(); // TODO: error
                    if let Some(value) = self.ast[expr].left {
                        let value = self.expression(value.get());
                        self.file.push(Instruction::Break {
                            block,
                            value: Some(value),
                        })
                    } else {
                        self.file.push(Instruction::Break { block, value: None })
                    }
                }
                Expression::Do => todo!(),
                Expression::Let { mutable: _mutable } => todo!(),
                Expression::Assign => todo!(),
                Expression::AssignAdd => todo!(),
                Expression::AssignSub => todo!(),
                Expression::AssignDiv => todo!(),
                Expression::AssignMul => todo!(),
                Expression::AssignMod => todo!(),
                Expression::Range => todo!(),
                Expression::Equals => todo!(),
                Expression::NotEquals => todo!(),
                Expression::Greater => todo!(),
                Expression::GreaterEquals => todo!(),
                Expression::Less => todo!(),
                Expression::LessEquals => todo!(),
                Expression::Add => todo!(),
                Expression::Sub => todo!(),
                Expression::Mul => todo!(),
                Expression::Div => todo!(),
                Expression::Mod => todo!(),
                Expression::Typed => todo!(),
                Expression::Cast => todo!(),
                Expression::Negate => todo!(),
                Expression::Plus => todo!(),
                Expression::Reference => todo!(),
                Expression::Dereference => todo!(),
                Expression::PreIncrement => todo!(),
                Expression::PreDecrement => todo!(),
                Expression::PostDecrement => todo!(),
                Expression::PostIncrement => todo!(),
                Expression::Member => todo!(),
                Expression::Index => todo!(),
                Expression::Call => {
                    let fun = self.ast[expr].left.unwrap().get();
                    let args = self.ast[expr].right.unwrap().get();

                    get!(exprs?, blocks? = self.ast[args] => Arguments);
                    let args = Iterator::chain(
                        blocks
                            .iter()
                            .copied()
                            .flat_map(|b| self.ast.children_rev(b)),
                        exprs.iter().copied().flat_map(|e| self.ast.children_rev(e)),
                    )
                    .collect::<Box<[_]>>();

                    let fun = self.expression(fun);
                    let args = list! {
                        for arg in args.iter().copied().rev();
                        self => match self.ast[arg].variant {
                            NodeVariant::Lambda => todo!(),
                            NodeVariant::Expression(_) => self.expression(arg),
                            _ => panic!(),
                        }
                    };

                    self.file.push(Instruction::Call { fun, args })
                }
                Expression::Block => self.block(expr, false),
                Expression::Path => {
                    let full_ident = self.ast[expr].left.unwrap().get();
                    self.ident(full_ident)
                }
                Expression::Array => todo!(),
                Expression::Struct => todo!(),
                Expression::Constant => {
                    let constant = self.ast[expr].left.unwrap().get();
                    self.constant(constant)
                }
            },
            _ => panic!(),
        }
    }
    fn block(&mut self, expr: u32, breakable: bool) -> Reg {
        let exprs = self.ast[expr].left.unwrap().get();
        let exprs = self.ast.children_rev(exprs).collect::<Box<[_]>>();
        if let Some(last) = exprs.first().copied() {
            if breakable {
                block_breakable! {
                    self =>
                    for expr in exprs.iter().copied().skip(1).rev() {
                        self.expression(expr);
                    }
                    self.expression(last)
                }
            } else {
                block! {
                    self =>
                    for expr in exprs.iter().copied().skip(1).rev() {
                        self.expression(expr);
                    }
                    self.expression(last)
                }
            }
        } else {
            self.file.push(Instruction::ValueUnit)
        }
    }
    fn constraint(&mut self, constraint: u32) -> Reg {
        match self.ast[constraint].variant {
            NodeVariant::Constraint(c) => match c {
                Constraint::Constant => {
                    let left = self.ast[constraint].left.unwrap().get();
                    let left = self.constant(left);
                    self.file.push(Instruction::Constraint { constant: left })
                }
                Constraint::Unify => {
                    let left = self.ast[constraint].left.unwrap().get();
                    let right = self.ast[constraint].right.unwrap().get();

                    let left = self.constant(left);
                    let right = self.constant(right);

                    let unify = self.file.push(Instruction::Unify(left, right));
                    self.file.push(Instruction::Constraint { constant: unify })
                }
            },
            _ => panic!(),
        }
    }
    fn ident(&mut self, ident: u32) -> Reg {
        match self.ast[ident].variant {
            NodeVariant::Identifier(i) => match i {
                Identifier::Identifier => {
                    let text = self.text(ident);
                    match self.get(text) {
                        Some(reg) => reg,
                        None => {
                            let name = self.file.intern(text);
                            self.file.push(Instruction::Identifier {
                                package: None,
                                name,
                            })
                        }
                    }
                }
                Identifier::PackagedIdentifier => todo!(),
                Identifier::FullIdentifier => {
                    let id = self.ast[ident].left.unwrap().get();
                    let constants = self.ast[ident].right.unwrap().get();
                    let constants = self.ast.children_rev(constants).collect::<Box<[_]>>();

                    let higher = self.ident(id);
                    let args = list! {
                        for constant in constants.iter().copied().rev();
                        self => self.constant(constant)
                    };
                    self.file.push(Instruction::Resolve { higher, args })
                }
            },
            _ => panic!(),
        }
    }
    fn type_(&mut self, typ: u32) -> Reg {
        match self.ast[typ].variant {
            NodeVariant::Type(t) => match t {
                Type::Path => {
                    let full_ident = self.ast[typ].left.unwrap().get();
                    self.ident(full_ident)
                }
                Type::Slice => {
                    let inner = self.ast[typ].left.unwrap().get();
                    let inner = self.type_(inner);
                    self.file.push(Instruction::TypeSlice(inner))
                }
                Type::Array => {
                    let size = self.ast[typ].left.unwrap().get();
                    let inner = self.ast[typ].right.unwrap().get();

                    let size = self.constant(size);
                    let inner = self.type_(inner);
                    self.file.push(Instruction::TypeArray(size, inner))
                }
                Type::Pointer { maybe: _maybe } => todo!(),
                Type::Struct => todo!(),
                Type::Typeof => todo!(),
                Type::Type => self.file.push(Instruction::Type),
                Type::Effect => self.file.push(Instruction::Effect),
                Type::Never => self.file.push(Instruction::Never),
            },
            _ => panic!(),
        }
    }
    fn constant(&mut self, constant: u32) -> Reg {
        match self.ast[constant].variant {
            NodeVariant::Constant(c) => match c {
                Constant::Path => {
                    let full_ident = self.ast[constant].left.unwrap().get();
                    self.ident(full_ident)
                }
                Constant::Type => self.type_(self.ast[constant].left.unwrap().get()),
                Constant::Sizeof => todo!(),
                Constant::Alignof => todo!(),
                Constant::Array => {
                    let constants = self.ast[constant].left.unwrap().get();
                    let children = self.ast.children_rev(constants).collect::<Box<[_]>>();
                    let list = list! {
                        for constant in children.iter().copied().rev();
                        self => self.constant(constant)
                    };
                    self.file.push(Instruction::Array { list })
                }
                Constant::Struct => todo!(),
                Constant::Case => todo!(),
                Constant::Integer => {
                    let text = self.text(constant);
                    let i: u64 = text.parse().unwrap(); // TODO: error
                    self.file.push(Instruction::Integer(i))
                }
                Constant::String => {
                    let text = self.text(constant);
                    let text = self.file.intern(text);
                    self.file.push(Instruction::String(text))
                }
                Constant::Character => todo!(),
                Constant::Zero => todo!(),
                Constant::Uninit => todo!(),
            },
            _ => panic!(),
        }
    }
}

pub fn codegen(ast: &Nodes, src: &str) -> File {
    let mut codegen = Codegen {
        file: File::new(),
        ast,
        src,
        scope: Vec::new(),
        breakable: Vec::new(),
    };
    codegen.lucu(ast.last());
    codegen.file
}
