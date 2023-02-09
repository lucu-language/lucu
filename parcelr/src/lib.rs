extern crate proc_macro;
use std::{collections::HashSet, fmt};

use proc_macro::TokenStream;
use syn::{Item, parse_macro_input, parse::{Parse, ParseStream}, ReturnType, Type, FnArg, Ident, Fields, Path, punctuated::Punctuated, PathSegment, PathArguments, parse_quote};

type Symbols = HashSet<String>;

struct Rule {
    name: Path,
    lhs: String,
    rhs: Vec<String>,
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.lhs.fmt(f)?;
        f.write_str(" ->")?;
        for s in &self.rhs {
            f.write_str(" ")?;
            s.fmt(f)?;
        }
        Ok(())
    }
}

fn type_name(typ: &Type) -> Option<String> {
    match typ {
        Type::Path(path) => {
            Some(path.path.segments.last()?.ident.to_string())
        }
        _ => None
    }
}

fn put_symbol(symbols: &mut Symbols, value: &String) {
    if !symbols.contains(value) {
        symbols.insert(value.clone());
    }
}

fn next_rules(item: Item, symbols: &mut Symbols) -> Vec<Rule> {
    match item {
        Item::Fn(f) => {
            let ReturnType::Type(_, typ) = f.sig.output else { return vec![]; };
            let Some(lhs) = type_name(&typ)             else { return vec![]; };
            put_symbol(symbols, &lhs);

            let mut rhs = Vec::new();
            for param in f.sig.inputs {
                let FnArg::Typed(pat) = param           else { return vec![]; };
                let Some(str) = type_name(&pat.ty)      else { return vec![]; };
                put_symbol(symbols, &str);
                rhs.push(str);
            }

            let name = f.sig.ident;
            vec![Rule {
                name: parse_quote!{ #name },
                lhs, rhs,
            }]
        }
        Item::Enum(e) => {
            let base = e.ident;
            let lhs = base.to_string();

            let mut variants = Vec::new();
            for variant in e.variants {
                let name = variant.ident;
                let Fields::Unnamed(fields) = variant.fields else { return vec![]; };
                put_symbol(symbols, &lhs);

                let mut rhs = Vec::new();
                for field in fields.unnamed {
                    let Some(str) = type_name(&field.ty) else { return vec![]; };
                    put_symbol(symbols, &str);
                    rhs.push(str);
                }

                variants.push(Rule {
                    name: parse_quote!{ #base::#name },
                    lhs: lhs.clone(), rhs,
                });
            }
            variants
        }
        Item::Struct(s) => {
            let name = s.ident;
            let lhs = name.to_string();
            let Fields::Unnamed(fields) = s.fields else { return vec![]; };
            put_symbol(symbols, &lhs);

            let mut rhs = Vec::new();
            for field in fields.unnamed {
                let Some(str) = type_name(&field.ty) else { return vec![]; };
                put_symbol(symbols, &str);
                rhs.push(str);
            }

            vec![Rule {
                name: parse_quote!{ #name },
                lhs, rhs,
            }]
        }
        _ => vec![]
    }
}

struct Input(Vec<Item>);

impl Parse for Input {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut items = Vec::new();
        while !input.is_empty() {
            items.push(input.parse()?);
        }
        Ok(Input(items))
    }
}

#[proc_macro]
pub fn parcelr(item: TokenStream) -> TokenStream {
    let clone = item.clone();
    let Input(input) = parse_macro_input!(clone);
    let mut symbols = HashSet::new();

    let mut rules = Vec::new();
    for item in input {
        rules.append(&mut next_rules(item, &mut symbols))
    }

    for rule in rules {
        println!("{}", rule);
    }

    item
}