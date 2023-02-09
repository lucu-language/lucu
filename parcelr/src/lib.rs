extern crate proc_macro;
use std::{collections::{HashMap, HashSet, hash_map::Entry}, fmt};

use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use syn::{Item, parse_macro_input, parse::{Parse, ParseStream}, ReturnType, Type, FnArg, Fields, Generics, ItemEnum, ItemStruct};

type Symbols = HashMap<String, TokenStream>;
type SymbolSet<'a> = HashSet<&'a str>;
type SymbolMap<'a> = HashMap<&'a str, SymbolSet<'a>>;

enum Decision<'a> {
    Shift(usize), // state index in grammar
    Reduce(&'a Rule),
}

#[derive(Debug)]
struct ParseItem<'a> {
    rule: &'a Rule,
    index: usize,
    lookahead: SymbolSet<'a>,
}

type State<'a> = HashMap<&'a str, Decision<'a>>;
type Grammar<'a> = Vec<State<'a>>;

struct Rule {
    name: TokenStream,
    lhs: String,
    rhs: Vec<String>,
}

fn empty_set<'a>(rules: &'a Vec<Rule>) -> SymbolSet<'a> {
    let mut empty = SymbolSet::new();

    let mut repeat = true;
    while repeat {
        repeat = false;
        for rule in rules {
            // add rules to the set if the rhs also contains empty elements
            if !empty.contains(rule.lhs.as_str()) && rule.rhs.iter().all(|s| empty.contains(s.as_str())) {
                empty.insert(rule.lhs.as_str());
                repeat = true;
            }
        }
    }

    empty
}

fn insert<'a>(map: &mut SymbolMap<'a>, key: &'a str, value: &'a str) -> bool {
    match map.entry(key) {
        Entry::Occupied(mut e) => e.get_mut().insert(value),
        Entry::Vacant(e) => e.insert(SymbolSet::new()).insert(value),
    }
}

fn insert_from<'a>(map: &mut SymbolMap<'a>, key: &'a str, value: &'a str) -> bool {
    match map.get(value) {
        Some(set) => {
            let clone = set.clone();
            match map.entry(key) {
                Entry::Occupied(mut e) => {
                    if e.get().is_superset(&clone) {
                        false
                    } else {
                        e.get_mut().extend(clone);
                        true
                    }
                }
                Entry::Vacant(e) => {
                    e.insert(clone);
                    true
                }
            }
        }
        None => false
    }
}

fn extend_from<'a>(set: &mut SymbolSet<'a>, map: &SymbolMap<'a>, key: &'a str) {
    if let Some(val) = map.get(key) {
        set.extend(val);
    }
}

fn first_set<'a>(rules: &'a Vec<Rule>, lexemes: &SymbolSet<'a>, empty: &SymbolSet<'a>) -> SymbolMap<'a> {
    let mut first = SymbolMap::new();

    for lexeme in lexemes {
        insert(&mut first, lexeme, lexeme);
    }

    let mut routes: HashSet<(&'a str, &'a str)> = HashSet::new();
    for rule in rules {
        for symbol in &rule.rhs {
            routes.insert((rule.lhs.as_str(), symbol.as_str()));
            if !empty.contains(symbol.as_str()) { break };
        }
    }

    let mut repeat = true;
    while repeat {
        repeat = false;
        for (key, value) in &routes {
            if insert_from(&mut first, key, value) {
                repeat = true;
            }
        }
    }
    
    first
}

fn predict<'a>(rules: &'a Vec<Rule>, mut set: Vec<ParseItem<'a>>, first: &SymbolMap<'a>, empty: &SymbolSet<'a>) -> Vec<ParseItem<'a>> {
    let mut prediction: Vec<ParseItem<'a>> = Vec::new();
    for item in &set {
        // check if we are at the end
        if item.rule.rhs.len() <= item.index {
            continue;
        }

        // get next symbol
        let next = item.rule.rhs[item.index].as_str();

        // calculate lookahead
        let mut lah = SymbolSet::new();
        let mut i = item.index + 1;
        while i < item.rule.rhs.len() {
            extend_from(&mut lah, &first, item.rule.rhs[i].as_str());
            if !empty.contains(item.rule.rhs[i].as_str()) { break; };
            i += 1;
        }
        if i == item.rule.rhs.len() {
            lah.extend(&item.lookahead);
        }

        // find prediuctions
        for rule in rules.iter().filter(|rule| rule.lhs == next) {
            prediction.extend(predict(rules, vec![ParseItem {
                rule,
                index: 0,
                lookahead: lah.clone(),
            }], first, empty));
        }
    }

    // add or merge new items (this is what differentiates an SLR1 and LALR1 parser)
    for item in prediction {
        match set.iter_mut().find(|prev| std::ptr::eq(prev.rule, item.rule) && prev.index == item.index) {
            Some(prev) => prev.lookahead.extend(item.lookahead),
            None       => set.push(item),
        }
    }
    set
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

impl fmt::Debug for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
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

fn put_type(symbols: &mut Symbols, value: &String, typ: &Type) {
    if !symbols.contains_key(value) {
        symbols.insert(value.clone(), quote!{ #typ });
    }
}

fn put_enum(symbols: &mut Symbols, value: &String, typ: &ItemEnum) {
    if !symbols.contains_key(value) {
        let base = &typ.ident;
        let args = arguments(&typ.generics);
        symbols.insert(value.clone(), quote!{ #base #args });
    }
}
fn put_struct(symbols: &mut Symbols, value: &String, typ: &ItemStruct) {
    if !symbols.contains_key(value) {
        let base = &typ.ident;
        let args = arguments(&typ.generics);
        symbols.insert(value.clone(), quote!{ #base #args });
    }
}

fn arguments(g : &Generics) -> TokenStream {
    if g.lt_token.is_none() {
        quote!{}
    } else {
        let lifetimes = g.lifetimes().map(|_| quote!{ 'a, });
        quote!{ < #(#lifetimes)* > }
    }
}

fn next_rules(item: Item, symbols: &mut Symbols) -> Vec<Rule> {
    match item {
        Item::Fn(f) => {
            let ReturnType::Type(_, typ) = f.sig.output else { return vec![]; };
            let Some(lhs) = type_name(&typ)             else { return vec![]; };
            put_type(symbols, &lhs, &typ);

            let mut rhs = Vec::new();
            for param in f.sig.inputs {
                let FnArg::Typed(pat) = param           else { return vec![]; };
                let Some(str) = type_name(&pat.ty)      else { return vec![]; };
                put_type(symbols, &str, &pat.ty);
                rhs.push(str);
            }

            let name = f.sig.ident;
            vec![Rule {
                name: quote!{ #name },
                lhs, rhs,
            }]
        }
        Item::Enum(e) => {
            let base = &e.ident;
            let lhs = base.to_string();
            put_enum(symbols, &lhs, &e);

            let mut variants = Vec::new();
            for variant in e.variants {
                let name = variant.ident;
                let Fields::Unnamed(fields) = variant.fields else { return vec![]; };

                let mut rhs = Vec::new();
                for field in fields.unnamed {
                    let Some(str) = type_name(&field.ty) else { return vec![]; };
                    put_type(symbols, &str, &field.ty);
                    rhs.push(str);
                }

                variants.push(Rule {
                    name: quote!{ #base::#name },
                    lhs: lhs.clone(), rhs,
                });
            }
            variants
        }
        Item::Struct(s) => {
            let name = &s.ident;
            let lhs = name.to_string();
            put_struct(symbols, &lhs, &s);

            let Fields::Unnamed(fields) = s.fields else { return vec![]; };
            let mut rhs = Vec::new();
            for field in fields.unnamed {
                let Some(str) = type_name(&field.ty) else { return vec![]; };
                put_type(symbols, &str, &field.ty);
                rhs.push(str);
            }

            vec![Rule {
                name: quote!{ #name },
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
pub fn parcelr(mut item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let clone = item.clone();
    let Input(input) = parse_macro_input!(clone);
    let mut symbols = Symbols::new();

    // get rules
    let mut rules = Vec::new();
    for item in input {
        rules.append(&mut next_rules(item, &mut symbols))
    }

    // insert root rule
    rules.insert(0, Rule {
        name: quote!{ std::convert::identity }.into(),
        lhs: "".into(),
        rhs: vec![rules[0].lhs.clone()],
    });

    // generate lexemes
    let mut lexemes = SymbolSet::from_iter(symbols.keys().map(String::as_str));
    for rule in &rules {
        lexemes.remove(rule.lhs.as_str());
    }

    // token enum
    let tokens = symbols.iter().map(|(key, value)| {
        let ident = Ident::new(key, Span::call_site());
        quote! { #ident(#value), }
    });
    let enum_def: proc_macro::TokenStream = quote! {
        #[derive(Debug)]
        enum Token<'a> {
            #(#tokens)*
            EOF,
        }
    }.into();

    println!("RULES");
    for rule in &rules {
        println!("{}", rule);
    }
    println!();

    let empty = empty_set(&rules);
    let first = first_set(&rules, &lexemes, &empty);
    let prediction = predict(&rules, vec![ParseItem {
        rule: &rules[0],
        index: 0,
        lookahead: HashSet::from_iter(vec!["EOF".into()]),
    }], &first, &empty);
    println!("EMPTY\n{:?}\n", empty);
    println!("FIRST\n{:?}\n", first);
    println!("PREDICT\n{:?}\n", prediction);

    item.extend(enum_def.into_iter());
    item
}