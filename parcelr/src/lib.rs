extern crate proc_macro;
use std::{collections::{HashMap, HashSet, BTreeMap, btree_map::Entry}, fmt, hash::Hash};

use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{Item, parse_macro_input, parse::{Parse, ParseStream}, ReturnType, Type, FnArg, Fields, Generics, ItemEnum, ItemStruct, Error};

type Symbols = HashMap<String, TokenStream>;
type SymbolSet<'a> = HashSet<&'a str>;
type SymbolMap<'a> = HashMap<&'a str, SymbolSet<'a>>;

type ItemSet<'a> = BTreeMap<ParseItem<'a>, SymbolSet<'a>>;

#[derive(Clone, Copy)]
enum Decision<'a> {
    Shift(usize), // state index in grammar
    Reduce(&'a Rule),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
struct ParseItem<'a> {
    rule: &'a Rule,
    index: usize,
}

impl PartialEq for &Rule {
    fn eq(&self, other: &&Rule) -> bool {
        std::ptr::eq(*self, *other)
    }
}

impl PartialOrd for &Rule {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (*self as *const Rule).partial_cmp(&(*other as *const Rule))
    }
}

impl Ord for &Rule {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (*self as *const Rule).cmp(&(*other as *const Rule))
    }
}

impl Eq for &Rule {}

impl Hash for &Rule {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (*self as *const Rule).hash(state);
    }
}

type State<'a> = HashMap<&'a str, Decision<'a>>;
struct Grammar<'a>(Vec<State<'a>>);

struct Rule {
    error_spot: Span,
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

fn insert<K, V>(map: &mut HashMap<K, HashSet<V>>, key: K, value: V) -> bool
where K: Eq + Hash, V: Eq + Hash {
    match map.entry(key) {
        std::collections::hash_map::Entry::Occupied(mut e) => e.get_mut().insert(value),
        std::collections::hash_map::Entry::Vacant(e) => e.insert(HashSet::new()).insert(value),
    }
}

fn extend_hash<K, V>(map: &mut HashMap<K, HashSet<V>>, key: K, value: HashSet<V>) -> bool
where K: Eq + Hash, V: Eq + Hash + Copy {
    match map.entry(key) {
        std::collections::hash_map::Entry::Occupied(mut e) => {
            if e.get().is_superset(&value) {
                false
            } else {
                e.get_mut().extend(value);
                true
            }
        }
        std::collections::hash_map::Entry::Vacant(e) => {
            e.insert(value);
            true
        }
    }
}

fn extend<K, V>(map: &mut BTreeMap<K, HashSet<V>>, key: K, value: HashSet<V>) -> bool
where K: Eq + Ord, V: Eq + Hash + Copy {
    match map.entry(key) {
        Entry::Occupied(mut e) => {
            if e.get().is_superset(&value) {
                false
            } else {
                e.get_mut().extend(value);
                true
            }
        }
        Entry::Vacant(e) => {
            e.insert(value);
            true
        }
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
        for (from, to) in &routes {
            if let Some(starts) = first.get(to) {
                let clone = starts.clone();
                if extend_hash(&mut first, from, clone) {
                    repeat = true;
                }
            }
        }
    }
    
    first
}

fn predict<'a>(rules: &'a Vec<Rule>, mut set: ItemSet<'a>, first: &SymbolMap<'a>, empty: &SymbolSet<'a>) -> ItemSet<'a> {
    let mut prediction: ItemSet<'a> = ItemSet::new();

    while let Some((item, lookahead)) = set.pop_first() {
        // add or merge new items (this is what differentiates an SLR1 and LALR1 parser)
        if !extend(&mut prediction, item, lookahead.clone()) {
            continue;
        }

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
            if let Some(starts) = first.get(item.rule.rhs[i].as_str()) {
                lah.extend(starts);
            }

            if !empty.contains(item.rule.rhs[i].as_str()) { break; };
            i += 1;
        }
        if i == item.rule.rhs.len() {
            lah.extend(lookahead);
        }

        // find prediuctions
        for rule in rules.iter().filter(|rule| rule.lhs == next) {
            set.insert(ParseItem { rule, index: 0 }, lah.clone());
        }
    }

    prediction
}

fn partition<'a>(set: ItemSet<'a>) -> HashMap<&'a str, ItemSet<'a>> {
    let mut groups: HashMap<&'a str, ItemSet<'a>> = HashMap::new();

    for (item, lookahead) in set {
        let (sym, put) = if item.rule.rhs.len() > item.index {(
            item.rule.rhs[item.index].as_str(),
            ParseItem { rule: item.rule, index: item.index + 1 },
        )} else {(
            "",
            item,
        )};

        match groups.entry(sym) {
            std::collections::hash_map::Entry::Occupied(mut e) => {
                extend(e.get_mut(), put, lookahead);
            }
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(ItemSet::new()).insert(put, lookahead);
            }
        }
    }
    
    groups
}

fn grammar<'a>(rules: &'a Vec<Rule>, lexemes: &SymbolSet<'a>) -> Result<Grammar<'a>, TokenStream> {
    let mut grammar = Vec::new();

    let empty = empty_set(rules);
    let first = first_set(rules, lexemes, &empty);

    let mut start = ItemSet::new();
    start.insert(ParseItem {
        rule: &rules[0],
        index: 0,
    }, HashSet::from_iter(vec!["$"]));

    let mut processed: HashMap<Vec<ParseItem<'a>>, (ItemSet<'a>, usize)> = HashMap::new();
    let mut stack: Vec<(ItemSet<'a>, usize)> = Vec::new();

    processed.insert(start.keys().copied().collect(), (start.clone(), 0));
    stack.push((start, 0));

    grammar.push(State::new());
    while let Some((set, index)) = stack.pop() {
        let pset = predict(rules, set, &first, &empty);
        let part = partition(pset);

        for (sym, items) in part {
            if sym == "" {
                // REDUCE
                for (item, lah) in items {
                    let r = Decision::Reduce(item.rule);
                    for sym in lah {
                        if let Some(decision) = grammar[index].get(sym) {
                            match decision {
                                Decision::Shift(_)  => return Err(quote_spanned! {
                                    item.rule.error_spot => compile_error!("SHIFT/REDUCE CONFLICT");
                                }),
                                Decision::Reduce(_) => return Err(quote_spanned! {
                                    item.rule.error_spot => compile_error!("REDUCE/REDUCE CONFLICT");
                                }),
                            }
                        } else {
                            grammar[index].insert(sym, r);
                        }
                    }
                }
            } else {
                if let Some(decision) = grammar[index].get(sym) {
                    match decision {
                        Decision::Shift(_)  => {},
                        Decision::Reduce(r) => return Err(quote_spanned! {
                            r.error_spot => compile_error!("SHIFT/REDUCE CONFLICT");
                        }),
                    }
                }

                // SHIFT
                let keys: Vec<ParseItem<'a>> = items.keys().copied().collect();

                if let Some(prev) = processed.get_mut(&keys) {
                    grammar[index].insert(sym, Decision::Shift(prev.1));

                    // get unprocessed lookaheads
                    let mut new_item = ItemSet::new();

                    for (item, lah) in items {
                        let prev_lah = prev.0.get_mut(&item).unwrap();
                        let diff: SymbolSet<'a> = lah.difference(prev_lah).copied().collect();
                        if diff.is_empty() { continue; }

                        prev_lah.extend(&diff);
                        new_item.insert(item, diff);
                    }

                    if !new_item.is_empty() {
                        stack.push((new_item, prev.1));
                    }
                } else {
                    let len = grammar.len();
                    grammar[index].insert(sym, Decision::Shift(len));
                    grammar.push(State::new());

                    processed.insert(keys, (items.clone(), len));
                    stack.push((items, len));
                };
            }
        }
    }

    Ok(Grammar(grammar))
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

impl<'a> fmt::Display for Grammar<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut i = 0;
        for state in &self.0 {
            write!(f, "{}\n", i)?;
            for (sym, decision) in state {
                match decision {
                    Decision::Shift(i)  => write!(f, "  {: <10}: shift {}\n", sym, i)?,
                    Decision::Reduce(r) => write!(f, "  {: <10}: {}\n", sym, r)?,
                }
            }
            i += 1;
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
                error_spot: name.span(),
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

                match variant.fields {
                    Fields::Unnamed(fields) => {
                        let mut rhs = Vec::new();
                        for field in fields.unnamed {
                            let Some(str) = type_name(&field.ty) else { return vec![]; };
                            put_type(symbols, &str, &field.ty);
                            rhs.push(str);
                        }

                        variants.push(Rule {
                            name: quote!{ #base::#name },
                            error_spot: name.span(),
                            lhs: lhs.clone(), rhs,
                        });
                    }
                    Fields::Named(_) => {
                        return vec![];
                    }
                    Fields::Unit => {
                    }
                }
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
                error_spot: name.span(),
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
        error_spot: Span::call_site(),
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
    item.extend(enum_def.into_iter());

    // analyse grammar
    println!("RULES");
    for rule in &rules {
        println!("{}", rule);
    }
    println!();

    let empty = empty_set(&rules);
    let first = first_set(&rules, &lexemes, &empty);

    let mut items = ItemSet::new();
    items.insert(ParseItem {
        rule: &rules[0],
        index: 0,
    }, HashSet::from_iter(vec!["EOF".into()]));

    println!("EMPTY\n{:?}\n", empty);
    println!("FIRST\n{:?}\n", first);

    match grammar(&rules, &lexemes) {
        Ok(grammar) => {
            println!("GRAMMAR\n{}\n", grammar);
        }
        Err(err) => {
            let error: proc_macro::TokenStream = err.into();
            item.extend(error.into_iter());
        }
    }

    item
}