use std::collections::HashMap;

use parcelr::parcelr;

type Members<'a> = HashMap<&'a str, Value<'a>>;
type Values<'a> = Vec<Value<'a>>;

struct BracketL();
struct BracketR();
struct BraceL();
struct BraceR();
struct Colon();
struct Comma();

type String<'a> = &'a str;
type Number = f64;
type Boolean = bool;

parcelr! {

    struct Json<'a>(Value<'a>);

    enum Value<'a> {
        Object(Object<'a>),
        Array(Array<'a>),
        String(String<'a>),
        Number(Number),
        Boolean(Boolean),
    }

    // { members }
    struct Object<'a>(BraceL, Members<'a>, BraceR);

    // [ values ]
    struct Array<'a>(BracketL, Values<'a>, BracketR);

    // { }
    fn object_empty(l: BraceL, r: BraceR) -> Object<'static> {
        Object(l, HashMap::new(), r)
    }

    // [ ]
    fn array_empty(l: BracketL, r: BracketR) -> Array<'static> {
        Array(l, Vec::new(), r)
    }

    // str : value
    fn members_single<'a>(key: String<'a>, _: Colon, value: Value<'a>) -> Members<'a> {
        HashMap::from([(key, value)])
    }

    // members , str : value
    fn members_join<'a>(mut left: Members<'a>, _: Comma, key: String<'a>, _: Colon, value: Value<'a>) -> Members<'a> {
        left.insert(key, value);
        left
    }

    // value
    fn values_single<'a>(value: Value<'a>) -> Values<'a> {
        vec![value]
    }

    // values , value
    fn values_join<'a>(mut left: Values<'a>, _: Comma, value: Value<'a>) -> Values<'a> {
        left.push(value);
        left
    }

}

fn main() {
    println!("Hello, world!");
}
