package ast

Constant :: union($T: typeid) {
	T,
	Ident_Full,
}

Type_Slice :: struct {}
Type_Array :: struct {
	size: Constant(u64),
}
Type_Pointer :: struct {
	maybe: bool,
}

Type_Prefix :: union #no_nil {
	Type_Slice,
	Type_Array,
	Type_Pointer,
}

Type :: struct {
	head:   Maybe(Ident_Full),
	prefix: []Type_Prefix,
}

Kind_Type :: struct {}
Kind_Effect :: struct {}
Kind_Constant :: struct {
	typ: Type,
}
Kind_High :: struct {
	generics: []Generic_Def,
}
Kind :: union #no_nil {
	Kind_Type,
	Kind_Effect,
	Kind_Constant,
	Kind_High,
}

AnyConstant :: union #no_nil {
	string,
	u64,
	Type,
}

Generic_Def :: struct {
	name: string,
	kind: Kind,
}

Ident_Full :: struct {
	pkg:      string,
	ident:    string,
	generics: []AnyConstant,
}

Definition_Constant :: struct {
	name:     string,
	generics: []Generic_Def,
	value:    AnyConstant,
}

// TODO: make this a struct with a name and generics
// with a Definition_Value member
Definition :: union {
	Definition_Constant,
}

