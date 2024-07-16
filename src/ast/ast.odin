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

Type_Struct :: struct {
	members: []Param,
}
Type_Head :: union {
	Ident_Full,
	Type_Struct,
}

Type :: struct {
	prefix: []Type_Prefix,
	head:   Type_Head,
}

Generic :: union #no_nil {
	string,
	u64,
	Type,
}

Ident_Full :: struct {
	pkg:      string,
	ident:    string,
	generics: []Generic,
}

Param :: struct {
	name: string,
	type: Type,
}

Definition_Sign :: union #no_nil {
	Definition_Type,
	Definition_Func,
}
Definition_Impl :: struct #raw_union {
	definition_type: Type,
	definition_func: Body,
}

Definition :: struct {
	name:     string,
	generics: []string,
	sign:     Definition_Sign,
	impl:     Maybe(Definition_Impl),
}

Body :: struct {}

Definition_Type :: struct {}
Definition_Func :: struct {
	params: []Param,
	output: Maybe(Type),
}

