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
	definition_func: Expression,
}

Definition :: struct {
	name:     string,
	generics: []string,
	sign:     Definition_Sign,
	impl:     Maybe(Definition_Impl),
}

Binary_Op :: enum {
	Assign,
	Equals,
	Less,
	Greater,
	Divide,
	Multiply,
	Subtract,
	Add,
	Index,
	Range,
}

Unary_Op :: enum {
	POST_INCREMENT,
	POST_DECREMENT,
	REFERENCE,
	CAST,
	DO,
}

Expression_Kind :: enum {
	BODY,
	LOOP,
	CALL,
	MEMBER,
	IF_ELSE,
	IF_ELSE_UNWRAP,
	BINARY_OP,
	UNARY_OP,
	BREAK,
	LET,
	AS,
	SIZE_OF,
	ALIGN_OF,
	ARRAY,
	STR,
	INT,
	IDENT,
	UNINIT,
}

Expression :: struct {
	kind: Expression_Kind,
	data: struct #raw_union {
		base:    []Expression,
		binop:   struct {
			children: []Expression,
			operator: Binary_Op,
		},
		unnop:   struct {
			children: []Expression,
			operator: Unary_Op,
		},
		member:  struct {
			children: []Expression,
			member:   string,
		},
		let:     struct {
			children: []Expression,
			name:     string,
			mutable:  bool,
		},
		as:      struct {
			children: []Expression,
			type:     Type,
		},
		sizeof:  struct {
			children: []Expression,
			type:     Type,
		},
		alignof: struct {
			children: []Expression,
			type:     Type,
		},
		str:     struct {
			children: []Expression,
			string:   string,
		},
		int:     struct {
			children: []Expression,
			int:      u64,
		},
		ident:   struct {
			children: []Expression,
			ident:    Ident_Full,
		},
	},
}

Definition_Type :: struct {}
Definition_Func :: struct {
	params: []Param,
	output: Maybe(Type),
}

