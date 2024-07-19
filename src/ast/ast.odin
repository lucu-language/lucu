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
	Definition_Effect,
	Definition_Use,
	Definition_Func,
}
Definition_Impl :: struct #raw_union {
	definition_type:   Type,
	definition_effect: []Definition,
	definition_use:    []Definition,
	definition_func:   Expression,
}

Definition :: struct {
	ctxt:     []Ident_Full,
	name:     string,
	generics: []string,
	sign:     Definition_Sign,
	impl:     Maybe(Definition_Impl),
}

Definition_Type :: struct {}
Definition_Effect :: struct {}
Definition_Use :: struct {
	ident: Ident_Full,
}
Definition_Func :: struct {
	params: []Param,
	output: Maybe(Type),
}

Binary_Op :: enum {
	ASSIGN,
	ADD_ASSIGN,
	MUL_ASSIGN,
	SUB_ASSIGN,
	MOD_ASSIGN,
	DIV_ASSIGN,
	EQUALS,
	NOT_EQUALS,
	LESS,
	LESS_EQUALS,
	GREATER,
	GREATER_EQUALS,
	DIVIDE,
	MULTIPLY,
	SUBTRACT,
	MODULUS,
	ADD,
	INDEX,
	RANGE,
}

Unary_Op :: enum {
	POST_INCREMENT,
	POST_DECREMENT,
	REFERENCE,
	NEGATE,
	PLUS, // no-op for numbers
	CAST,
	DO,
}

Expression_Kind :: enum {
	BODY,
	LAMBDA,
	LOOP,
	CALL,
	CALL_POINTER,
	MEMBER,
	IF_ELSE,
	IF_ELSE_UNWRAP,
	BINARY_OP,
	UNARY_OP,
	BREAK,
	LET,
	MUT,
	AS,
	SIZE_OF,
	ALIGN_OF,
	ARRAY,
	STRUCT,
	STR,
	INT,
	IDENT,
	UNINIT,
}

Expression :: struct {
	kind: Expression_Kind,
	data: struct #raw_union {
		base:    []Expression,
		lambda:  struct {
			children: []Expression,
			params:   []Param,
		},
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
			ident:    string,
		},
	},
}

