package ast

import "core:slice"
import "core:strings"

Constant :: union($T: typeid) {
	T,
	Ident_Full,
}

clone_constant :: proc(constant: Constant($T)) -> Constant(T) {
	switch c in constant {
	case T:
		return c
	case Ident_Full:
		return clone_ident(c)
	}
	panic("unreachable")
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

clone_prefix :: proc(prefix: Type_Prefix) -> Type_Prefix {
	switch p in prefix {
	case Type_Slice:
		return p
	case Type_Array:
		return Type_Array{clone_constant(p.size)}
	case Type_Pointer:
		return p
	}
	panic("unreachable")
}

Type_Struct :: struct {
	members: []Param,
}
Type_Func :: struct {
	ctxt: []Ident_Full,
	sign: Definition_Func,
}
Type_Head :: union {
	Ident_Full,
	Type_Struct,
	Type_Func,
}

clone_struct :: proc(type: Type_Struct) -> Type_Struct {
	return {clone_slice(type.members, clone_param)}
}
clone_func :: proc(type: Type_Func) -> Type_Func {
	return {clone_slice(type.ctxt, clone_ident), clone_sign(type.sign)}
}

clone_head :: proc(type: Type_Head) -> Type_Head {
	switch t in type {
	case Ident_Full:
		return clone_ident(t)
	case Type_Struct:
		return clone_struct(t)
	case Type_Func:
		return clone_func(t)
	}
	panic("unreachable")
}

Type :: struct {
	prefix: []Type_Prefix,
	head:   Type_Head,
}

clone_type :: proc(type: Type) -> Type {
	return {clone_slice(type.prefix, clone_prefix), clone_head(type.head)}
}

Generic :: union #no_nil {
	string,
	u64,
	Type,
}

clone_generic :: proc(generic: Generic) -> Generic {
	switch g in generic {
	case string:
		return strings.clone(g)
	case u64:
		return g
	case Type:
		return clone_type(g)
	}
	panic("unreachable")
}

Ident_Full :: struct {
	pkg:      string,
	ident:    string,
	generics: []Generic,
}

clone_ptr :: proc(ptr: ^$T, clone: proc(_: T) -> T) -> ^T {
	if ptr == nil {
		return nil
	} else {
		return new_clone(clone(ptr^))
	}
}
clone_slice :: proc(slice: []$T, clone: proc(_: T) -> T) -> []T {
	ret := make([]T, len(slice))
	for i in 0 ..< len(slice) {
		ret[i] = clone(slice[i])
	}
	return ret
}

clone_ident :: proc(ident: Ident_Full) -> Ident_Full {
	return {
		strings.clone(ident.pkg),
		strings.clone(ident.ident),
		clone_slice(ident.generics, clone_generic),
	}
}

Param :: struct {
	name: string,
	type: Type,
}

clone_param :: proc(param: Param) -> Param {
	return {strings.clone(param.name), clone_type(param.type)}
}

Definition_Sign :: union #no_nil {
	Definition_Type,
	Definition_Effect,
	Definition_Const,
	Definition_Use,
	Definition_Func,
}
Definition_Impl :: struct #raw_union {
	definition_type:   Type,
	definition_effect: []Definition,
	definition_use:    Handler,
	definition_func:   Expression,
	definition_const:  Expression,
}

Handler :: union #no_nil {
	[]Definition,
	^Expression,
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
Definition_Const :: struct {
	type: Type,
}
Definition_Use :: struct {
	ident: Ident_Full,
}
Definition_Func :: struct {
	params: []Param,
	output: ^Type,
}

clone_sign :: proc(sign: Definition_Func) -> Definition_Func {
	return {clone_slice(sign.params, clone_param), clone_ptr(sign.output, clone_type)}
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
	USE_HANDLER,
}

Expression :: struct {
	kind: Expression_Kind,
	data: struct #raw_union {
		base:        []Expression,
		lambda:      struct {
			children: []Expression,
			params:   []Param,
		},
		binop:       struct {
			children: []Expression,
			operator: Binary_Op,
		},
		unnop:       struct {
			children: []Expression,
			operator: Unary_Op,
		},
		member:      struct {
			children: []Expression,
			member:   string,
		},
		let:         struct {
			children: []Expression,
			name:     string,
		},
		as:          struct {
			children: []Expression,
			type:     Type,
		},
		sizeof:      struct {
			children: []Expression,
			type:     Type,
		},
		alignof:     struct {
			children: []Expression,
			type:     Type,
		},
		str:         struct {
			children: []Expression,
			string:   string,
		},
		int:         struct {
			children: []Expression,
			int:      u64,
		},
		ident:       struct {
			children: []Expression,
			ident:    string,
		},
		use_handler: struct {
			children: []Expression,
			ident:    Ident_Full,
			handler:  Handler,
		},
	},
}

