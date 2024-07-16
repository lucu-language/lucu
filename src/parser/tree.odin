package parser

import "../ast"
import "base:runtime"
import "generated"

Node :: generated.Token

into_dynamic :: proc(a: $T/[]$E) -> [dynamic]E {
	s := transmute(runtime.Raw_Slice)a
	d := runtime.Raw_Dynamic_Array {
		data      = s.data,
		len       = s.len,
		cap       = s.len,
		allocator = runtime.nil_allocator(),
	}
	return transmute([dynamic]E)d
}

node_children :: proc(node: Node, i: ^int) -> (Node, bool) {
	defer i^ += 1

	switch node.symbol {
	case .EOF,
	     .ERR,
	     .SEMICOLON,
	     .TYPE,
	     .EQUALS,
	     .FUNC,
	     .OPEN_PAREN,
	     .CLOSE_PAREN,
	     .ARROW,
	     .OPEN_BRACE,
	     .CLOSE_BRACE,
	     .partial_ident,
	     .COLON,
	     .COMMA,
	     .generic_ident,
	     .DOT,
	     .int_literal,
	     .str_literal,
	     .OPEN_BRACKET,
	     .CLOSE_BRACKET,
	     .UNDERSCORE,
	     .CARET,
	     .QUESTION,
	     .type_sign,
	     .prefix_slice,
	     .LOOP,
	     .IF,
	     .ELSE,
	     .BREAK,
	     .LET,
	     .SIZE_OF,
	     .ALIGN_OF,
	     .TRIPLE_DASH,
	     .DO,
	     .CAST,
	     .DOUBLE_DASH,
	     .DOUBLE_PLUS,
	     .AS,
	     .prefix_pointer:
		return {}, false
	case .definition, .definition_type, .definition_func:
		switch i^ {
		case 0:
			return {.partial_ident, {ident = node.value.definition.name}}, true
		case 1:
			return {
					.generics_defs,
					{generics_defs = into_dynamic(node.value.definition.generics)},
				},
				true
		case 2:
			switch sign in node.value.definition.sign {
			case ast.Definition_Type:
				return {.type_sign, {type_sign = sign}}, true
			case ast.Definition_Func:
				return {.func_sign, {func_sign = sign}}, true
			}
		case 3:
			impl := node.value.definition.impl.? or_break
			switch _ in node.value.definition.sign {
			case ast.Definition_Type:
				return {.data_type_full, {data_type = impl.definition_type}}, true
			case ast.Definition_Func:
				return {.body, {body = impl.definition_func}}, true
			}
		}
	case .lucu:
		arr := node.value.lucu
		if i^ >= len(arr) do break
		return {.definition, {definition = arr[len(arr) - i^ - 1]}}, true
	case .generics_defs:
		arr := node.value.generics_defs
		if i^ >= len(arr) do break
		return {.generic_ident, {ident = arr[len(arr) - i^ - 1]}}, true
	case .exprs_semi, .exprs_comma:
		arr := node.value.exprs_semi
		if i^ >= len(arr) do break
		return {.expr, {expr = arr[len(arr) - i^ - 1]}}, true
	case .params:
		arr := node.value.params
		if i^ >= len(arr) do break
		return {.param, {param = arr[len(arr) - i^ - 1]}}, true
	case .members, .struct_members:
		arr := node.value.members
		if i^ >= len(arr) do break
		return {.member, {param = arr[len(arr) - i^ - 1]}}, true
	case .generics:
		arr := node.value.generics
		if i^ >= len(arr) do break

		switch generic in arr[len(arr) - i^ - 1] {
		case string:
			return {.str_literal, {str_literal = generic}}, true
		case u64:
			return {.int_literal, {int_literal = generic}}, true
		case ast.Type:
			return {.data_type_full, {data_type = generic}}, true
		}
	case .type_prefixes:
		arr := node.value.type_prefixes
		if i^ >= len(arr) do break

		switch prefix in arr[len(arr) - i^ - 1] {
		case ast.Type_Slice:
			return {.prefix_slice, {prefix_slice = prefix}}, true
		case ast.Type_Array:
			return {.prefix_array, {prefix_array = prefix}}, true
		case ast.Type_Pointer:
			return {.prefix_pointer, {prefix_pointer = prefix}}, true
		}
	case .type_prefix:
		if i^ != 0 do break

		switch prefix in node.value.type_prefix {
		case ast.Type_Slice:
			return {.prefix_slice, {prefix_slice = prefix}}, true
		case ast.Type_Array:
			return {.prefix_array, {prefix_array = prefix}}, true
		case ast.Type_Pointer:
			return {.prefix_pointer, {prefix_pointer = prefix}}, true
		}
	case .data_type_full, .data_type, .type_head:
		if i^ == 0 && node.value.data_type.prefix == nil do i^ = 1

		switch i^ {
		case 0:
			return {.type_prefixes, {type_prefixes = into_dynamic(node.value.data_type.prefix)}},
				true
		case 1:
			switch head in node.value.data_type.head {
			case ast.Ident_Full:
				return {.ident_full, {ident_full = head}}, true
			case ast.Type_Struct:
				return {.type_struct, {type_struct = head}}, true
			case nil:
				return {.UNDERSCORE, {}}, true
			}
		}
	case .ident_package, .ident_full:
		if i^ == 0 && node.value.ident_full.pkg == "" do i^ = 1
		if i^ == 2 && node.value.ident_full.generics == nil do i^ = 3

		switch i^ {
		case 0:
			return {.partial_ident, {ident = node.value.ident_full.pkg}}, true
		case 1:
			if node.value.ident_full.pkg == "" {
				return {.ident, {ident = node.value.ident_full.ident}}, true
			} else {
				return {.partial_ident, {ident = node.value.ident_full.ident}}, true
			}
		case 2:
			return {.generics, {generics = into_dynamic(node.value.ident_full.generics)}}, true
		}
	case .func_sign:
		switch i^ {
		case 0:
			return {.params, {params = into_dynamic(node.value.func_sign.params)}}, true
		case 1:
			output := node.value.func_sign.output.? or_break
			return {.data_type_full, {data_type = output}}, true
		}
	case .param:
		switch i^ {
		case 0:
			return {.partial_ident, {ident = node.value.param.name}}, true
		case 1:
			return {.data_type_full, {data_type = node.value.param.type}}, true
		}
	case .member, .named_member:
		if i^ == 0 && node.value.member.name == "" do i^ = 1

		switch i^ {
		case 0:
			return {.partial_ident, {ident = node.value.param.name}}, true
		case 1:
			return {.data_type_full, {data_type = node.value.param.type}}, true
		}
	case .type_struct:
		switch i^ {
		case 0:
			return {.members, {params = into_dynamic(node.value.type_struct.members)}}, true
		}
	case .ident:
		if i^ != 0 do break

		if node.value.ident[0] == '\'' {
			return {.generic_ident, {ident = node.value.ident}}, true
		} else {
			return {.partial_ident, {ident = node.value.ident}}, true
		}
	case .prefix_array:
		if i^ != 0 do break

		switch size in node.value.prefix_array.size {
		case u64:
			return {.int_literal, {int_literal = size}}, true
		case ast.Ident_Full:
			return {.ident_full, {ident_full = size}}, true
		case nil:
			return {.UNDERSCORE, {}}, true
		}
	case .body, .expr, .expr0, .expr1, .expr2, .expr3, .expr4:
	}

	return {}, false
}

