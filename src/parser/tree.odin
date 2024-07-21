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
	     .ARROW_RIGHT,
	     .ARROW_LEFT,
	     .OPEN_BRACE,
	     .CLOSE_BRACE,
	     .partial_ident,
	     .COLON,
	     .COMMA,
	     .generic_ident,
	     .option_ident,
	     .DOT,
	     .int_literal,
	     .str_literal,
	     .OPEN_BRACKET,
	     .CLOSE_BRACKET,
	     .UNDERSCORE,
	     .CARET,
	     .QUESTION,
	     .prefix_slice,
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
	     .DASH,
	     .PLUS,
	     .STAR,
	     .SLASH,
	     .GREATER,
	     .GREATER_EQUALS,
	     .LESS,
	     .LESS_EQUALS,
	     .ARROW_RIGHT_FAT,
	     .DOUBLE_EQUALS,
	     .BANG_EQUALS,
	     .DOUBLE_DOT,
	     .PERCENT,
	     .PLUS_EQUALS,
	     .DASH_EQUALS,
	     .SLASH_EQUALS,
	     .STAR_EQUALS,
	     .PERCENT_EQUALS,
	     .AMPERSAND,
	     .USING,
	     .HANDLE,
	     .EFFECT,
	     .MUT,
	     .CONST,
	     .IMPORT,
	     .prefix_pointer:
		return {}, false
	case .definition,
	     .definition_type,
	     .definition_func,
	     .definition_effect,
	     .definition_use,
	     .definition_const:
		def, ok := node.value.definition.sign.(ast.Definition_Use)
		if !ok && node.value.definition.name == "" && (i^ == 1 || i^ == 2) do i^ = 3
		if ok && i^ == 2 do i^ = 3

		switch i^ {
		case 0:
			return {
					.definition_context,
					{definition_context = into_dynamic(node.value.definition.ctxt)},
				},
				true
		case 1:
			if ok {
				return {.ident_full, {ident_full = def.ident}}, true
			} else {
				return {.partial_ident, {ident = node.value.definition.name}}, true
			}
		case 2:
			return {
					.generics_defs,
					{generics_defs = into_dynamic(node.value.definition.generics)},
				},
				true
		case 3:
			switch sign in node.value.definition.sign {
			case ast.Definition_Type:
				return {.TYPE, {}}, true
			case ast.Definition_Effect:
				return {.EFFECT, {}}, true
			case ast.Definition_Const:
				return {.data_type_full, {data_type_full = sign.type}}, true
			case ast.Definition_Use:
				return {.HANDLE, {}}, true
			case ast.Definition_Func:
				return {.func_sign, {func_sign = sign}}, true
			}
		case 4:
			impl := node.value.definition.impl.? or_break
			switch _ in node.value.definition.sign {
			case ast.Definition_Type:
				return {.data_type_full, {data_type = impl.definition_type}}, true
			case ast.Definition_Effect, ast.Definition_Use:
				return {.definitions, {definitions = into_dynamic(impl.definition_effect)}}, true
			case ast.Definition_Func:
				return {.body, {body = impl.definition_func}}, true
			case ast.Definition_Const:
				return {.expr, {expr = impl.definition_const}}, true
			}
		}
	case .lucu, .definitions:
		arr := node.value.lucu
		if i^ >= len(arr) do break
		return {.definition, {definition = arr[len(arr) - i^ - 1]}}, true
	case .generics_defs:
		arr := node.value.generics_defs
		if i^ >= len(arr) do break
		return {.generic_ident, {ident = arr[len(arr) - i^ - 1]}}, true
	case .stmts_semi, .stmts_semi_suffix, .exprs, .member_exprs_struct, .member_exprs:
		arr := node.value.exprs
		if i^ >= len(arr) do break
		return {.expr, {expr = arr[len(arr) - i^ - 1]}}, true
	case .params:
		arr := node.value.params
		if i^ >= len(arr) do break
		return {.param, {param = arr[len(arr) - i^ - 1]}}, true
	case .lambda_params:
		arr := node.value.lambda_params
		if i^ >= len(arr) do break
		return {.lambda_param, {param = arr[len(arr) - i^ - 1]}}, true
	case .members, .struct_members:
		arr := node.value.members
		if i^ >= len(arr) do break
		return {.member, {param = arr[len(arr) - i^ - 1]}}, true
	case .definition_context, .constraints:
		arr := node.value.constraints
		if i^ >= len(arr) do break
		return {.constraint, {ident_full = arr[len(arr) - i^ - 1]}}, true
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
	case .data_type_full, .data_type, .type_head, .data_type_full_nofunc:
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
			case ast.Type_Func:
				return {
						.definition_func,
						{definition_func = {head.ctxt, "", nil, head.sign, nil}},
					},
					true
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
			output := node.value.func_sign.output
			if output == nil do break
			return {.data_type_full, {data_type = output^}}, true
		}
	case .member, .named_member, .param, .lambda_param, .lambda_param_nofunc:
		if i^ == 0 && node.value.member.name == "" do i^ = 1
		if i^ == 1 && node.value.member.type.prefix == nil && node.value.member.type.head == nil do i^ = 2

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
	case .pre:
		if i^ != 0 do break
		sym, _ := unop_symbol(node.value.pre)
		return {sym, {}}, true
	case .mul, .add, .cmp, .eq, .range, .ass_op:
		if i^ != 0 do break
		return {binop_symbol(node.value.mul), {}}, true
	case .struct_expr, .array_expr, .cond_expr, .body, .lambda, .call:
		arr := node.value.expr.data.base
		if i^ >= len(arr) do break
		return {.expr, {expr = arr[len(arr) - i^ - 1]}}, true
	case .imports:
	// TODO
	case .constraint:
	// TODO
	case .expr,
	     .expr_top,
	     .expr_post,
	     .expr_pre,
	     .expr_keyword,
	     .expr_typed,
	     .stmt,
	     .stmt_final,
	     .expr_mul,
	     .expr_add,
	     .expr_cmp,
	     .expr_eq,
	     .expr_range,
	     .expr_nolambda,
	     .expr_pre_lambda,
	     .expr_keyword_lambda,
	     .expr_typed_lambda,
	     .expr_mul_lambda,
	     .expr_add_lambda,
	     .expr_cmp_lambda,
	     .expr_eq_lambda,
	     .expr_range_lambda,
	     .expr_lambda,
	     .lambda_body,
	     .expr_post_lambda,
	     .stmt_ass,
	     .named_expr,
	     .member_expr,
	     .stmt_ass_op:
		switch node.value.expr.kind {
		case .BODY:
			if i^ > 0 do break
			return {.body, node.value}, true
		case .LAMBDA:
			if i^ > 0 do break
			return {.lambda, node.value}, true
		case .CALL, .CALL_POINTER:
			if i^ > 0 do break
			return {.call, node.value}, true
		case .IF_ELSE, .IF_ELSE_UNWRAP:
			if i^ > 0 do break
			return {.cond_expr, node.value}, true
		case .ARRAY:
			if i^ > 0 do break
			return {.array_expr, node.value}, true
		case .STRUCT:
			if i^ > 0 do break
			return {.struct_expr, node.value}, true
		case .BINARY_OP:
			switch i^ {
			case 0:
				return {.expr, {expr = node.value.expr.data.base[1]}}, true
			case 1:
				return {binop_symbol(node.value.expr.data.binop.operator), {}}, true
			case 2:
				return {.expr, {expr = node.value.expr.data.base[0]}}, true
			case 3:
				if node.value.expr.data.binop.operator == .INDEX {
					return {.CLOSE_BRACKET, {}}, true
				}
			}
		case .MEMBER:
			switch i^ {
			case 0:
				return {.expr, {expr = node.value.expr.data.base[0]}}, true
			case 1:
				return {.DOT, {}}, true
			case 2:
				return {.partial_ident, {ident = node.value.expr.data.member.member}}, true
			}
		case .AS:
			switch i^ {
			case 0:
				return {.expr, {expr = node.value.expr.data.base[0]}}, true
			case 1:
				return {.AS, {}}, true
			case 2:
				return {.data_type_full, {data_type_full = node.value.expr.data.as.type}}, true
			}
		case .SIZE_OF:
			switch i^ {
			case 1:
				return {.SIZE_OF, {}}, true
			case 2:
				return {.data_type_full, {data_type_full = node.value.expr.data.sizeof.type}}, true
			}
		case .ALIGN_OF:
			switch i^ {
			case 1:
				return {.ALIGN_OF, {}}, true
			case 2:
				return {.data_type_full, {data_type_full = node.value.expr.data.alignof.type}},
					true
			}
		case .UNARY_OP:
			if i^ >= 2 do break
			sym, rhs := unop_symbol(node.value.expr.data.unnop.operator)
			if (i^ == 1) == rhs {
				return {sym, {}}, true
			} else {
				return {.expr, {expr = node.value.expr.data.base[0]}}, true
			}
		case .STR:
			if i^ > 0 do break
			return {.str_literal, {str_literal = node.value.expr.data.str.string}}, true
		case .IDENT:
			if i^ > 0 do break
			return {.ident, {ident = node.value.expr.data.ident.ident}}, true
		case .INT:
			if i^ > 0 do break
			return {.int_literal, {int_literal = node.value.expr.data.int.int}}, true
		case .UNINIT:
			if i^ > 0 do break
			return {.TRIPLE_DASH, {}}, true
		case .LET:
			switch i^ {
			case 0:
				return {.LET, {}}, true
			case 1:
				return {.partial_ident, {ident = node.value.expr.data.let.name}}, true
			case 2:
				return {.expr, {expr = node.value.expr.data.base[0]}}, true
			}
		case .USE_HANDLER:
			switch i^ {
			case 0:
				return {.HANDLE, {}}, true
			case 1:
				return {.ident_full, {ident_full = node.value.expr.data.use_handler.ident}}, true
			case 2:
				switch h in node.value.expr.data.use_handler.handler {
				case []ast.Definition:
					return {.definitions, {definitions = into_dynamic(h)}}, true
				case ^ast.Expression:
					return {.lambda, {lambda = h^}}, true
				}
			case 3:
				return {.body, {body = node.value.expr}}, true
			}
		case .MUT:
			switch i^ {
			case 0:
				return {.LET, {}}, true
			case 1:
				return {.partial_ident, {ident = node.value.expr.data.let.name}}, true
			case 2:
				return {.expr, {expr = node.value.expr.data.base[0]}}, true
			}
		case .BREAK:
			switch i^ {
			case 0:
				return {.BREAK, {}}, true
			case 1:
				if len(node.value.expr.data.base) == 0 do break
				return {.expr, {expr = node.value.expr.data.base[0]}}, true
			}
		}
	}

	return {}, false
}

unop_symbol :: proc(op: ast.Unary_Op) -> (generated.Symbol, bool) {
	switch op {
	case .POST_INCREMENT:
		return .DOUBLE_PLUS, true
	case .POST_DECREMENT:
		return .DOUBLE_DASH, true
	case .REFERENCE:
		return .AMPERSAND, false
	case .NEGATE:
		return .DASH, false
	case .PLUS:
		return .PLUS, false
	case .CAST:
		return .CAST, false
	case .DO:
		return .DO, false
	}
	return .ERR, false
}

binop_symbol :: proc(op: ast.Binary_Op) -> generated.Symbol {
	switch op {
	case .ASSIGN:
		return .EQUALS
	case .ADD_ASSIGN:
		return .PLUS_EQUALS
	case .MUL_ASSIGN:
		return .STAR_EQUALS
	case .SUB_ASSIGN:
		return .DASH_EQUALS
	case .MOD_ASSIGN:
		return .PERCENT_EQUALS
	case .DIV_ASSIGN:
		return .SLASH_EQUALS
	case .EQUALS:
		return .DOUBLE_EQUALS
	case .NOT_EQUALS:
		return .BANG_EQUALS
	case .LESS:
		return .LESS
	case .LESS_EQUALS:
		return .LESS_EQUALS
	case .GREATER:
		return .GREATER
	case .GREATER_EQUALS:
		return .GREATER_EQUALS
	case .DIVIDE:
		return .SLASH
	case .MULTIPLY:
		return .STAR
	case .SUBTRACT:
		return .DASH
	case .MODULUS:
		return .PERCENT
	case .ADD:
		return .PLUS
	case .INDEX:
		return .OPEN_BRACKET
	case .RANGE:
		return .DOUBLE_DOT
	}
	return .ERR
}

