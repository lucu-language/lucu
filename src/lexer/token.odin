package lexer

import "../parser/generated"
import "core:fmt"
import "core:slice"
import "core:strconv"
import "core:strings"
import "core:unicode"
import "core:unicode/utf8"

Symbol :: generated.Symbol
Token :: generated.Token

token_color :: generated.token_color
token_value_string :: generated.token_value_string
token_name :: proc(token: Token) -> string {
	return generated.symbol_name(token.symbol)
}

_next_rune :: proc(text: ^string) -> (char: rune, size: int, ok: bool) {
	if len(text^) == 0 {
		return {}, {}, false
	} else {
		rune, len := utf8.decode_rune_in_string(text^)
		text^ = text[len:]
		return rune, len, true
	}
}

_peek_rune :: proc(text: string) -> (char: rune, size: int, ok: bool) {
	if len(text) == 0 {
		return {}, {}, false
	} else {
		return utf8.decode_rune_in_string(text), true
	}
}

_skip_whitespace :: proc(text: ^string) -> bool {
	found_newline := false
	for len(text^) > 0 {
		rune, offset := utf8.decode_rune_in_string(text^)
		if rune == '#' do for rune != '\n' {
			text^ = text[offset:]
			if len(text^) == 0 do return found_newline
			rune, offset = utf8.decode_rune_in_string(text^)
		}

		if !unicode.is_white_space(rune) do break
		text^ = text[offset:]

		found_newline |= rune == '\n'
	}
	return found_newline
}

Tokenizer :: struct {
	text:          string,
	brace_state:   uint,
	prev_finished: bool,
	peek:          Maybe(Token),
}

_is_operator :: proc(rune: rune) -> bool {
	return (unicode.is_punct(rune) || unicode.is_symbol(rune)) && rune != '_'
}

_next_token :: proc(text: ^string) -> (token: Token, ok: bool) {
	ptr := slice.first_ptr(transmute([]u8)(text^))
	first, len := _next_rune(text) or_return

	if first == '"' {

		str: [dynamic]u8
		for {
			old := text^
			next, size := _next_rune(text) or_break

			if next == '\\' {
				escape, _ := _next_rune(text) or_break
				switch escape {
				case 'n':
					append(&str, '\n')
				case '"':
					append(&str, '"')
				}
			} else if next == '"' {
				break
			} else {
				append_elem_string(&str, old[:size])
			}
		}

		return {.str_literal, {str_literal = transmute(string)str[:]}}, true

	} else if _is_operator(first) && first != '\'' && first != '@' {

		// check with every token if it's a known symbol.
		// this assumes that any prefix of a symbol is also a symbol,
		// except the first character of a symbol

		ident := strings.string_from_ptr(ptr, len)
		symbol := generated.symbol_from_literal(ident)
		for {
			next, size := _peek_rune(text^) or_break
			len += size

			new_ident := strings.string_from_ptr(ptr, len)
			new_symbol := generated.symbol_from_literal(new_ident)
			if new_symbol == .ERR {
				break
			}

			symbol = new_symbol
			_next_rune(text)
		}

		return {symbol, {}}, true
	} else {
		// get full word
		for {
			next, size := _peek_rune(text^) or_break
			if _is_operator(next) || unicode.is_white_space(next) {
				break
			}
			_next_rune(text)
			len += size
		}
		ident := strings.string_from_ptr(ptr, len)

		// check if keyword
		if symbol := generated.symbol_from_literal(ident); symbol != .ERR {
			return {symbol, {}}, true
		}

		// check if number
		// NOTE: this simply overflows with too large integers
		if num, ok := strconv.parse_u64_maybe_prefixed(ident); ok {
			return {.int_literal, {int_literal = num}}, true
		}

		// other, identifier
		if first == '\'' {
			return {.generic_ident, {generic_ident = ident}}, true
		} else {
			return {.partial_ident, {partial_ident = ident}}, true
		}
	}

}

next_token :: proc(state: ^Tokenizer) -> (token: Token, ok: bool) {
	if peek, ok := state.peek.?; ok {
		state.peek = nil
		return peek, true
	}

	newline := _skip_whitespace(&state.text)
	next, ok2 := _next_token(&state.text)
	in_brace := state.brace_state & 1 == 1

	if !ok2 {
		if in_brace && state.prev_finished {
			state.prev_finished = false
			return {.SEMICOLON, {}}, true
		} else {
			return {}, false
		}
	}

	defer state.prev_finished = generated.symbol_precedes_semicolon(next.symbol)

	if in_brace &&
	   newline &&
	   state.prev_finished &&
	   generated.symbol_follows_semicolon(next.symbol) &&
	   next.symbol != .CLOSE_BRACE {
		state.peek = next
		return {.SEMICOLON, {}}, true
	} else {
		return next, true
	}
}

tokenize :: proc(text: string) -> [dynamic]Token {
	tokens := make([dynamic]Token)

	tokenizer := Tokenizer{text, 1, false, nil}
	for token in next_token(&tokenizer) {
		append(&tokens, token)
	}

	return tokens
}

