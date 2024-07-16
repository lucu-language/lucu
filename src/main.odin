package lucu

import "core:fmt"
import "core:log"
import "core:os"
import "core:slice"
import "core:strings"
import "vendor:wasm/js"

import "lexer"
import "parser"

when ODIN_OS == .JS {
	set_html :: proc(id: string, html: string) {
		sb: strings.Builder
		defer strings.builder_destroy(&sb)

		fmt.sbprintf(&sb, "document.getElementById(%q).innerHTML = %q", id, html)
		js.evaluate(strings.to_string(sb))
	}
}

display_tokens :: proc(shifted: #soa[]parser.State, tokens: []lexer.Token) {

	token_title :: proc(sb: ^strings.Builder, token: lexer.Token) {
		val := lexer.token_value_string(token)
		if val != "" {
			fmt.sbprintf(sb, "title='%s'", val)
			delete(val)
		}
	}

	token_print :: proc(sb: ^strings.Builder, token: lexer.Token) {
		color := lexer.token_color(token)
		name := lexer.token_name(token)

		fmt.sbprintf(sb, "<span style=\"color:#%02x%02x%02x\"", color[0], color[1], color[2])
		token_title(sb, token)
		fmt.sbprintf(sb, ">%s</span>", name)

		if token.symbol == .SEMICOLON {
			fmt.sbprint(sb, "<br>")
		}
	}

	sb: strings.Builder
	defer strings.builder_destroy(&sb)

	for state in shifted {
		token_print(&sb, {state.symbol, state.value})
	}

	fmt.sbprint(&sb, " @ ")

	for token in tokens {
		token_print(&sb, token)
	}

	when ODIN_OS == .JS {
		set_html("tokens", strings.to_string(sb))
	} else {
		fmt.print(strings.to_string(sb))
	}
}

main2 :: proc(str: string) {
	tokens := lexer.tokenize(str)
	display_tokens({}, tokens[:])

	parser.delete(global_parser)
	global_parser = parser.init(tokens)
}

global_parser: parser.Parser

main :: proc() {

	DEFAULT_TEXT :: "type Array 't 'n:usize = ['t]'n\ntype NROM              = Array u8 0x8000\n\nfunc zeroed()        -> Array u8 'n { }\nfunc filled(val: 't) -> Array 't 'n { }"

	when ODIN_OS == .JS {
		js.set_element_value_string("text", DEFAULT_TEXT)
		js.add_event_listener("text", .Change, nil, proc(e: js.Event) {
			len := js.get_element_value_string_length("text")
			buffer := make([]byte, len)
			defer delete(buffer)

			text := js.get_element_value_string("text", buffer)
			main2(text)
		})
		js.add_event_listener("next", .Click, nil, proc(e: js.Event) {
			parser.step(&global_parser)

			slice.reverse(global_parser.stack[:])
			display_tokens(global_parser.shifted[:], global_parser.stack[:])
			slice.reverse(global_parser.stack[:])
		})
		js.add_event_listener("next_big", .Click, nil, proc(e: js.Event) {
			only_once := !parser.will_shift(&global_parser)
			for {
				parser.step(&global_parser)
				if only_once || !parser.will_shift(&global_parser) do break
			}

			slice.reverse(global_parser.stack[:])
			display_tokens(global_parser.shifted[:], global_parser.stack[:])
			slice.reverse(global_parser.stack[:])
		})
	}

	main2(DEFAULT_TEXT)

}

