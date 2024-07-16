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
	add_togglers :: proc() {
		js.evaluate(
			`
			const togglers = document.getElementsByClassName("caret")
			for (const toggler of togglers) {
				toggler.addEventListener("click", function() {
					this.parentElement.querySelector(".nested").classList.toggle("active")
					this.classList.toggle("caret-down")
				})
			}
			`,
		)
	}
}

display_tokens :: proc(shifted: #soa[]parser.State, tokens: []lexer.Token) {

	title :: proc(sb: ^strings.Builder, token: lexer.Token) {
		val := lexer.token_value_string(token)
		if val != "" {
			fmt.sbprintf(sb, "title='%s'", val)
			delete(val)
		}
	}

	print :: proc(sb: ^strings.Builder, token: lexer.Token) {
		color := lexer.token_color(token)
		name := lexer.token_name(token)

		fmt.sbprintf(sb, "<span style=\"color:#%02x%02x%02x\"", color[0], color[1], color[2])
		title(sb, token)

		#partial switch token.symbol {
		case .partial_ident, .generic_ident:
			fmt.sbprintf(sb, "><i>%s</i></span>", token.value.ident)
		case .str_literal:
			fmt.sbprintf(sb, "><i>%q</i></span>", token.value.str_literal)
		case .int_literal:
			fmt.sbprintf(sb, "><i>%v</i></span>", token.value.int_literal)
		case:
			fmt.sbprintf(sb, ">%s</span>", lexer.token_name(token))
		}

		if token.symbol == .SEMICOLON {
			fmt.sbprint(sb, "<br>")
		}
	}

	print_tree :: proc(sb: ^strings.Builder, node: parser.Node) {
		current := node
		child := node
		has_children := true
		two_children := false

		nodes := 0
		for has_children && !two_children {
			nodes += 1
			current = child

			zero := 0
			child, has_children = parser.node_children(current, &zero)
			_, two_children = parser.node_children(current, &zero)

			if strings.has_suffix(lexer.token_name(current), "s") {
				two_children = true
			}
		}

		if has_children {
			fmt.sbprint(sb, `<li><span class="caret">`)

			print(sb, node)
			if nodes > 2 {
				fmt.sbprint(sb, "...")
			}
			if nodes > 1 {
				print(sb, current)
			}

			fmt.sbprint(sb, `</span><ul class="nested">`)

			zero := 0
			for child in parser.node_children(current, &zero) {
				print_tree(sb, child)
			}

			fmt.sbprint(sb, `</ul></li>`)
		} else {
			fmt.sbprint(sb, `<li>`)

			print(sb, node)
			if nodes > 2 {
				fmt.sbprint(sb, "...")
			}
			if nodes > 1 {
				print(sb, current)
			}

			fmt.sbprint(sb, `</li>`)
		}
	}

	// Token list
	sb: strings.Builder
	defer strings.builder_destroy(&sb)

	for state in shifted {
		print(&sb, {state.symbol, state.value})
	}

	fmt.sbprint(&sb, " @ ")

	for token in tokens {
		print(&sb, token)
	}

	when ODIN_OS == .JS {
		set_html("tokens", strings.to_string(sb))
	} else {
		fmt.print(strings.to_string(sb))
	}

	// Token tree
	strings.builder_init(&sb)

	first: parser.Node
	if len(shifted) > 0 {
		first = {shifted[0].symbol, shifted[0].value}
	} else if len(tokens) > 0 {
		first = tokens[0]
	} else {
		first = {.EOF, {}}
	}

	print_tree(&sb, first)

	when ODIN_OS == .JS {
		set_html("tree", strings.to_string(sb))
		add_togglers()
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

global_text: string
global_parser: parser.Parser

main :: proc() {

	DEFAULT_TEXT :: "type Array 't 'n = ['t]'n\ntype NROM        = Array u8 0x8000\n\nfunc zeroed()        -> Array u8 'n { }\nfunc filled(val: 't) -> Array 't 'n { }"

	when ODIN_OS == .JS {
		js.set_element_value_string("text", DEFAULT_TEXT)
		js.add_event_listener("text", .Change, nil, proc(e: js.Event) {
			len := js.get_element_value_string_length("text")
			buffer := make([]byte, len)

			delete(global_text)
			global_text = js.get_element_value_string("text", buffer)
			main2(global_text)
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
		js.add_event_listener("next_all", .Click, nil, proc(e: js.Event) {
			state := parser.step(&global_parser)
			for state == .OK {
				state = parser.step(&global_parser)
			}

			slice.reverse(global_parser.stack[:])
			display_tokens(global_parser.shifted[:], global_parser.stack[:])
			slice.reverse(global_parser.stack[:])
		})

		add_togglers()
	}

	main2(DEFAULT_TEXT)

}

