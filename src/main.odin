package lucu

import "core:fmt"
import "core:log"
import "core:os"
import "vendor:wasm/js"

import "lexer"
import "parser"

main2 :: proc(str: string) {
	fmt.print("\033[2J")
	tokens := lexer.tokenize(str)
	for token in tokens {
		lexer.print_token(token)
		fmt.println()
	}
	parser.parse(tokens)
}

main :: proc() {

	when ODIN_OS == .JS {
		js.add_event_listener("text", .Change, nil, proc(e: js.Event) {
			len := js.get_element_value_string_length("text")
			buffer := make([]byte, len)
			defer delete(buffer)

			text := js.get_element_value_string("text", buffer)
			fmt.println(text)
			main2(text)
		})
	}

	main2(
		"type Array 't 'n:usize = ['t]'n\ntype NROM              = Array u8 0x8000\n\nfunc zeroed() -> Array u8 'n { }",
	)

}
