package parser

import "./generated"

// Parses an array of tokens into the abstract syntax tree.
// This deletes the token array for you.
parse :: generated.parse
peek :: generated.peek

State :: generated.State
Parser :: generated.Parser

init :: generated.parser_init
delete :: generated.parser_delete
step :: generated.parser_step

will_shift :: generated.parser_will_shift

