// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

package specparser

import (
	"fmt"
	"github.com/antlr/antlr4/runtime/Go/antlr"
)

// Parse provides the interface for parsing a given input string into a set of specification abstract syntax tree
// nodes. For each specification construct contained in the string, one node is created.
func Parse(input string, line ...int) []Node {
	defer func() {
		if err := recover(); err != nil {
			if len(line) > 0 {
				panic(fmt.Sprintf("Error parsing specification at line %d. Error displayed above.", line[0]))
			} else {
				panic(fmt.Sprintf("Error parsing specification. Error displayed above."))
			}
		}
	}()
	is := antlr.NewInputStream(input)
	lexer := NewSpecGrammarLexer(is)
	stream := antlr.NewCommonTokenStream(lexer, antlr.TokenDefaultChannel)
	p := NewSpecGrammarParser(stream)
	tree := p.Start()
	node := tree.Accept(NewSpecGrammarVisitor()).([]Node)
	return node
}
