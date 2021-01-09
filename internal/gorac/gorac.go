// This source code form is subject to the terms of the Mozilla Public
// License Version 2.0. If a copy of the MPL was not distributed with
// this file, you can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2020 ETH Zurich.

// Package main provides an executable for GoRAC, a program used to generate runtime assertion checks for Go code
// based on provided specification comments.
package gorac

import (
	"bufio"
	"bytes"
	"flag"
	"fmt"
	"go/ast"
	"go/format"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"io"
	"log"
	"os"
	"strings"
)

// Config holds the information specified by the user through command line flags.
type Config struct {
	inputFile                string
	outputFile               string
	printInputFile           bool
	printOutputFile          bool
	printInputAST            bool
	printOutputAST           bool
	writeOutputFile          bool
	generateAssertionChecks  bool
	generatePrePostChecks    bool
	generateInvariantsChecks bool
}

func isFlagPassed(name string, flags *flag.FlagSet) bool {
	found := false
	flags.Visit(func(f *flag.Flag) {
		if f.Name == name {
			found = true
		}
	})
	return found
}

// ParseFlags parses the command line flags provided by the user. On success, it returns the corresponding
// configuration and the output information of the parsing, otherwise it returns the output information and an error.
func ParseFlags(progname string, args []string) (config *Config, output string, err error) {
	flags := flag.NewFlagSet(progname, flag.ContinueOnError)
	var buf bytes.Buffer
	flags.SetOutput(&buf)
	var conf Config
	flags.StringVar(&conf.inputFile, "file", "", "Go file to generate runtime checks for.")
	flags.StringVar(&conf.outputFile, "outputFile", "",
		"Specifies the name of the output file. Defaults to <input_file_name>_rac.go.")
	flags.BoolVar(&conf.printInputFile, "printInputFile", false, "Prints the input Go file to the command line.")
	flags.BoolVar(&conf.printOutputFile, "printOutputFile", false, "Prints the output Go file to the command line.")
	flags.BoolVar(&conf.printInputAST, "printInputAST", false, "Prints the abstract syntax tree of the input to the command line.")
	flags.BoolVar(&conf.printOutputAST, "printOutputAST", false, "Prints the abstract syntax tree of the output to the command line.")
	flags.BoolVar(&conf.generateAssertionChecks, "generateAssertionChecks", false, "Generates runtime checks for all assertions. (Default configuration generates checks for all specification constructs.)")
	flags.BoolVar(&conf.generatePrePostChecks, "generatePrePostChecks", false, "Generates runtime checks for all pre- and postconditions. (Default configuration generates checks for all specification constructs.)")
	flags.BoolVar(&conf.generateInvariantsChecks, "generateInvariantChecks", false, "Generates runtime checks for all invariants. (Default configuration generates checks for all specification constructs.)")
	err = flags.Parse(args)
	// If no RAC generation configuration parameters were passed at all, the default configuration should generate
	// check for all of them.
	if !isFlagPassed("generateAssertionChecks", flags) &&
		!isFlagPassed("generatePrePostChecks", flags) &&
		!isFlagPassed("generateInvariantChecks", flags) {
		conf.generateAssertionChecks = true
		conf.generatePrePostChecks = true
		conf.generateInvariantsChecks = true
	}
	if err != nil {
		return nil, buf.String(), err
	}
	// Set default output file name (since this depends on the input file name which is only available after parsing)
	if conf.outputFile == "" {
		conf.outputFile = strings.TrimSuffix(conf.inputFile, ".go") + "_rac.go"
	}
	return &conf, buf.String(), nil
}

// ComputeRuntimeAssertionChecks encapsulates the runtime assertion check generation for files. It returns the file set,
// the abstract syntax tree (ast) file of the input program and the root node of the ast that includes the runtime checks.
// Based on the given configuration, the input or output files and asts are printed and possibly an output file
// containing the Go code with runtime assertion checks is created.
// Note that the optional parameter `src_unittest_only` provides a way to pass a program as strings to the function.
func ComputeRuntimeAssertionChecks(conf *Config, srcUnittestOnly ...string) (*token.FileSet, *ast.File, ast.Node) {
	fset := token.NewFileSet()
	var err error
	var astFile *ast.File
	if len(srcUnittestOnly) == 0 {
		// Parse the specified input file and receive an ast file or error
		astFile, err = parser.ParseFile(fset, conf.inputFile, nil, parser.ParseComments)
	} else {
		// Parse the given source code string and receive an ast file or error
		astFile, err = parser.ParseFile(fset, "", srcUnittestOnly[0], parser.ParseComments)
	}
	if err != nil {
		panic(err)
	}
	// If configured, print the input file and ast to the command line.
	PrintInfo(conf.printInputFile, conf.printInputAST, "input", fset, astFile)
	// Type check the input file and receive package object
	typesConf := types.Config{Importer: importer.ForCompiler(fset, "source", nil)}
	pkg, err := typesConf.Check("cmd/gorac", fset, []*ast.File{astFile}, nil)
	if err != nil {
		log.Fatal(err)
	}
	// Initializes a new RACGenerator object and calls the runtime check generation that returns the root node of
	// the modified ast that holds the original code together with the runtime checks
	modifiedRoot := NewRACGenerator(conf, fset, astFile, fset.File(astFile.Pos()), pkg).Generate()
	// Write modified program to output file. Only write output file if this is unit test.
	if len(srcUnittestOnly) == 0 {
		writeRACFile(modifiedRoot, fset, conf.outputFile)
	}
	// If configured, print the output file and ast to the command line.
	PrintInfo(conf.printOutputFile, conf.printOutputAST, "output", fset, astFile)
	return fset, astFile, modifiedRoot
}

// PrintInfo prints the program code and/or ast to the command line. The parameter `header` specifies the header/title
// of what is written - in the case of GoRAC these are `input` and `output`.
func PrintInfo(printFile, printAST bool, header string, fset *token.FileSet, f *ast.File) {
	if printFile {
		var buf2 bytes.Buffer
		if err := format.Node(&buf2, fset, f); err != nil {
			panic(err)
		}
		fmt.Printf("--------- %s program ---------\n%s\n", header, buf2.Bytes())
	}
	if printAST {
		err := ast.Print(fset, f)
		if err != nil {
			panic(err)
		}
	}
}

// writeRACFile writes the modified ast that represents the original program with the included runtime assertion checks
// to the file that is specified using the parameter `filename`.
func writeRACFile(n ast.Node, fset *token.FileSet, filename string) {
	var buffer bytes.Buffer
	if err := format.Node(&buffer, fset, n); err != nil {
		panic(err)
	}
	racFile, err := os.Create(filename)
	if err != nil {
		panic(err)
	}
	defer func() {
		if err := racFile.Close(); err != nil {
			panic(err)
		}
	}()
	writer := bufio.NewWriter(racFile)
	buf := make([]byte, 1024)
	for {
		n, err := buffer.Read(buf)
		if err != nil && err != io.EOF {
			panic(err)
		}
		if n == 0 {
			break
		}
		if _, err := writer.Write(buf[:n]); err != nil {
			panic(err)
		}
	}
	if err = writer.Flush(); err != nil {
		panic(err)
	}
}

