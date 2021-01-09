package main

import (
	"flag"
	"fmt"
	"os"
	"github.com/viperproject/gorac/internal/gorac"
)

func main() {
	conf, output, err := gorac.ParseFlags(os.Args[0], os.Args[1:])
	if err == flag.ErrHelp {
		fmt.Println(output)
		os.Exit(2)
	} else if err != nil {
		fmt.Println("Error occured:", err)
		fmt.Println("Erroneous output: ", output)
		os.Exit(1)
	}
	gorac.ComputeRuntimeAssertionChecks(conf)
}