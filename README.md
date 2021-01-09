# GoRAC 

GoRAC (**Go** **R**untime **A**ssertion **C**hecker) is a command line tool that generates runtime assertion checks for a Go program that is annotated with a specification. GoRAC supports the following specification constructs: assert statements, assumptions, loop invariants, pre- and postconditions, quantifiers, predicates, old expressions, access permissions, and purity annotations.

## Installation 

GoRAC is written in Go. Therefore, Go needs to be installed. GoRAC uses a patched version of `go/ast`. Since the [patch](https://github.com/golang/go/issues/39753) is not yet merged into the standard Go library (scheduled for the Go 1.17 release), you need to install a custom version of Go as described below. 

The following steps will guide you through the installation of the modified Go version and enable you to run GoRAC.

#### Prerequisites

In order to compile the modified Go version, you already require an official Go release. Therefore, please [download](https://golang.org/dl/) a binary release of Go and follow the official [installation instructions](https://golang.org/doc/install).

If you have [git](https://git-scm.com/) installed, obtain the modified Go version for GoRAC by cloning the following [Github repository](https://github.com/ec-m/go). Please note that the cloned directory should not be called `go/` in order to avoid clashes with existing Go versions.

```
$ git clone git@github.com:ec-m/go.git goroot
``` 

Otherwise you can [download](https://github.com/ec-m/go/archive/master.zip) the sources as a zip file and unpack it in your preferred installation directory that is named anything else but `go/`.

#### Compiling Go

Navigate to the source folder of the cloned or unzipped directory

```
$ cd goroot/src
```

and run 

```
$ ./all.bash
```

or for Windows `all.bat`. 

If the installation was successful, you should see the message `ALL TESTS PASSED [...]`. In case something goes wrong, please consult the official instructions for [installing Go from source](https://golang.org/doc/install/source).

#### Adding to PATH

Add the custom Go installation to the PATH environment variable.

```
$ export PATH=$PATH:/path/to/goroot/bin
``` 

#### Setting GOROOT

Set the environment variable `GOROOT` to the folder the modified Go version was installed in.

``` 
$ export GOROOT=/path/to/goroot
```

In case you use [JetBrains Goland IDE](https://www.jetbrains.com/go/) you can follow [these instructions](https://www.jetbrains.com/help/go/configuring-goroot-and-gopath.html) to adjust `GOROOT`.

#### Building GoRAC

Clone or download the [GoRAC](https://github.com/viperproject/gorac) source files.
 
```
$ git clone git@github.com:viperproject/gorac.git
```

Open the folder containing the Go files of the command line tool and build GoRAC.

```
$ cd gorac/cmd/gorac
$ go build .
```

This should create an executable called `gorac` in the same directory. 
You can now test the installation by executing the unit tests or use GoRAC as described below.

#### Parser development

The following steps only need to be taken, if you want to change the implementation of the specification parser used by GoRAC.

[Download](https://www.antlr.org/download.html) and [install](https://github.com/antlr/antlr4/blob/master/doc/getting-started.md) ANTLR v4.
You can find the files of the specification parser under

``` 
$ cd gorac/pkg/specparser
```

where `SpecGrammar.g4` defines the grammar of GoRAC specifications. In order to generate lexer 
and parser source files for the grammar execute

```
$ antlr4 -Dlanguage=Go -o . -package specparser -visitor SpecGrammar.g4
```

## Usage

#### Adding specification 

Specification can be added to Go files as comments starting with `//@` for single line and `/*@ ... @*/` for multiline comments.
The following file shows an example Go program that includes specification for a function computing the sum over all natural numbers (including 0) up until some given `n`.

```Go
package main 

//@ requires n >= 0
//@ ensures res == n * (n + 1) / 2
func sum(n int) (res int) {
	res = 0 
	i := 0 // not a specification comment

	/*@
	invariant i <= n + 1
	invariant res == i * (i - 1) / 2
	@*/
	for i <= n {
		res += i
		i++
	}

	//@ assert i == n + 1
	return
}
```

Please consult the [documentation](./doc/specificationlanguage.pdf) for further information on the specification language of GoRAC.

#### Running GoRAC

Assuming the file containing the example program from above is called `sum.go`, you can execute GoRAC on this file

```
$ cd gorac/cmd/gorac
$ ./gorac -file=sum.go ...
```

where `...` can be replaced with more command line flags. This creates the file `sum_rac.go` that contains the original Go program with runtime assertion checks for the provided specification. The generated program `sum_rac.go` can now be run with different inputs to check whether the assertions hold for these executions.

To see all available configuration options of GoRAC, execute

```
$ ./gorac -help
```

## Testing 


#### Unit tests 

Several unit tests are implemented in order to provide a solid testing coverage for all GoRAC and specification parser functions.
All unit tests can be run at once with 

```
$ cd gorac
$ go test ./...
```

## License

All rights are reserved for [ETH Zurich](https://ethz.ch/de.html) represented by Prof. Peter Müller, [Programming Methodology Group](https://www.pm.inf.ethz.ch/).

This project is licensed under the [Mozilla Public License Version 2.0](LICENSE).
