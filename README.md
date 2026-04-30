# Hardy, the deductive verifier for high-level temporal properties

<p align=center>
<img src=media/hardy.svg title="Hardy Logo" width=150/>
</p>

*Hardy* is a proof of concept synchronous reactive program verification framework enabling deductive verification of temporal properties.


## Installation

```sh
git clone https://github.com/sail-pl/hardy.git && cd hardy
# install all dependencies in a local switch
opam switch create .
# build and install to the local switch
dune build @install
```

## Basic Usage

Executing

```sh
hardy <file.hd>
```

will:

1. parse `file.hd` as an LTL-specified synchronous reactive program
2. Reduce the program and its temporal specification into a WhyML program `file.hd.mlw` together with local {pre,post}-conditions, inside a directory called `file_gen`
3. Attempt an automatic proof using alt-ergo via the Why3 API.

## Writing Specification

For now, only (temporal) safety specification are accepted for the high-level specification.

The low-level specification consists of local invariants written in first-order logic.

There are two specification modes: LTL with past instrumentation at the propositional level and pure-past LTL. The default one is LTL and can be changed using the `-s` flag

### Linear Temporal Logic with Past Instrumentation



Syntax:



### Pure-past Linear Temporal Logic

Past disappears from the temporal formulas atoms, but at the cost of limited expressivity (only propositions are supported).

Syntax:





## Code Documentation

With `odig` (via `opam install odig`), and after having installed `hardy`, use `odig doc hardy`.


## CLI Options

```plain
Usage : hardy <file> [-v]
  -s What is inside an LTL specification : direct (default) or ppltl for pure past ltl
  -a Automaton format: hoa (uses spot's ltl2tgba, default) or neverclaim (uses ltl2ba) 
  -da Dump specification automata used to generate triples, including their dot representation
  -v Debug output
  -noiaconj Do not add the rely the formula to the guarantee one
  -smoketests Replace all ensures with false to detect inconsistent specification
  -help  Display this list of options
  --help  Display this list of options
```


<!-- Hardy can be decomposed into 3 parts:

- the frontend is a parser for a simple imperative synchronous reactive language annotated by first-order and linear temporal logic formulas. Accepted programs are written in a setup-loop format akin to Arduino where the setup procedure is executed once at the beginning, followed by the loop procedure, the latter repeated indefinitely. At each instant, which corresponds to one execution of the loop procedure, a program consumes an input and produces an output. The temporal specification is parameterized by the inputs and outputs, forming the program's contract. It consists of a *guarantee* and *rely* pair of formulas that describes the expected behaviour of the output across time according to a well-behaved input.
- the middle-end takes such programs and performs transformation based on automata representation of the temporal specification to obtain a set of hoare triples.
- the backend converts the hoare triples to an mlw file that will be fed to Why3 to perform deductive verification. -->
