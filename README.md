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

Hardy programs are suffixed by `.hd`. Examples can be found in [examples](examples) and are divided in three folders:

- [LTL](examples/LTL/) : examples specified with LTL
- [ppLTL](examples/ppLTL/) examples specified with pure-past LTL
- [WIP](examples/WIP/) : examples not yet working

Executing

```sh
hardy examples/LTL/<file.hd>
```

will:

1. parse `file.hd` as an LTL-specified synchronous reactive program
2. Reduce the program and its temporal specification into a WhyML program `file.hd.mlw` together with local {pre,post}-conditions, inside a directory called `file_gen`
3. Attempt an automatic proof using alt-ergo via the Why3 API.

To execute ppLTL examples, `-s ppltl` must be appended to the above command.

## Specification

For now, only (temporal) safety specification are accepted for the high-level specification.

The low-level specification consists of local invariants written in first-order logic.

As hinted at earlier, there are two specification modes: LTL with past instrumentation at the propositional level and pure-past LTL. The default one is LTL and can be changed using the `-s <spec>` flag (supported modes are `ltl`or `ppltl`)

### Shared (Parameterized) Grammar

```bnf
<LTL(atom)> ::= <atom>                                ; atomic formula
            | '(' <LTL(atom)> ')'
            | "tt"                                    ; TRUE
            | "ff"                                    ; FALSE
            | 'X' <LTL(atom)>                         ; Next
            | 'F' <LTL(atom)>                         ; Eventually    
            | 'G' <LTL(atom)>                         ; Globally
            | <logic_un_op> <LTL(atom)>               ; Common unary boolean operator
            | <LTL(atom)> 'U' <LTL(atom)>             ; Until
            | <LTL(atom)> 'W' <LTL(atom)>             ; Weak Until
            | <LTL(atom)> 'R' <LTL(atom)>             ; Release
            | <LTL(atom)> 'V' <LTL(atom)>             ; Release (alias)
            | <LTL(atom)> 'M' <LTL(atom)>             ; Strong Release
            | <LTL(atom)> <logic_bin_op> <LTL(atom)>  ; Common binary boolean operator 



<FOL(atom)> ::= <atom>
            | '(' <FOL(atom)> ')'
            | "tt" 
            | "ff"
            | <logic_un_op> <FOL(atom)>          
            | <FOL(atom)> <comparison> <FOL(atom)>   
            | <FOL(atom)> <logic_bin_op> <FOL(atom)>
            | "forall"  (  <ID> (':' ty)?   )+        ; universal
            | "exists"  (  <ID> (':' ty)?   )+        ; existential


<logic_bin_op> ::= "->" | "=>" | "<->" | "<=>" | "&&" | "||"

<logic_un_op> ::= '!' ; Not

<comparison> ::= "=" | "<" | "<=" | ">" | ">=" | "<>"

<expr(v)> ::=   v                                     ; program variable   
            | "true" | "false"  
            | '(' expr ')'
            | <INT>                                
            | <REAL>                                  
            | '"' <STRING> '"'
            | '(' ( expr ',' )* ')'                   ; tuple
            | '!' <expr(v)>                           ; negation
            | <expr(v)> <logic_bin_op> <expr(v)>
            | <expr(v)> <comparison> <expr(v)> 
            | <expr(v)>  '[' <expr(v)> ']'            ; array access
            | "[|" (<expr(v)> ';')+ "|]"              ; array literal
```

### Linear Temporal Logic with Past Instrumentation

LTL atoms consists of first-order formulas over program expressions where past values of variables can be referenced and quantified upon:

```bnf

<spec> ::= <LTL(<FOL_h>)> ; high-level program specification

<FOL_h> ::=   "forall_prev" <ID> "as" <ID> ',' <FOL_h>
            | "exists_prev" <ID> "as" <ID> ',' <FOL_h>
            | <FOL(  '{' expr(past_var) '}' )>


past_var ::=  <ID>
            | <ID> ('@' | "at" ) <INT> 
            | ("prev" | "last") <INT>? <ID> 
            | <ID> '#' <INT>
            | ("start" | "first" | '$') <ID>
```

| Syntax                        | Semantics                                                   |
| ----------------------------- | ----------------------------------------------------------- |
| `x at n`, `x@n`               | `x` value at instant `n`                                    |
| `start x`, `first x`, `$x`    | first value of `x` (equivalent to `x@0`)                    |
| `prev n x`, `last n x`, `x#n` | `x` value `n` instants before the current one (`x#0` ⟺ `x`) |
| `prev x`, `last x`            | `x` value at the last instant (equivalent to `x#1`)         |
| `forall_prev x as x_t, f`     | `f` must hold for all past values of `x`, bound to `x_t` in f |
| `exists_prev x as x_t, f`     | `f` must hold for at least one past value of `x`, bound to `x_t` in f |

#### Example

```raw
G ( {o = 0} || {o = i} || {exists_prev i as p, p = o} )
```

[LTL-specified program examples](examples/LTL/)

### Pure-past Linear Temporal Logic

Past disappears from the temporal formulas' atoms, but at the cost of limited expressivity (only propositions are supported at the temporal level).


```bnf

<spec> ::= <LTL('{' <ppLTL> '}')>

<ppLTL> ::=   '{' <FOL(<expr(<ID>)>)> '}'     ; FOL with no past quantification over program variables 
            | 'H' <ppLTL>                     ; Historically
            | 'O' <ppLTL>                     ; Once
            | 'Y' <ppLTL>                     ; Yesterday
            | 'T' <ppLTL>                     ; Weak Yesterday
            | <logic_un_op> <ppLTL>           ; Common unary operators
            | <ppLTL> 'S' <ppLTL>             ; Since
            | <ppLTL> 'Z' <ppLTL>             ; Weak Since
            | <ppLTL> <logic_bin_op> <ppLTL>  ; Common binary operator 
```

#### Example

```raw
guarantees G {
    (
        O {err = 1} &&
        O {err = 2} &&
        Z H {!flag12}
    ) 
    <=> { flag12 }
}
```

[ppLTL-specified program examples](examples/ppLTL/)

### Assumptions and Guarantees

The temporal specification is given as a set of preconditions with the `assumes` keyword and postconditions with the `guarantees` keyword.

Special care must be taken when mentioning outputs in preconditions: they must always be about a past output but even then, might be unsatisfiable:

- `assumes {prev o = 2}` is unsatisfiable : no previous output before the first instant.
- `assumes G {o = 3 }` is unsatisfiable : we cannot make assumption about an output before it happens
- `assumes X G {i=2 -> prev o = 3 }` is satisfiable : we assume previous output to be 3 if current input is 2
- `assumes G ({i=2} -> X {prev o = 2})` is also satisfiable : if the input is 2 at the nth instant, we assume the output to be 2 at the nth+1 instant.

We can mention outputs within assumptions in order to state how the environnement reacts to the program's output:

`assumes X G ({prev o <> 0} -> {i = first n / prev o})`

## Program Syntax

As the focus is the specification of code and not the code itself, programs in hardy are very basic: they are reactive as they must continuously receive input and produce output, but also synchronous: time is discretized as a list of instants, where one input is *synchronized to one output* and no there input is consumed until the current one leads to the production of an output.

Programs thus consists of a `setup` procedure that is run once at the very beginning of execution and used to initialize memory and a main `loop` that runs indefinitely. The code inside is a simplified imperative language with a specific syntax to distinguish writing variables and emitting to an output.

Program composition is not possible currently but is our next priority.

Example

```raw
input 
    value : int
    set : bool
;
output o : int;
var x : int;


setup :
    x := 0;

loop :
    emit x to o;

    if set then
        x := value;
    end
```

## Code Documentation

With `odig` (via `opam install odig`), and after installing `hardy`, use `odig doc hardy`.


## CLI Options

```plain
Usage : hardy <file> [-v]
  -s What is inside an LTL specification : ltl (default) or ppltl for pure past ltl
  -a Automaton format: hoa (uses spot's ltl2tgba, default) or neverclaim (uses ltl2ba) 
  -da Dump specification automata used to generate triples, including their dot representation
  -v Debug output
  -noiaconj Do not add the rely the formula to the guarantee one
  -smoketests Replace all ensures with false to detect inconsistent specification
  -help  Display this list of options
  --help  Display this list of options
```
