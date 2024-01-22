Objectives 

- Design of a toy language with setup/loop arduino like method
- Design of a specification language to express temporal properties over programs (safety only)
- Compilation of the toy language to Why3, properties are translated as first order properties over the history
- Formalisation in Coq of the toy language and of a minimal subset of why3 to certify the correctness of the compilation 

Toy language 

input a b c;
output u v w;
var x y z;

requires {Temporal formula}
ensures {Temporal formula}

setup:
  ensures {Formula}
  // BODY

loop: 
  // BODY


instructions 
  c ::= 
    | x := ( e | ! s) (* assign the value of a simple expression or of a signal *)
    | emit s e        (* emit a signal *)
    | c;c             
    | if e then c else c end 
    | while e do c done

Temporal formulas F (first order logic over words)

  - predicates over positions index and values (e.g i < j -> s(i) < s(j))
  - F /\ F, F \/ F, not F, F -> F
  - forall i. F (* where i is a position *)
  - exists i. F (* where i is a position *)
    

TODO

- clean code for the parser
- see how to use the untype why3 API instead of the local definition
- write many examples directly in why3 to see how to perform the translation automatically
- put auxiliary functions of the instrumentation in a separated file
