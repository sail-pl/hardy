## Objectives 

- Design of a toy language with setup/loop arduino like method
- Design of a specification language to express temporal properties over programs (safety only)
- Compilation of the toy language to Why3, properties are translated as first order properties over the history
- Formalisation in Coq of the toy language and of a minimal subset of why3 to certify the correctness of the compilation 

## Toy language 

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
    | x := ( e | ! s) // assign the value of a simple expression or of a signal  
    | emit s e        // emit a signal  
    | c;c  
    | if e then c else c end   
    | while e do c done  

### Temporal formulas F (first order logic over words)

  - predicates over positions index and values (e.g i < j -> s(i) < s(j))
  - F /\ F, F \/ F, not F, F -> F
  - forall i. F (* where i is a position *)
  - exists i. F (* where i is a position *)

### PLTL formulas 

Formulas are interpreter over finite non-empty traces.


$$
\begin{array}{lcll}
\phi,\psi &::=& \mid True \mid \neg \phi \mid \phi \vee \psi \\
&& \mid p & {\text{(atomic proposition)}}\\
&& \mid {\mathcal{Y}} ~ \phi & {\text{(yesterday)}}\\
&& \mid \phi ~ {\mathcal{S}} ~ \psi & {\text{(since)}}
\end{array}
$$

$$
\begin{array}{lcll}
  \mathcal{O} ~ \phi & = & True ~ {\mathcal{S}} ~ \phi & {\text{(once)}} \\
  \mathcal{H} ~ \phi &=& \neg ({\mathcal{O}} ~ (\neg ~ \phi)) & {\text{(historically)}}
\end{array}
$$

The function $current$ returns the last instant. Given a natural number i, $shift ~ i$ performs a backward time shift of i positions.

$$
\begin{array}{lcl}
current ~ (a \cdot tr) &=& a
\\
\\
shift ~ 0 ~ tr &=& tr \\
shift ~ (i + 1) ~ (a \cdot tr) &=& shift ~ i ~ tr
\end{array}
$$

$$
\begin{array}{lcl}
  tr \models True\\
  tr \models \neg ~ \phi ~ &\Leftrightarrow& ~ \neg (tr \models \phi)\\
  tr \models \phi \vee \psi ~ &\Leftrightarrow& ~ tr \models \phi \vee tr \models \psi\\ 
  tr \models p ~ &\Leftrightarrow& ~  p ~ (current ~ a)\\ 
  tr \models {\mathcal{Y}} ~ \phi ~ &\Leftrightarrow& ~ shift ~ 1 ~ tr \models \phi\\
  tr \models \phi ~ {\mathcal{S}} ~\phi ~ &\Leftrightarrow& \exists i. shift ~ i ~ tr \models \phi \wedge \forall k. 0 <= k < i -> shift ~ k ~ tr \models \psi
\end{array}
$$
## TODO

- clean code for the parser
- see how to use the untype why3 API instead of the local definition
- write many examples directly in why3 to see how to perform the translation automatically
- put auxiliary functions of the instrumentation in a separated file
