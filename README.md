## Objectives 

- Design of a toy language with setup/loop arduino like method
- Design of a specification language to express temporal properties over programs (safety only)
- Compilation of the toy language to Why3, properties are translated as first order properties over the history
- Formalisation in Coq of the toy language and of a minimal subset of why3 to certify the correctness of the compilation 

## Toy language 

input a b c;  
output u v w;  
var x y z;  

requires {PLTL formula}  
ensures {PLTL formula}  

setup:  
  c 

loop:  
  c 

where 


$$
\begin{array}{lcl}
c &::=& \mid x:= e \\
&& \mid x := ~ !s\\
&& \mid emit ~ s ~ e\\
&& \mid c;c \\
&& \mid if ~ e ~ then ~ c ~ else ~ c ~ end\\
&& \mid while ~ e ~ do ~ [Invariant] ~ [Variant] ~ c ~ done 
\end{array}
$$

- Need to add temporal formulas mentionning the state. Where ?
- The separation between i/o formulas and state formulas is not that clear if we consider nested modules

### PLTL formulas 

Formulas are interpreter over finite non-empty traces. 
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

Formulas are defined as follows:

$$
\begin{array}{lcll}
\phi,\psi &::=& \mid True \mid \neg \phi \mid \phi \vee \psi \\
&& \mid p & {\text{(atomic proposition)}}\\
&& \mid {\mathcal{Y}} ~ \phi & {\text{(yesterday)}}\\
&& \mid \phi ~ {\mathcal{S}} ~ \psi & {\text{(since)}}
\end{array}
$$

Intuitively an atomic proposition $p$ holds if it holds at the last instant of the trace.
A formula ${\mathcal{Y}} ~ \phi$ holds, if $\phi$ holds before the last instant.
A formula $\phi ~ {\mathcal{S}} ~ \psi$ holds if 
$\psi$ is valid at one point in time and $\phi$ is valid thereafter.
More formally 

$$
\begin{array}{lcl}
  tr \models True\\
  tr \models \neg ~ \phi ~ &\Leftrightarrow& ~ \neg (tr \models \phi)\\
  tr \models \phi \vee \psi ~ &\Leftrightarrow& ~ tr \models \phi \vee tr \models \psi\\ 
  tr \models p ~ &\Leftrightarrow& ~  p ~ (current ~ a)\\ 
  tr \models {\mathcal{Y}} ~ \phi ~ &\Leftrightarrow& ~ shift ~ 1 ~ tr \models \phi\\
  tr \models \phi ~ {\mathcal{S}} ~\phi ~ &\Leftrightarrow& \exists i. shift ~ i ~ tr \models \phi \wedge \forall k. 0 <= k < i \rightarrow shift ~ k ~ tr \models \psi
\end{array}
$$

We consider the usual operators ${\mathcal{O}}$ (Once) and ${\mathcal{H}}$ (Historically).
Intuitively, a formula ${\mathcal{O}} ~ \phi$ holds if $\phi$ is valid at one point in time.
A formula ${\mathcal{H}} ~ \phi$ holds if $\phi$ always holds. 

$$
\begin{array}{lcll}
  \mathcal{O} ~ \phi & = & True ~ {\mathcal{S}} ~ \phi & {\text{(once)}} \\
  \mathcal{H} ~ \phi &=& \neg ({\mathcal{O}} ~ (\neg ~ \phi)) & {\text{(historically)}}
\end{array}
$$


- Pure-Past Linear Temporal and Dynamic Logic on Finite Traces, De Giacomo, 2020
- Planning for Temporally Extended Goals in Pure-Past Linear Temporal Logic: A Polynomial Reduction to Standard Planning, De Giacomo, 2022
  
### First order logic over words

Should we restrict expressivity to mention only past positions ? We should see how invariants are preserved to answer this question.
Hint : replace while true s by s;while true s to distinguish the first instant (running in the initial state).

  - predicates over positions index and values (e.g i < j -> s(i) < s(j))
  - F /\ F, F \/ F, not F, F -> F
  - forall i. F (* where i is a position *)
  - exists i. F (* where i is a position *)

- A SURVEY ON SMALL FRAGMENTS OF FIRST-ORDER LOGIC OVER FINITE WORDS, Diekert, Gastin and Kufleitner, 2008

## TODO

- clean code for the parser
- see how to use the untype why3 API instead of the local definition
- write many examples directly in why3 to see how to perform the translation automatically
- put auxiliary functions of the instrumentation in a separated file
