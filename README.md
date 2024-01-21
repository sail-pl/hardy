Objectives 

- Design of a toy language with setup/loop arduino like method
- Design of a specification language to express temporal properties over programs (safety only)
- Compilation of the toy language to Why3, properties are translated as first order properties over the history
- Formalisation in Coq of the toy language and of a minimal subset of why3 to certify the correctness of the compilation 

TODO

- clean code for the parser
- see how to use the untype why3 API instead of the local definition
- write many examples directly in why3 to see how to perform the translation automatically
- put auxiliary functions of the instrumentation in a separated file
