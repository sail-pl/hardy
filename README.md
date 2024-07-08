<p align=center>
<img src=media/hardy.svg title="Hardy Logo" width=200/>
</p>

*Hardy* is a proof of concept synchronous reactive program verification framework enabling deductive verification of temporal properties.

Hardy can be decomposed into 3 parts:

- the frontend is a parser for a simple imperative synchronous reactive language annotated by first-order and linear temporal logic formulas. Accepted programs are written in a setup-loop format akin to Arduino where the setup procedure is executed once at the beginning, followed by the loop procedure, the latter repeated indefinitely. At each instant, which corresponds to one execution of the loop procedure, a program consumes an input and produces an output. The temporal specification is parameterized by the inputs and outputs, forming the program's contract. It consists of a *guarantee* and *rely* pair of formulas that describes the expected behaviour of the output across time according to a well-behaved input.
- the middle-end takes such programs and performs transformation based on automata representation of the temporal specification to obtain a set of hoare triples.
- the backend converts the hoare triples to an mlw file that will be fed to Why3 to perform deductive verification.