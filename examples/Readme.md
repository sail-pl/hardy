# Examples

## Success 

- constant.mlw : 
	+ continuously emits the value of its constant internal state
	+ to check that the initial value of the state is visible
- identity.mlw :
	+ outputs the input value
- incr.mlw :
  	+ record the number of the current instant
  	+ shows that we need to relate the value of variables at the beginning of an
  	  instant to their values at the previous instant if exists, to the initial value otherwise

- onoff.mlw : use invariant instead of formula over words, to update

## Failure
- delay.mlw :
	+ outputs the preceding value of its input



## More examples to test 

- register : 
  	+ input input_val, set; output output_val; var state
  	+ use a variable to store a state
  	+ outputs its state at each instant on output_val
  	+ records the value of input_val when input set is activated
