# EDTL
Event-driven temporal logic, test implementation  in C++


The Hand dryer is a simple control system which uses a hands sensor as an input and a dryer switching device as an output. 
Due to the blackbox principle, we abstract from the control logic and observe only the input and output values. 
We formulate the following requirements:

1. If the dryer is on, then it turns off after no hands are present for 1 second.
2. If the dryer was not turned on and hands appeared, it will turn on after no more than 1 cycle.
3. If the hands are present and the dryer is on, it will not turn off.
4. If there is no hands and the dryer is not turned on, the dryer will not turnon until the hands appear.
5. The time of continuous work is no more than an hour.

The requirenments are formulated and checked in C++ code in terms of EDTL. 


Class diagram for the solution:

<img src="terms.png">

