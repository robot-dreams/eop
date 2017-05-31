# eop

In December 2015 I spent 11 days working through the masterpiece "Elements of Programming" by Alexander Stepanov and Paul McJones.  This repository is the result of those 11 days.

I've written up proofs to most of the lemmas stated in the text here:
https://github.com/robot-dreams/eop/blob/master/lemmas.md

The code in this repository is a combination of code copied directly from the text and my own work (natural extensions + solutions to exercises).  You shouldn't expect to find any of the actual code particularly useful--it's likely that everything here already has some (more optimized and polished) counterpart in the C++ STL or another library (Boost?).  However, here are some highlights:

* [Iterative mergesort for linked lists (!)](https://github.com/robot-dreams/eop/commit/1526c4db3e1157c0436b688890795bc1c72ad260)
* [goto considered useful (for implementing a simple state machine)](https://github.com/robot-dreams/eop/blob/master/my_link.h#L181)
* Did I [write](https://github.com/robot-dreams/eop/blob/master/my_copy.h#L287) [enough](https://github.com/robot-dreams/eop/blob/master/my_iterator.h#L1037) [comments](https://github.com/robot-dreams/eop/blob/master/my_bifurcate.h#L620)?
* [Never pass up an opportunity to use the X macro trick](https://github.com/robot-dreams/eop/blob/master/my_selection_test.cpp#L375)
