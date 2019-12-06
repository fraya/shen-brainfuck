(load "brainfuck.shen")

(set *program* (program [+ + + -]))
(set *bf* (bfvm-make (value *program*)
     	  	     (tape-make 3)))

(bf-run (value *bf*))