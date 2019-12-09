(load "brainfuck.shen")

(set *program* (program [+ + + -]))
(set *bf* (bf-make (value *program*)
                   (tape-make 3)))

(bf-run (value *bf*))