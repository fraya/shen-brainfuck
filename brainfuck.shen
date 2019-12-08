(synonyms tape (vector number))

(datatype program
  P : (vector (bfvm -> bfvm));
  ===========
  P : program; )

(datatype bfvm
  Pp : number; Dp : number; P : program; T : Tape;
  ================================================
  [Pp Dp P T] : bfvm; )

(define tape-make
  { number --> tape }
  N -> (_tape-init (vector N) 1 N))

(define _tape-init
  { tape --> number --> number --> tape }
  V L L -> V
  V N L -> (_tape-init (vector-> V N 0) (+ N 1) L))

(define _tape-change
  { tape --> number --> number --> tape }
  T Dp A -> (let V (+ (<-vector T Dp) A)
                   (vector-> T Dp V)))

(define bfvm-make
  { program --> tape --> bfvm }
  P T -> [1 1 P T])

(define instruction
  { bfvm --> (bfvm -> bfvm) }
  [Pp Dp P T] -> (<-vector P Pp))

(define incr-pp
  { bfvm --> bfvm }
  [Pp Dp P T] -> [(+ 1 Pp) Dp P T])

(define forward-tape
  { bfvm --> bfvm }
  [Pp Dp P T] -> [Pp (+ 1 Dp) P T])
  
(define is-off?
  { bfvm --> boolean }
  [Pp Dp P T] -> (> Pp (limit P)))
  
(define bf-run
  { bfvm --> bfvm }
  Vm -> Vm where (is-off? Vm)
  Vm -> (let F (instruction Vm)
             (incr-pp (F Vm))))

(define nop
  { bvfm --> bfvm }
  Vm -> Vm)
  
(define incr
  { bfvm --> bfvm }
  [Pp Dp P T] -> [Pp Dp P (_tape-change T Dp 1)])

(define decr
  { bfvm --> bfvm }
  [Pp Dp P T] -> [Pp Dp P (_tape-change T Dp -1)])

(define sym->instruction
  { sym --> (bfvm -> bfvm) }
  + -> (function incr)
  - -> (function decr)
  _ -> (function nop))

(define _list->vector
  { (list A) --> (vector A) }
  L -> (_list->vector-help L (vector (length L)) 1))
  
(define _list->vector-help
  { (list A) --> (vector A) --> number --> (vector A) }
  [] V N -> V
  [X | Xs] V N -> (_list->vector-help Xs (vector-> V N X) (+ N 1)))

(define program
  { (list symbol) --> program }
  Syms -> (_list->vector (map sym->instruction Syms)))


