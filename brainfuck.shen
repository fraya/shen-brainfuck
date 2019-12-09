(synonyms tape (vector number))

(datatype program
  P : (vector (bfvm -> bfvm));
  ============================
  P : program; )

(datatype bfvm
  Pp : number; Dp : number; P : program; T : Tape;
  ================================================
  [Pp Dp P T] : bfvm; )

(define tape-make
  { number --> tape }
  N -> (tape-make-h (vector N) 1 N))

(define tape-make-h
  { tape --> number --> number --> tape }
  V L L -> V
  V N L -> (tape-make-h (vector-> V N 0) (+ N 1) L))

(define bf-make
  { program --> tape --> bfvm }
  P T -> [1 1 P T])

(define instruction
  { bfvm --> (bfvm -> bfvm) }
  [Pp Dp P T] -> (<-vector P Pp))

(define incr-pp
  { number --> bfvm --> bfvm }
  N [Pp Dp P T] -> [(+ Pp N) Dp P T])

(define incr-dp
  { bfvm --> number --> bfvm }
  [Pp Dp P T] N -> [Pp (+ Dp N) P T])
  
(define is-off?
  { bfvm --> boolean }
  [Pp Dp P T] -> (> Pp (limit P)))
  
(define bf-run
  { bfvm --> bfvm }
  Vm -> Vm where (is-off? Vm)
  Vm -> (let F (instruction Vm)
               (bf-run (incr-pp 1 (F Vm)))))

(define nop
  { bvfm --> bfvm }
  Vm -> Vm)
  
(define bf-incr
  { number --> bfvm  --> bfvm }
  N [Pp Dp P T1] -> (let V  (<-vector T1 Dp)
                         T2 (vector-> T1 Dp (+ V N))
                            [Pp Dp P T2]))

(define bf-decr
  { number --> bfvm --> bfvm }
  N Bfvm -> (bf-incr (- 0 N) Bfvm))

(define sym->instruction
  { sym --> (bfvm -> bfvm) }
  + -> (bf-incr 1)
  - -> (bf-decr 1)
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


