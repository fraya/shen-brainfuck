(synonyms tape (vector number)
          program (vector instruction)
          instructions (list instruction))

(datatype operator

  if (element? X [+ - > < jmpf jmpb . nop])
  __________
  X : operator; )

(define groupable?
  { operator --> boolean }
  X -> (element? X [+ - > <]))

(datatype instruction
  
  F : operator;
  N : number;
  ===========
  [F N] : instruction; )

\**
 *
 * Brainfuck virtual machine definition, where:
 * 
 * Pp: Program Pointer
 * Dp: Data Pointer
 *  P: Program
 *  T: Tape
 *\

(datatype vm

  Pp : number; 
  Dp : number; 
  P  : program; 
  T  : tape;
  ===========
  [Pp Dp P T] : vm; )

\** Constructors *\

(define mk-tape'
  { number --> tape --> tape }
  0 T -> T
  N T -> (mk-tape' (- N 1) (vector-> T N 0)))

(define mk-tape
  { number --> tape }
  N -> (mk-tape' N (vector N)))
  
(define mk-vm
  { program --> number --> vm }
  P N -> [1 1 P (mk-tape N)])

\* Parse character to instruction *\

(define byte->instruction
  { number --> instruction }
  43 -> [+ 1]
  45 -> [- 1]
  60 -> [< 1]
  62 -> [> 1]
  46 -> [. 0]
  91 -> [jmpf 0]
  93 -> [jmpb 0]
  _  -> [nop 0])

(define jmpf?
  { instruction --> boolean }
  [jmpf _] -> true
  _        -> false)

(define jmpb?
  { instruction --> boolean }
  [jmpb _] -> true
  _        -> false)

\*  Brainfuck's instructions *\

(define pp++
  { vm --> vm }
  [Pp Dp P T] -> [(+ Pp 1) Dp P T])
  
(define b-out
  { number --> vm --> vm }
  _ [Pp Dp P T] -> (let Char (n->string (<-vector T Dp))
		     (do (output "~A" Char)
			 [Pp Dp P T])))

(define jmpf
  { number --> vm --> vm }
  _ [Pp Dp P T] -> [Pp Dp P T] where (not (= 0 (<-vector T Dp)))
  A [Pp Dp P T] -> [A Dp P T])

(define jmpb
  { number --> vm --> vm }
  _ [Pp Dp P T] -> [Pp Dp P T] where (= 0 (<-vector T Dp))
  A [Pp Dp P T] -> [A Dp P T])

(define execute
  { vm --> instruction --> vm }
  [Pp Dp P T] [+ N] -> [Pp Dp P (vector-> T Dp (+ (<-vector T Dp) N))] 
  [Pp Dp P T] [- N] -> [Pp Dp P (vector-> T Dp (- (<-vector T Dp) N))] 
  [Pp Dp P T] [> N] -> [Pp (+ Dp N) P T]
  [Pp Dp P T] [< N] -> [Pp (- Dp N) P T]
  Vm [jmpf A]       -> (jmpf A Vm)
  Vm [jmpb A]       -> (jmpb A Vm)
  Vm [. N]          -> (b-out N Vm)
  Vm _              -> Vm)

(define loop
  { vm --> symbol }
  [Pp Dp P T] -> (do (output "~%") done) where (= Pp (limit P))
  [Pp Dp P T] -> (loop (pp++ (execute [Pp Dp P T] (<-vector P Pp)))))


\** Utilities *\

(define list->vector
  { (list A) --> (vector A) }
  L -> (list->vector' L (vector (length L)) 1))
  
(define list->vector'
  { (list A) --> (vector A) --> number --> (vector A) }
  [] V N -> V
  [X | Xs] V N -> (list->vector' Xs (vector-> V N X) (+ N 1)))

(define vector->list
  { (vector A) --> (list A) }
  V -> (vector->list' V (limit V) []))

(define vector->list'
  { (vector A) --> number --> (list A) --> (list A) }
  V 0 L -> L
  V N L -> (vector->list' V (- N 1) [(<-vector V N) | L]))
  
\** Optimizations *\

(define optimize1
  { instructions --> instructions }
  P -> (go1' 1 P []))

(define go1'
  { number --> instructions --> instructions --> instructions }
  _  []                 Rs -> (reverse Rs)
  Pp [[nop _] | Xs]     Rs -> (go1' (+ Pp 1) Xs Rs)
  Pp [[F N] [F M] | Xs] Rs -> (go1' (+ Pp 1) [[F (+ N M)] | Xs] Rs) where (groupable? F)
  Pp [X | Xs]           Rs -> (go1' (+ Pp 1) Xs [X | Rs])) 

(define match-jmp
  { program --> number --> number --> number }
  P Lv Pp -> (error "Mismatched jump") where (> Pp (limit P)) 
  _ 0  Pp -> (- Pp 1)
  P Lv Pp -> (match-jmp P (+ Lv 1) (+ Pp 1)) where (jmpf? (<-vector P Pp))
  P Lv Pp -> (match-jmp P (- Lv 1) (+ Pp 1)) where (jmpb? (<-vector P Pp))
  P Lv Pp -> (match-jmp P Lv (+ Pp 1)))

(define optimize2
  { program --> program }
  P -> (optimize2' P 1))

(define optimize2'
  { program --> number --> program }
  P Pp -> P where (= Pp (limit P))
  P Pp -> (let Pp+ (+ Pp 1)
               A (match-jmp P 1 Pp+)
               _ (vector-> P Pp [jmpf A])
               _ (vector-> P A  [jmpb Pp])
              (optimize2' P Pp+)) where (jmpf? (<-vector P Pp))
  P Pp -> (optimize2' P (+ Pp 1)))


(define file->program
  { string --> program }
  Filename -> (let B  (read-file-as-bytelist Filename)  
                   P  (map byte->instruction B)
                   O1 (optimize1 P)
                   (optimize2 (list->vector O1))))

(define bf-run
  { string --> symbol }
  Filename -> (loop (mk-vm (file->program Filename) 3000)))
