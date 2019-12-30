(synonyms tape (vector number)
          bfcode (token * number)
	  instruction (bfvm --> bfvm)
          program (vector instruction)
          optimization ((list bfcode) --> (list bfcode)))

(datatype token
  if (element? X [+ - > < f b . ?])
  __________
  X : token; )

(datatype bfvm

  Pp : number; 
  Dp : number; 
  P  : program; 
  T  : tape;
  ===========
  [Pp Dp P T] : bfvm; ) 
  
(define mk-tape
  { number --> tape }
  Size -> (mk-tape' Size 1 (vector Size)))

(define mk-tape'
  { number --> number --> tape --> tape }
  Size Size Tape -> Tape
  Size N    Tape -> (mk-tape' Size (+ N 1) (vector-> Tape N 0)))
  
(define mk-bf
  { program --> bfvm }
  Program -> [1 1 Program (mk-tape 3000)])

(define datum+
  { number --> bfvm --> bfvm }
  N [Pp Dp P T] -> [Pp Dp P (vector-> T Dp (+ (<-vector T Dp) N))])

(define tape>>
  { number --> bfvm --> bfvm }
  N [Pp Dp P T] -> [Pp (+ Dp N) P T])

(define pp++
  { bfvm --> bfvm }
  [Pp Dp P T] -> [(+ Pp 1) Dp P T])
  
(define b-out
  { number --> bfvm --> bfvm }
  _ [Pp Dp P T] -> (do (output "~A" (n->string (<-vector T Dp))) [Pp Dp P T]))

(define jmp-f
  { number --> bfvm --> bfvm }
  _ [Pp Dp P T] -> [Pp Dp P T] where (not (= 0 (<-vector T Dp)))
  A [Pp Dp P T] -> [A Dp P T])

(define jmp-b
  { number --> bfvm --> bfvm }
  _ [Pp Dp P T] -> [Pp Dp P T] where (= 0 (<-vector T Dp))
  A [Pp Dp P T] -> [A Dp P T])

(define nop
  { number --> bfvm --> bfvm }
  _ Bf -> Bf)

(define loop
  { bfvm --> symbol }
  [Pp Dp P T] -> (do (output "~%") done) where (= Pp (limit P))
  [Pp Dp P T] -> (loop (pp++ ((<-vector P Pp) [Pp Dp P T]))))
  
(define byte->bfcode
  { number --> bfcode }
  43 -> (@p + 1)
  45 -> (@p - 1)
  60 -> (@p < 1)
  62 -> (@p > 1)
  46 -> (@p . 0)
  91 -> (@p f 0)
  93 -> (@p b 0)
  _  -> (@p ? 0))

(define list->vector
  { (list A) --> (vector A) }
  L -> (list->vector' L (vector (length L)) 1))
  
(define list->vector'
  { (list A) --> (vector A) --> number --> (vector A) }
  [] V N -> V
  [X | Xs] V N -> (list->vector' Xs (vector-> V N X) (+ N 1)))

(define optimize1
  { (list bfcode) --> (list bfcode) }
  L -> (optimize1' 1 L []))

(define optimize1'
  { number --> (list bfcode) --> (list bfcode) --> (list bfcode) }
  Pp [] R                       -> (reverse R)
  Pp [(@p ? 0) | Xs] R          -> (optimize1' (+ Pp 1) Xs R)
  Pp [(@p X N) (@p X M) | Xs] R -> (optimize1' (+ Pp 1) [(@p X (+ N M)) | Xs] R) where (element? X [+ - > <])
  Pp [X | Xs] R                 -> (optimize1' (+ Pp 1) Xs [X | R])) 

(define optimize2
  { (vector bfcode) --> (vector bfcode) }
  P -> (optimize2' P 1))

(define optimize2'
  { (vector bfcode) --> number --> (vector bfcode) }
  P Pp -> P where (= Pp (limit P))
  P Pp -> (let Pp+ (+ Pp 1)
               A (match-jf P 1 Pp+)
               _ (vector-> P Pp (@p f A))
               _ (vector-> P A  (@p b Pp))
              (optimize2' P Pp+)) where (= f (fst (<-vector P Pp)))
  P Pp -> (optimize2' P (+ Pp 1)))

(define match-jf
  { (vector bfcode) --> number --> number --> number }
  P Lv Pp -> (error "Mismatched jump forward") where (= Pp (limit P))
  _ 0  Pp -> (- Pp 1)
  P Lv Pp -> (match-jf P (+ Lv 1) (+ Pp 1)) where (= f (fst (<-vector P Pp)))
  P Lv Pp -> (match-jf P (- Lv 1) (+ Pp 1)) where (= b (fst (<-vector P Pp)))
  P Lv Pp -> (match-jf P Lv (+ Pp 1)))

(define bfcode->program
  { (vector bfcode) --> program }
  Bfcodes -> (bfcode->program' Bfcodes (vector (limit Bfcodes)) (limit Bfcodes) 1))

(define bfcode->program'
  { (vector bfcode) --> program --> number --> number --> program }
  B P Size Size -> P
  B P Size Pp   -> (do (vector-> P Pp (bfcode->instruction (<-vector B Pp)))
                       (bfcode->program' B P Size (+ Pp 1))))
  
(define bfcode->instruction
  { bfcode --> (bfvm --> bfvm) }
  (@p + N) -> (datum+ N)
  (@p - N) -> (datum+ (- 0 N))
  (@p > N) -> (tape>> N)
  (@p < N) -> (tape>> (- 0 N))
  (@p f N) -> (jmp-f N)
  (@p b N) -> (jmp-b N)
  (@p . N) -> (b-out N)
  (@p ? N) -> (nop N))

(define file->program
  { string --> program }
  File -> (let Bytes (read-file-as-bytelist File)  
               Bfcode (map byte->bfcode Bytes)
               Opt1   (optimize1 Bfcode)
               Opt2   (optimize2 (list->vector Opt1))
	       (bfcode->program Opt2)))

(define bf-run
  { string --> symbol }
  File -> (loop (mk-bf (file->program File))))