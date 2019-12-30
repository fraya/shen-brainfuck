(synonyms tape (vector number)
          bfcode (token * number)
          program (vector bfcode)
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

(define <-datum
  { bfvm --> number }
  [Pp Dp Program Tape] -> (<-vector Tape Dp))

(define datum->
  { number --> bfvm --> bfvm }
  N [Pp Dp Program Tape] -> [Pp Dp Program (vector-> Tape Dp N)])

(define datum+
  { number --> bfvm --> bfvm }
  N Bf -> (datum-> (+ (<-datum Bf) N) Bf))

(define <-dp
  { bfvm --> number }
  [Pp Dp Program Tape] -> Dp)

(define dp->
  { number --> bfvm --> bfvm }
  Addr [Pp Dp Program Tape] -> [Pp Addr Program Tape])

(define tape>>
  { number --> bfvm --> bfvm }
  N Bf -> (dp-> (+ (<-dp Bf) N) Bf))

(define <-pp 
  { bfvm --> number }
  [Pp Dp Program Tape] -> Pp)

(define pp->
  { number --> bfvm --> bfvm }
  Addr [Pp Dp Program Tape] -> [Addr Dp Program Tape])

(define program++
  { bfvm --> bfvm }
  Bf -> (pp-> (+ 1 (<-pp Bf)) Bf))
  
(define bfcode
  { bfvm --> bfcode }
  [Pp Dp Program Tape] -> (<-vector Program Pp))

(define b-out
  { bfvm --> bfvm }
  Bf -> (do (output "~A" (n->string (<-datum Bf))) Bf))

(define jmp-f
  { number --> bfvm --> bfvm }
  _ Bf -> Bf where (not (= 0 (<-datum Bf)))
  A Bf -> (pp-> A Bf))

(define jmp-b
  { number --> bfvm --> bfvm }
  _ Bf -> Bf where (= 0 (<-datum Bf))
  A Bf -> (pp-> A Bf))

(define nop
  { bfvm --> bfvm }
  Bf -> Bf)

(define exec
  { bfvm --> bfvm }
  Bf -> (exec' Bf (bfcode Bf)))

(define exec'
  { bfvm --> bfcode --> bfvm }
  Bf (@p + N) -> (datum+ N Bf)
  Bf (@p - N) -> (datum+ (- 0 N) Bf)
  Bf (@p > N) -> (tape>> N Bf)
  Bf (@p < N) -> (tape>> (- 0 N) Bf)
  Bf (@p f N) -> (jmp-f N Bf)
  Bf (@p b N) -> (jmp-b N Bf)
  Bf (@p . _) -> (b-out Bf)
  Bf (@p ? _) -> (nop Bf))

(define bf-run
  { bfvm --> symbol }
  [Pp Dp Program Tape] -> (do (output "~%") done) where (= Pp (limit Program))
  Bf -> (bf-run (program++ (exec Bf))))
  
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
  { program --> program }
  P -> (optimize2' P 1))

(define optimize2'
  { program --> number --> program }
  P Pp -> P where (= Pp (limit P))
  P Pp -> (let I (<-vector P Pp)
               A (match-jf P 1 (+ Pp 1))
               _ (vector-> P Pp (@p f A))
               _ (vector-> P A  (@p b Pp))
              (optimize2' P (+ Pp 1))) where (= f (fst (<-vector P Pp)))
  P Pp  -> (optimize2' P (+ Pp 1)))

(define match-jf
  { program --> number --> number --> number }
  P Lv Pp -> (error "Mismatched jump forward") where (= Pp (limit P))
  _ 0  Pp -> (- Pp 1)
  P Lv Pp -> (match-jf P (+ Lv 1) (+ Pp 1)) where (= f (fst (<-vector P Pp)))
  P Lv Pp -> (match-jf P (- Lv 1) (+ Pp 1)) where (= b (fst (<-vector P Pp)))
  P Lv Pp -> (match-jf P Lv (+ Pp 1)))

(define program
  { string --> program }
  File -> (let Bytes (read-file-as-bytelist File)  
               Bfcode (map byte->bfcode Bytes)
               Opt1   (optimize1 Bfcode)
               P      (list->vector Opt1)
               (optimize2 P)))
  