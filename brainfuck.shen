(synonyms tape (vector number)
          bfcode (symbol * number)
          bfcodes (list bfcode)
          optimization (bfcodes --> bfcodes))

(datatype bfvm

  Pp : number; 
  Dp : number; 
  P  : (vector bfcode); 
  T  : tape;
  ==================
  [Pp Dp P T] : bfvm; )
  
(define mk-tape
  { number --> tape }
  Size -> (mk-tape' (vector Size) 1 Size))

(define mk-tape'
  { tape --> number --> number --> tape }
  T L L -> T
  T N L -> (mk-tape' (vector-> T N 0) (+ N 1) L))
  
(define mk-bfvm
  { (list bfcode) --> bfvm }
  P -> [1 1 (list->vector P) (mk-tape 6000)])

(define <-datum
  { bfvm --> number }
  [Pp Dp P T] -> (<-vector T Dp))

(define datum->
  { number --> bfvm --> bfvm }
  N [Pp Dp P T] -> [Pp Dp P (vector-> T Dp N)])

(define datum+
  { number --> bfvm --> bfvm }
  N B -> (datum-> (+ (<-datum B) N) B))

(define datum-
  { number --> bfvm --> bfvm }
  N B -> (datum+ (- 0 N) B))

(define <-dp
  { bfvm --> number }
  [Pp Dp P T] -> Dp)

(define dp->
  { number --> bfvm --> bfvm }
  A [Pp Dp P T] -> [Pp A P T])

(define tape>>
  { number --> bfvm --> bfvm }
  N B -> (dp-> (+ (<-dp B) N) B))

(define <<tape
  { number --> bfvm --> bfvm }
  N B -> (tape>> (- 0 N) B))

(define <-pp 
  { bfvm --> number }
  [Pp Dp P T] -> Pp)

(define pp->
  { number --> bfvm --> bfvm }
  A [Pp Dp P T] -> [A Dp P T])

(define program>>
  { number --> bfvm --> bfvm }
  N B -> (pp-> (+ N (<-pp B)) B))
  
(define <<program
  { number --> bfvm --> bfvm }
  N B -> (program>> (- 0 N) B))

(define program++
  { bfvm --> bfvm }
  B -> (program>> 1 B))

(define program--
  { bfvm --> bfvm }
  B -> (<<program 1 B))

(define bfcode
  { bfvm --> bfcode }
  [Pp Dp P T] -> (<-vector P Pp))

(define b-out
  { bfvm --> bfvm }
  B -> (do (output "~A" (n->string (<-datum B))) B))

(define jf
  { number --> bfvm --> bfvm }
  _ B -> B where (not (= 0 (<-datum B)))
  0 B -> (jf' 1 (program++ B))
  A B -> (program>> A B))

(define jf'
  { number --> bfvm --> bfvm }
  0 B           -> B
  _ [Pp Dp P T] -> (error "Mismatched jump forward") where (= Pp (limit P))
  L B           -> (jf' (+ L 1) (program++ B)) where (= jf (fst (bfcode B)))
  L B           -> (jf' (- L 1) (program++ B)) where (= jb (fst (bfcode B)))
  L B           -> (jf' L (program++ B)))

(define jb
  { number --> bfvm --> bfvm }
  _ B -> B where (= 0 (<-datum B))
  0 B -> (jb' 1 (program-- B))
  A B -> (<<program A B))

(define jb'
  { number --> bfvm --> bfvm }
  0 B           -> B
  _ [Pp Dp P T] -> (error "Mismatched jump backward") where (= Pp 1)
  L B           -> (jb' (- L 1) (program-- B)) where (= jf (fst (bfcode B)))
  L B           -> (jb' (+ L 1) (program-- B)) where (= jb (fst (bfcode B)))
  L B           -> (jb' L (program-- B)))

(define nop
  { bfvm --> bfvm }
  B -> B)

(define exec
  { bfvm --> bfvm }
  B -> (exec' B (bfcode B)))

(define exec'
  { bfvm --> bfcode --> bfvm }
  B (@p datum+ N) -> (datum+ N B)
  B (@p datum- N) -> (datum- N B)
  B (@p tape>> N) -> (tape>> N B)
  B (@p <<tape N) -> (<<tape N B)
  B (@p jf N)     -> (jf N B)
  B (@p jb N)     -> (jb N B)
  B (@p b-out _)  -> (b-out B)
  B (@p nop _)    -> (nop B))

(define bf-run
  { bfvm --> symbol }
  [Pp Dp P T] -> (do (output "~%") done) where (= Pp (limit P))
  B           -> (bf-run (program++ (exec B))))
  
(define byte->bfcode
  { number --> bfcode }
  43 -> (@p datum+ 1)
  45 -> (@p datum- 1)
  60 -> (@p <<tape 1)
  62 -> (@p tape>> 1)
  46 -> (@p b-out 0)
  91 -> (@p jf 0)
  93 -> (@p jb 0)
  _  -> (@p nop 0))

(define list->vector
  { (list A) --> (vector A) }
  L -> (list->vector-h L (vector (length L)) 1))
  
(define list->vector-h
  { (list A) --> (vector A) --> number --> (vector A) }
  [] V N -> V
  [X | Xs] V N -> (list->vector-h Xs (vector-> V N X) (+ N 1)))

(define filter
  { (list A) --> (A --> boolean) --> (list A) }
  L F -> (filter' L [] F))
  
(define filter'
  { (list A) --> (list A) --> (A --> boolean) --> (list A) }
  [] Result F       -> (reverse Result)
  [X | Xs] Result F -> (filter' Xs [X | Result] F) where (F X)
  [X | Xs] Result F -> (filter' Xs Result F))

(define program
  { string --> (list bfcode) }
  File -> (optimize [exclude-nop] (file->program File)))
  
(define file->program
  { string --> (list bfcode) }
  File -> (map byte->bfcode (read-file-as-bytelist File)))

(define optimize
  { (list optimization) --> bfcodes --> bfcodes }
  [] P -> P
  [Optimization | Os] P -> (optimize Os (Optimization P)))

(define exclude-nop
  { bfcodes --> bfcodes }
  L -> (filter L (/. X (not (= (fst X) nop)))))
