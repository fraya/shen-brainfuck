(synonyms bfcode (symbol * number)
          bfcodes (list bfcode)
	  optimization (bfcodes --> bfcodes)
          program (vector bfcode)
	  tape (vector number))

(datatype bfvm
  Pp: number; Dp: number; P: program; T: tape;
  ============
  [Pp Dp P T]: bfvm;)
  
(define make-tape
  { number --> tape }
  Size -> (make-tape' (vector Size) 1 Size))

(define make-tape'
  { tape --> number --> number --> tape }
  T L L -> T
  T N L -> (make-tape' (vector-> T N 0) (+ N 1) L))

(define make-bfvm
  { program --> bfvm }
  P -> [1 1 P (make-tape 100)])
  
(define datum
  { bfvm --> number }
  [_ Dp _ T] -> (<-vector T Dp))
  
(define datum->
  { bfvm --> number --> bfvm }
  [Pp Dp P T] N -> (do (vector-> T Dp N) [Pp Dp P T]))

(define datum+
  { bfvm --> number --> bfvm }
  B N -> (do (datum-> B (+ (datum B) N)) B))

(define datum-
  { bfvm --> number --> bfvm }
  B N -> (datum+ B (- 0 N)))

(define dp+
  { bfvm --> number --> bfvm }
  [Pp Dp P T] N -> (error "Tape overflow") where (> (+ N Dp) (limit T))
  [Pp Dp P T] N -> [Pp (+ N Dp) P T])

(define dp-
  { bfvm --> number --> bfvm }
  [Pp Dp P T] N -> (error "Tape underflow") where (< (- Dp N) 1)
  [Pp Dp P T] N -> [Pp (- Dp N) P T])
  
(define pp+
  { bfvm --> number --> bfvm }
  [Pp Dp P T] N -> (error "address overflow") where (> (+ N Pp) (limit P))
  [Pp Dp P T] N -> [(+ Pp N) Dp P T])
  
(define pp-
  { bfvm --> number --> bfvm }
  [Pp Dp P T] N -> (error "address underflow") where (< (- Pp N) 1)
  [Pp Dp P T] N -> [(- Pp N) Dp P T])

(define pp++
  { bfvm --> bfvm }
  B -> (pp+ B 1))

(define pp--
  { bfvm --> bfvm }
  B -> (pp+ B (- 0 1)))
  
(define bfcode
  { bfvm --> bfcode }
  [Pp Dp P T] -> (<-vector P Pp))

(define off?
  { bfvm --> boolean }
  [Pp Dp P T] -> (= Pp (limit P)))
  
(define bf-run
  { bfvm --> symbol }
  B -> (do (output "~%") done) where (off? B)
  B -> (bf-run (pp++ (exec B))))

(define exec
  { bfvm --> bfvm }
  B -> (exec' B (bfcode B)))

(define exec'
  { bfvm --> bfcode --> bfvm }
  B (@p datum+ N) -> (datum+ B N)
  B (@p datum- N) -> (datum- B N)
  B (@p dp+ N)    -> (dp+ B N)
  B (@p dp- N)    -> (dp- B N)
  B (@p jf N)     -> (jf B N)
  B (@p jb N)     -> (jb B N)
  B (@p b-out _)  -> (b-out B)
  B (@p nop _)    -> B
  B _             -> (error "unknown instruction"))

(define b-out
  { bfvm --> bfvm }
  B -> (do (output "~A" (datum B)) B))

(define jf
  { bfvm --> number --> bfvm }
  B _           -> B where (= 0 (datum B))
  B 0           -> (jf' 1 (pp++ B))
  [Pp Dp P T] A -> [A Dp P T])

(define jf'
  { number --> bfvm --> bfvm }
  0 B -> B
  _ B -> (error "Mismatched jump forward") where (off? B)
  L B -> (jf' (+ L 1) (pp++ B)) where (= (fst (bfcode B)) jf)
  L B -> (jf' (- L 1) (pp++ B)) where (= (fst (bfcode B)) jb)
  L B -> (jf' L (pp++ B)))

(define jb
  { bfvm --> number --> bfvm }
  B _           -> B where (not (= 0 (datum B)))
  B 0           -> (jb' 1 (pp++ B))
  [Pp Dp P T] A -> [A Dp P T])

(define jb'
  { number --> bfvm --> bfvm }
  0 B           -> B
  _ [Pp Dp P T] -> (error "Mismatched jump backward") where (= Pp 1)
  L B           -> (jb' (- L 1) (pp-- B)) where (= (fst (bfcode B)) jf)
  L B           -> (jb' (+ L 1) (pp-- B)) where (= (fst (bfcode B)) jb)
  L B           -> (jb' L (pp-- B)))
  
(define byte->bfcode
  { number --> bfcode }
  43 -> (@p datum+ 1)
  45 -> (@p datum- 1)
  60 -> (@p dp- 1)
  62 -> (@p dp+ 1)
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

(define file->bfcode
  { string --> bfcodes }
  File -> (map byte->bfcode (read-file-as-bytelist File)))
  
(define program
  { string --> (list optimization) --> (vector bfcode) }
  File Opts -> (list->vector (optimize Opts (file->bfcode File))))

(define optimize
  { (list optimization) --> bfcodes --> bfcodes }
  []       C -> C
  [O | Os] C -> (optimize Os (O C)))

(define exclude-nop
  { bfcodes --> bfcodes }
  L -> (filter L (/. X (not (= (fst X) nop)))))

