(synonyms bfcode (symbol * number)
          program (vector bfcode)
	  tape (vector number))

(defstruct bfvm
  (pp number)
  (dp number)
  (program program)
  (tape tape))

(define make-tape
  { number --> tape }
  Size -> (make-tape' (vector Size) 1 Size))

(define make-tape'
  { tape --> number --> number --> tape }
  T L L -> T
  T N L -> (make-tape' (vector-> T N 0) (+ N 1) L))

(define make-bfvm
  { program --> bfvm }
  P -> (mk-bfvm 1 1 P (make-tape 100)))
  
(define tape-size
  { bfvm --> number }
  B -> (limit (bfvm-tape B)))
  
(define datum
  { bfvm --> number }
  B -> (<-vector (bfvm-tape B) (bfvm-dp B)))
  
(define datum->
  { bfvm --> number --> bfvm }
  B N -> (do (vector-> (bfvm-tape B) (bfvm-dp B) N) B))

(define datum+
  { bfvm --> number --> bfvm }
  B N -> (do (datum-> B (+ (datum B) N)) B))

(define datum-
  { bfvm --> number --> bfvm }
  B N -> (datum+ B (- 0 N)))

(define dp+
  { bfvm --> number --> bfvm }
  B N -> (error "Tape overflow") where (> (+ N (bfvm-dp B)) (tape-size B))
  B N -> (do (bfvm-dp-> B (+ N (bfvm-dp B))) B))

(define dp-
  { bfvm --> number --> bfvm }
  B N -> (error "Tape underflow") where (< (- (bfvm-dp B) N) 1)
  B N -> (dp+ B (- 0 N)))

(define program-size
  { bfvm --> number }
  B -> (limit (bfvm-program B)))
  
(define pp+
  { bfvm --> number --> bfvm }
  B N -> (error "address overflow") where (> (+ N (bfvm-pp B)) (program-size B))
  B N -> (bfvm-pp-> B (+ (bfvm-pp B) N)))
  
(define pp-
  { bfvm --> number --> bfvm }
  B N -> (error "address underflow") where (< (- (bfvm-pp B) N) 1)
  B N -> (pp+ B (- 0 N)))

(define pp++
  { bfvm --> bfvm }
  B -> (pp+ B 1))

(define pp--
  { bfvm --> bfvm }
  B -> (pp+ B (- 0 1)))
  
(define bfcode
  { bfvm --> bfcode }
  B -> (<-vector (bfvm-program B) (bfvm-pp B)))

(define off?
  { bfvm --> boolean }
  B -> (= (bfvm-pp B) (program-size B)))
  
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
  B _ -> B where (= 0 (datum B))
  B 0 -> (jf' 1 (pp++ B))
  B A -> (bfvm-pp-> B A))

(define jf'
  { number --> bfvm --> bfvm }
  0 B -> B
  _ B -> (error "Mismatched jump forward") where (off? B)
  L B -> (jf' (+ L 1) (pp++ B)) where (= (fst (bfcode B)) jf)
  L B -> (jf' (- L 1) (pp++ B)) where (= (fst (bfcode B)) jb)
  L B -> (jf' L (pp++ B)))

(define jb
  { bfvm --> number --> bfvm }
  B _ -> B where (not (= 0 (datum B)))
  B 0 -> (jb' 1 (pp++ B))
  B A -> (bfvm-pp-> B A))

(define jb'
  { number --> bfvm --> bfvm }
  0 B -> B
  _ B -> (error "Mismatched jump backward") where (= (bfvm-pp B) 1)
  L B -> (jb' (- L 1) (pp-- B)) where (= (fst (bfcode B)) jf)
  L B -> (jb' (+ L 1) (pp-- B)) where (= (fst (bfcode B)) jb)
  L B -> (jb' L (pp-- B)))
  
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

(define exclude-nop
  { (list bfcode) --> (list bfcode) }
  L -> (filter L (/. X (not (= (fst X) nop)))))
  
(define program
  { string --> (vector bfcode) }
  File -> (list->vector (map byte->bfcode (read-file-as-bytelist File))))

