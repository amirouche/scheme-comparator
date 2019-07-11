(import (scheme base))
(import (chibi emscripten))

(import (srfi 151)) ;; scheme bitwise
(import (scheme case-lambda))
(import (scheme char))
(import (scheme charset))
(import (scheme comparator))
(import (scheme cxr))
(import (scheme eval))
(import (scheme generator))
(import (scheme hash-table))
(import (scheme list))
(import (scheme sort))
(import (scheme mapping))
(import (scheme mapping hash))
(import (scheme read))
(import (scheme write))


(import (chibi match))
(import (chibi parse))


(write-string "Chibi Scheme is running...\n")

(eval-script! "document.resume = Module['resume']")

;; (scheme bytevector) shims that are (as of yet) missing from chibi

(define (bytevector=? bv other)
  (if (not (= (bytevector-length bv) (bytevector-length other)))
      #f
      (let loop ((index 0))
        (if (zero? (- (bytevector-length bv) index))
            #t
            (if (not (= (bytevector-u8-ref bv index)
                        (bytevector-u8-ref other index)))
                #f
                (loop (+ index 1)))))))

(define (u8-list->bytevector lst)
  (let ((bv (make-bytevector (length lst))))
    (let loop ((lst lst)
               (index 0))
      (unless (null? lst)
        (bytevector-u8-set! bv index (car lst))
        (loop (cdr lst) (+ index 1))))
    bv))

(define (bytevector->u8-list bv)
  (let loop ((index 0)
             (out '()))
    (if (zero? (- (bytevector-length bv) index))
        (reverse out)
        (loop (+ index 1) (cons (bytevector-u8-ref bv index) out)))))

;; scheme helpers

(define-syntax define-syntax-rule
  (syntax-rules ()
    ((define-syntax-rule (keyword args ...) body)
     (define-syntax keyword
       (syntax-rules ()
         ((keyword args ...) body))))))

(define (assume v)
  (unless v
    (error "assume error" v)))

(define (scm->string scm)
  (let ((port (open-output-string)))
    (write scm port)
    (get-output-string port)))

(define (string->scm string)
  (let ((port (open-input-string string)))
    (read port)))

(define (dg . args)
  (write-string (scm->string args))
  (newline))

(define (pk . args)
  (apply dg args)
  (car (reverse args)))

(define (acons a b alist)
  (cons (cons a b) alist))

(define (rm alist key)
  (let loop ((alist alist)
             (out '()))
    (if (null? alist)
        out
        (if (equal? (caar alist) key)
            (append out (cdr alist))
            (loop (cdr alist) (cons (car alist) out))))))

(define (set alist key value)
  (acons key value (rm alist key)))

(define (ref alist key)
  (let loop ((alist alist))
    (cond
     ((null? alist) #f)
     ((equal? (caar alist) key) (cdar alist))
     (else (loop (cdr alist))))))

;; prompt emulated with call/cc

(define %prompt #f)
(define %escape (list 'escape))

(define (call-with-prompt thunk handler)
  (call-with-values (lambda ()
                      (call/cc
                       (lambda (k)
                         (set! %prompt k)
                         (thunk))))
    (lambda out
      (cond
       ((and (pair? out) (eq? (car out) %escape))
        (apply handler (cdr out)))
       (else (apply values out))))))

(define (abort-to-prompt . args)
  (call/cc
   (lambda (k)
     (let ((prompt %prompt))
       (set! %prompt #f)
       (apply prompt (cons %escape (cons k args)))))))


;;; Commentary:
;;
;; arew streams


(define (list->stream lst)
  (let loop ((lst lst))
    (lambda ()
      (if (null? lst)
          (values #f #f)
          (values (car lst) (loop (cdr lst)))))))

(define (stream->list stream)
  (let loop ((stream stream)
             (out '()))
    (call-with-values stream
      (lambda (value next)
        (if next
            (loop next (cons value out))
            (reverse out))))))

(define stream-null
  (lambda ()
    (values #f #f)))

(define (stream-null? stream)
  (call-with-values stream
    (lambda (_ next?)
      (not next?))))

(define (stream-car stream)
  (call-with-values stream (lambda (item _) item)))


;;; Commentary:
;;
;; Parser combinators.
;;
;; TODO: improve error handling
;; TODO: add compatible pk procedure
;;
;; Also see:
;;
;; - https://epsil.github.io/gll/
;; - https://docs.racket-lang.org/parsack/index.html
;; - https://docs.racket-lang.org/megaparsack/
;; - https://git.dthompson.us/guile-parser-combinators.git
;; - https://gitlab.com/tampe/stis-parser
;;
;;; Code:

(define-record-type <result>
  (make-result value stream)
  result?
  (value result-value)
  (stream result-stream))

(define-record-type <failure>
  (make-failure value parser args)
  failure?
  (value failure-value)
  (parser failure-parser)
  (args failure-args))

(define continue make-result)

(define (fail value parser . args)
  (make-failure value parser args))

(define-record-type <xchar>
  ;; extended char with line, column and offset information
  (make-xchar char line column offset)
  xchar?
  (char xchar-char)
  (line xchar-line)
  (column xchar-column)
  (offset xchar-offset))

(define (make-pseudo-xchar char)
  (make-xchar char #f #f #f))

(define (parse-lift proc parser)
  "Apply PROC to the result of PARSER"
  (lambda (stream)
    (let ((out (parser stream)))
      (if (failure? out)
          out
          (continue (proc (result-value out)) (result-stream out))))))

(define (string->stream string)
  ;; TODO: optimize
  (let loop ((chars (string->list string))
             (line 1)
             (column 1)
             (offset 0)
             (out '()))
    (if (null? chars)
        (list->stream (reverse out))
        (if (eq? (car chars) #\newline)
            (loop (cdr chars)
                  (+ 1 line)
                  1
                  (+ 1 offset)
                  (cons (make-xchar #\newline line column offset) out))
            (loop (cdr chars)
                  line
                  (+ 1 column)
                  (+ 1 offset)
                  (cons (make-xchar (car chars) line column offset) out))))))

(define (parse parser stream)
  (let ((out (parser stream)))
    (if (failure? out)
        (error 'combinatorix "parse failed" out)
        (if (stream-null? (result-stream out))
            (result-value out)
            (error 'combinatorix
                   "stream was not fully consumed"
                   (stream-car (result-stream out)))))))

(define (parse-char char)
  (lambda (stream)
    (call-with-values stream
      (lambda (value next)
        (if next
            (if (char=? value char)
                (continue value next)
                (fail value parse-char char))
            (fail (eof-object) parse-char char))))))

(define (parse-xchar char)
  (lambda (stream)
    (call-with-values stream
      (lambda (value next)
        (if next
            (if (char=? (xchar-char value) char)
                (continue value next)
                (fail value parse-xchar char))
            (fail (eof-object) parse-xchar char))))))

(define (%either . args)
  (lambda (stream)
    (let loop ((parsers args))
      (if (null? parsers)
          (apply fail (stream-car stream) %either args)
          (let ((out (((car parsers)) stream)))
            (if (failure? out)
                (loop (cdr parsers))
                out))))))

(define-syntax-rule (parse-either parser ...)
  (%either (lambda () parser) ...))

(define (%each . args)
  (lambda (stream)
    (let loop ((parsers args)
               (stream stream)
               (out '()))
      (if (null? parsers)
          (continue (reverse out) stream)
          (let ((out* (((car parsers)) stream)))
            (if (failure? out*)
                out*
                (loop (cdr parsers)
                      (result-stream out*)
                      (cons (result-value out*) out))))))))

(define-syntax-rule (parse-each parser ...)
  (%each (lambda () parser) ...))

(define (parse-zero-or-more parser)
  (lambda (stream)
    (let loop ((stream stream)
               (out '()))
      (let ((out* (parser stream)))
        (if (failure? out*)
            (continue (reverse out) stream)
            (loop (result-stream out*) (cons (result-value out*) out)))))))

(define (parse-one-or-more parser)
  (parse-lift (lambda (x) (apply cons x)) (parse-each parser (parse-zero-or-more parser))))

(define (parse-when predicate? parser)
  (lambda (stream)
    (call-with-values stream
      (lambda (value next)
        (if next
            (if (predicate? value)
                (parser stream)
                (fail value parse-when predicate?))
            (fail (eof-object) parse-when predicate?))))))

(define (parse-when* parser other)
  ;; more general than parse-when
  (lambda (stream)
    (let ((out (parser stream)))
      (if (failure? out)
          out
          (other stream)))))

(define (parse-unless predicate? parser)
  (parse-when (lambda (value) (not (predicate? value))) parser))

(define (parse-unless* parser other)
  ;; more general than parse-unless
  (lambda (stream)
    (let ((out (parser stream)))
      (if (failure? out)
          (other stream)
          (fail (stream-car stream) parse-unless* parser other)))))

(define (parse-only predicate? parser)
  ;; PARSER succeed only if its results passed to PREDICATE? return
  ;; true.
  (lambda (stream)
    (let ((out (parser stream)))
      (if (failure? out)
          out
          (if (predicate? (result-value out))
              out
              (fail (stream-car stream) parse-only predicate? parser))))))

(define (parse-char-set char-set)
  (lambda (stream)
    (call-with-values stream
      (lambda (value next)
        (if next
            (if (char-set-contains? char-set (xchar-char value))
                (continue value next)
                (fail value parse-char-set char-set))
            (fail (eof-object) parse-char-set char-set))))))

(define parse-any
  (lambda (stream)
    (call-with-values stream
      (lambda (value next)
        (if next
            (continue value next)
            (fail (eof-object) parse-any #f))))))

(define (parse-return value)
  (lambda (stream)
    (continue value stream)))

(define (parse-maybe parser)
  (parse-either parser (parse-return #f)))

(define (parse-string string)
  (apply %each (map (lambda (char) (lambda () (parse-xchar char))) (string->list string))))

;;; Commentary:
;;
;; arew json parser
;;

(define (const v)
  (lambda args v))

(define json-null '(null))

(define (json-null? object)
  (eq? object json-null))

(define (json->scm string)
  (parse json (list->stream (parse tokens (string->stream string)))))

(define (->string value)
  (list->string (map xchar-char value)))

(define (%parse-escaped input output)
  (parse-lift (const (make-pseudo-xchar output)) (parse-string input)))

(define parse-escaped
  (parse-either (%parse-escaped "\\\"" #\")
                (%parse-escaped "\\\\" #\\)
                (%parse-escaped "\\/" #\/)
                (%parse-escaped "\\b" #\backspace)
                ;; (%parse-escaped "\\f" #\formfeed) ;; TODO: FIXME
                (%parse-escaped "\\n" #\newline)
                (%parse-escaped "\\r" #\return)
                (%parse-escaped "\\t" #\tab)
                ;; %parse-unicode
                ))

(define parse-string-token
  (parse-lift cadr
              (parse-each (parse-xchar #\")
                          (parse-lift
                           ->string
                           (parse-zero-or-more
                            (parse-unless
                             (lambda (v) (char=? #\" (xchar-char v)))
                             (parse-either parse-escaped
                                           parse-any))))
                          (parse-xchar #\"))))

(define %parse-integer
  (parse-lift ->string
              (parse-one-or-more
               (parse-char-set char-set:digit))))

(define %parse-float
  (parse-lift (lambda (args) (apply string-append args))
              (parse-each
               %parse-integer
               (parse-lift (const ".") (parse-xchar #\.))
               %parse-integer)))

(define parse-number-token
  (parse-lift string->number
              (parse-either %parse-float
                            %parse-integer)))

(define parse-number-special-token ;; TODO: give its proper name
  (parse-lift (lambda (x) (string->number (apply string-append x)))
              (parse-each
               (parse-lift
                number->string ;; oops!
                (parse-either parse-number-token
                              parse-negative-number-token))
               (parse-lift (lambda (v) (list->string (list (xchar-char v))))
                           (parse-either (parse-xchar #\e)
                                         (parse-xchar #\E)))
               (parse-either %parse-integer
                             (parse-lift (lambda (x) (string-append "-" (cadr x)))
                                         (parse-each (parse-xchar #\-)
                                                     %parse-integer))))))

(define parse-negative-number-token
  (parse-lift (lambda (x) (- (cadr x)))
              (parse-each (parse-xchar #\-)
                          parse-number-token)))

(define parse-true-token (parse-lift (const #t) (parse-string "true")))
(define parse-false-token (parse-lift (const #f) (parse-string "false")))
(define parse-null-token (parse-lift (const json-null) (parse-string "null")))

(define (parse-control-token char symbol)
  (parse-lift (const symbol) (parse-xchar char)))

(define (cleanup lst)
  (filter (lambda (x) (not (null? x))) lst))

(define tokens
  ;; parse character stream into tokens ignoring whitespace between tokens
  (parse-lift
   cleanup
   (parse-one-or-more
    (parse-either parse-string-token
                  parse-number-special-token
                  parse-number-token
                  parse-negative-number-token
                  parse-true-token
                  parse-false-token
                  parse-null-token
                  (parse-control-token #\, 'comma)
                  (parse-control-token #\: 'colon)
                  (parse-control-token #\{ 'brace-open)
                  (parse-control-token #\} 'brace-close)
                  (parse-control-token #\[ 'bracket-open)
                  (parse-control-token #\] 'bracket-close)
                  (parse-lift (const '()) (parse-char-set char-set:whitespace))))))

(define parse-json-string (parse-when string? parse-any))

(define parse-number (parse-when number? parse-any))

(define (parse-symbol symbol)
  (parse-when (lambda (x) (eq? x symbol)) parse-any))

(define %parse-object-item
  (parse-lift (lambda (v) (cons (string->symbol (car v)) (caddr v)))
              (parse-each parse-json-string
                          (parse-symbol 'colon)
                          json)))

(define parse-object
  (parse-either
   (parse-lift (const '())
               (parse-each (parse-symbol 'brace-open)
                           (parse-symbol 'brace-close)))
   (parse-lift (lambda (x) (append '() (cadr x) (list (caddr x))))
               (parse-each
                (parse-symbol 'brace-open)
                (parse-zero-or-more (parse-lift car
                                                (parse-each %parse-object-item
                                                            (parse-symbol 'comma))))
                %parse-object-item
                (parse-symbol 'brace-close)))))

(define parse-array
  (parse-either
   (parse-lift (const '())
               (parse-each (parse-symbol 'bracket-open)
                           (parse-symbol 'bracket-close)))
   (parse-lift (lambda (x) (append (cadr x) (list (caddr x))))
               (parse-each
                (parse-symbol 'bracket-open)
                (parse-zero-or-more (parse-lift car
                                                (parse-each json
                                                            (parse-symbol 'comma))))
                json
                (parse-symbol 'bracket-close)))))

(define parse-true (parse-when (lambda (x) (eq? x #t)) parse-any))

(define parse-false (parse-when (lambda (x) (eq? x #f)) parse-any))

(define parse-null (parse-when (lambda (x) (json-null? x)) parse-any))

(define json
  (parse-either parse-json-string
                parse-number
                parse-object
                parse-array
                parse-true
                parse-false
                parse-null
                ))


(define json->sexp json->scm)

;;
;; render json
;;

(define (assoc->json sexp)
  (let loop ((out "{")
             (sexp sexp))
    (if (null? sexp)
        (if (string=? out "{")
            "{}"
            (string-append (string-copy out 0 (- (string-length out) 1)) "}"))
        (loop (string-append out
                             (sexp->json (caar sexp))
                             ":"
                             (sexp->json (cdar sexp))
                             ",")
              (cdr sexp)))))

(define (list->json sexp)
  (let loop ((out "[")
             (sexp sexp))
    (if (null? sexp)
        (if (string=? out "[")
            "[]"
            (string-append (string-copy out 0 (- (string-length out) 1)) "]"))
        (loop (string-append out (sexp->json (car sexp)) ",")
              (cdr sexp)))))

(define (scheme-string->json-string string)
  ;; TODO: handle other escape sequence like \t
  (let loop ((chars (string->list string))
             (out '()))
    (if (null? chars)
        (list->string (reverse out))
        (if (char=? (car chars) #\newline)
            (loop (cdr chars) (cons #\n (cons #\\ out)))
            (loop (cdr chars) (cons (car chars) out))))))

(define (sexp->json sexp)
  (match sexp
    (#f "false")
    (#t "true")
    ('() "undefined")
    (('@ rest ...) (assoc->json rest))
    ((? pair? sexp) (list->json sexp))
    ((? symbol? sexp) (string-append "\"" (symbol->string sexp) "\""))
    ((? number? sexp) (number->string sexp))
    ((? string? sexp) (string-append "\"" (scheme-string->json-string sexp) "\""))))

;;; Commentary
;;
;; SRFI-167: okvs
;;

(define-record-type <memorydb>
  (make-memorydb store)
  okvs?
  (store memorydb-store memorydb-store!))

(define (lexicographic<? bytevector other)
  (negative? (lexicographic-compare bytevector other)))

(define vector-hash
  (comparator-hash-function
   (make-vector-comparator (make-default-comparator)
                           bytevector?
                           bytevector-length
                           bytevector-u8-ref)))

(define (make-lexicographic-comparator)
  (make-comparator bytevector? bytevector=? lexicographic<? vector-hash))

(define (okvs home . args)
  (make-memorydb (mapping (make-lexicographic-comparator))))

(define (okvs-close . args)
  #t)

(define (okvs-debug okvs proc)
  (mapping-for-each (memorydb-store okvs) proc))

(define-record-type <transaction>
  (make-transaction database store metadata)
  okvs-transaction?
  (database transaction-database transaction-database!)
  (store transaction-store transaction-store!)
  (metadata okvs-transaction-metadata))

(define (okvs-transaction-begin database . args)
  (make-transaction database
                    (memorydb-store database)
                    (make-hash-table (make-default-comparator))))

(define (okvs-transaction-commit transaction . args)
  (memorydb-store! (transaction-database transaction) (transaction-store transaction)))

(define (okvs-transaction-roll-back transaction . args)
  #f)

(define (%okvs-in-transaction okvs proc failure success)
  (let ((transaction (okvs-transaction-begin okvs)))
    (guard (ex
            (else
             (okvs-transaction-roll-back transaction)
             (failure ex)))
      (call-with-values (lambda () (proc transaction))
        (lambda out
          (okvs-transaction-commit transaction)
          (apply success out))))))

(define okvs-in-transaction
  (case-lambda
    ((okvs proc) (okvs-in-transaction okvs proc raise values))
    ((okvs proc failure) (okvs-in-transaction okvs proc failure values))
    ((okvs proc failure success) (%okvs-in-transaction okvs proc failure success))))

(define (okvs-ref transaction key)
  (mapping-ref/default (transaction-store transaction) key #f))

(define (okvs-set! transaction key value)
  (transaction-store! transaction (mapping-set (transaction-store transaction) key value)))

(define (okvs-delete! transaction key)
  (transaction-store! transaction (mapping-delete (transaction-store transaction) key)))

(define (okvs-range-remove! transaction start-key start-include? end-key end-include?)
  (let ((generator (okvs-range transaction start-key start-include? end-key end-include?)))
    (let loop ((pair (generator)))
      (unless (eof-object? pair)
        (let ((key (car pair)))
          (okvs-delete! transaction key)
          (loop (generator)))))))

(define (lexicographic-compare bytevector other)
  ;; Return -1 if BYTEVECTOR is before OTHER, 0 if equal
  ;; and otherwise 1
  (let ((end (min (bytevector-length bytevector)
                  (bytevector-length other))))
    (let loop ((index 0))
      (if (zero? (- end index))
          (if (= (bytevector-length bytevector)
                 (bytevector-length other))
              0
              (if (< (bytevector-length bytevector)
                     (bytevector-length other))
                  -1
                  1))
          (let ((delta (- (bytevector-u8-ref bytevector index)
                          (bytevector-u8-ref other index))))
            (if (zero? delta)
                (loop (+ 1 index))
                (if (negative? delta)
                    -1
                    1)))))))

(define (okvs-range-init store key)
  (let ((value (mapping-ref/default store key #f)))
    (if value
        (list (cons key value))
        '())))

(define (okvs-range transaction start-key start-include? end-key end-include? . args)
  (let* ((store (transaction-store transaction)))
    (let loop ((key (mapping-key-successor store start-key (const #f)))
               (out (if start-include?
                        (okvs-range-init store start-key)
                        '())))
      (if (not key)
          (list->generator (reverse! out))
          (case (lexicographic-compare key end-key)
            ((-1)
             (loop (mapping-key-successor store key (const #f))
                   (cons (cons key (mapping-ref/default store key #f)) out)))
            ((0)
             (if end-include?
                 (loop #f (cons (cons key (mapping-ref/default store key #f)) out))
                 (loop #f out)))
            ((1) (loop #f out)))))))

(define (strinc bytevector)
  "Return the first bytevector that is not prefix of BYTEVECTOR"
  ;; See https://git.io/fj34F, TODO: OPTIMIZE
  (let ((bytes (reverse! (bytevector->u8-list bytevector))))
    ;; strip #xFF
    (let loop ((out bytes))
      (when (null? out)
        (error 'okvs "Key must contain at least one byte not equal to #xFF." bytevector))
      (if (= (car out) #xFF)
          (loop (cdr out))
          (set! bytes out)))
    ;; increment first byte, reverse and return the bytevector
    (u8-list->bytevector (reverse! (cons (+ 1 (car bytes)) (cdr bytes))))))

(define (okvs-prefix transaction prefix . config)
  (apply okvs-range transaction prefix #t (strinc prefix) #f config))

;;; Commentary
;;
;; pack / unpack
;;

(define *null* '(null))

(define *null-code* #x00)
;; variable length
(define *bytes-code* #x01)
(define *string-code* #x02)
(define *symbol-code* #x03)
(define *nested-code* #x05)
;; integers
(define *neg-int-start* #x0B)
(define *int-zero-code* #x14)
(define *pos-int-end* #x1D)
;; double
(define *double-code* #x21)
;; true and false
(define *false-code* #x26)
(define *true-code* #x27)
(define *escape-code* #xFF)

;; pack

(define (struct:pack>Q integer)
  (let ((bytevector (make-bytevector 8 0)))
    (let loop ((index 0))
      (unless (= index 8)
        (bytevector-u8-set! bytevector index (bitwise-and
                                              (arithmetic-shift integer (- (* (- 7 index) 8)))
                                              #xFF))
        (loop (+ index 1))))
    bytevector))

(define (struct:unpack>Q bytevector)
  (let loop ((index 0)
             (out 0))
    (if (= index 8)
        out
        (loop (+ index 1)
              (+ out
                 (arithmetic-shift
                  (bytevector-u8-ref bytevector index)
                  (* (- 7 index) 8)))))))

(define (%%pack-bytes bv accumulator)
  (let loop ((index 0))
    (unless (= index (bytevector-length bv))
      (let ((byte (bytevector-u8-ref bv index)))
        (if (zero? byte)
            (begin ;; escape null byte
              (accumulator #x00)
              (accumulator *escape-code*))
            (accumulator byte))
        (loop (+ index 1)))))
  (accumulator #x00))

(define *bigish* (arithmetic-shift 1 (* 8 8)))

(define *limits*
  (let ((limits (make-vector 9)))
    (let loop ((index 0))
      (unless (= index 9)
        (vector-set! limits index (- (arithmetic-shift 1 (* index 8)) 1))
        (loop (+ index 1))))
    limits))

(define (bisect vector value)
  (let loop ((low 0)
             (high (vector-length vector)))
    (if (>= low high)
        low
        (let ((middle (quotient (+ low high) 2)))
          (if (< (vector-ref vector middle) value)
              (loop (+ middle 1) high)
              (loop low middle))))))

(define (%%pack-positive-integer integer accumulator)
  (if (< integer *bigish*)
      ;; small integer
      (let* ((length (integer-length integer))
             (n (exact (ceiling (/ length 8))))
             (bv (struct:pack>Q integer)))
        (accumulator (+ *int-zero-code* n))
        (let loop ((index (- (bytevector-length bv) n)))
          (unless (= index (bytevector-length bv))
            (accumulator (bytevector-u8-ref bv index))
            (loop (+ index 1)))))
      ;; big integer
      (let ((length (exact (floor (/ (+ (integer-length integer) 7) 8)))))
        (accumulator *pos-int-end*)
        (accumulator length)
        (let loop ((index (- length 1)))
          (unless (= index -1)
            (accumulator (bitwise-and (arithmetic-shift integer (- (* 8 index)))
                                      #xFF))
            (loop (- index 1)))))))

(define (%%pack-negative-integer integer accumulator)
  (if (< (- integer) *bigish*)
      ;; small negative integer
      (let* ((n (bisect *limits* (- integer)))
             (maxv (vector-ref *limits* n))
             (bv (struct:pack>Q (+ maxv integer))))
        (accumulator (- *int-zero-code* n))
        (let loop ((index (- (bytevector-length bv) n)))
          (unless (= index (bytevector-length bv))
            (accumulator (bytevector-u8-ref bv index))
            (loop (+ index 1)))))
      ;; big negative integer
      (let* ((length (exact (ceiling (/ (+ (integer-length integer) 7) 8))))
             (integer (+ integer (- (arithmetic-shift 1 (* length 8)) 1))))
        (accumulator *neg-int-start*)
        (accumulator (bitwise-xor length #xFF))
        (let loop ((index (- length 1)))
          (unless (= index -1)
            (accumulator (bitwise-and (arithmetic-shift integer (- (* 8 index)))
                                      #xFF))
            (loop (- index 1)))))))

(define (%%pack accumulator)
  (lambda (value)
    (cond
     ((eq? value *null*) (accumulator *null-code*))
     ((eq? value #t) (accumulator *true-code*))
     ((eq? value #f) (accumulator *false-code*))
     ((bytevector? value) (accumulator *bytes-code*) (%%pack-bytes value accumulator))
     ((string? value) (accumulator *string-code*) (%%pack-bytes (string->utf8 value) accumulator))
     ((symbol? value)
      (accumulator *symbol-code*)
      (%%pack-bytes (string->utf8 (symbol->string value)) accumulator))
     ;; integer
     ((and (number? value) (exact? value) (< value 0)) (%%pack-negative-integer value accumulator))
     ((and (number? value) (exact? value) (= value 0)) (accumulator *int-zero-code*))
     ((and (number? value) (exact? value) (> value 0)) (%%pack-positive-integer value accumulator))
     ;;
     (else (error 'pack "unsupported data type" value)))))

(define (%pack args accumulator)
  (for-each (%%pack accumulator) args))

(define (pack . args)
  (let ((accumulator (bytevector-accumulator)))
    (%pack args accumulator)
    (accumulator (eof-object))))

;; unpack

(define (list->bytevector list)
  (let ((vec (make-bytevector (length list) 0)))
    (let loop ((i 0) (list list))
      (if (null? list)
          vec
          (begin
            (bytevector-u8-set! vec i (car list))
            (loop (+ i 1) (cdr list)))))))

(define (unpack-bytes bv position)
  (let loop ((position position)
             (out '()))
    (if (zero? (bytevector-u8-ref bv position))
        (cond
         ;; end of bv
         ((= (+ position 1) (bytevector-length bv))
          (values (list->bytevector (reverse! out)) (+ position 1)))
         ;; escaped null bytes
         ((= (bytevector-u8-ref bv (+ position 1)) *escape-code*)
          (loop (+ position 2) (cons #x00 out)))
         ;; end of string
         (else (values (list->bytevector (reverse! out)) (+ position 1))))
        ;; just a byte
        (loop (+ position 1) (cons (bytevector-u8-ref bv position) out)))))

(define (unpack-positive-integer bv code position)
  (let* ((n (- code 20))
         (sub (make-bytevector 8 0)))
    (let loop ((index 0))
      (unless (= index n)
        (bytevector-u8-set! sub (+ (- 8 n) index) (bytevector-u8-ref bv (+ position 1 index)))
        (loop (+ index 1))))
    (values (struct:unpack>Q sub) (+ position 1 n))))

(define (unpack-negative-integer bv code position)
  (let* ((n (- 20 code))
         (maxv (vector-ref *limits* n))
         (sub (make-bytevector 8 0)))
    (let loop ((index 0))
      (unless (= index n)
        (bytevector-u8-set! sub (+ (- 8 n) index) (bytevector-u8-ref bv (+ position 1 index)))
        (loop (+ index 1))))
    (values (- (struct:unpack>Q sub) maxv) (+ position 1 n))))

(define (unpack-bigish-positive-integer bv code position)
  (let ((length (bytevector-u8-ref bv (+ position 1))))
    (values (let loop ((range (iota length))
                       (out 0))
              (if (null? range)
                  out
                  (loop (cdr range) (+ (arithmetic-shift out 8)
                                       (bytevector-u8-ref bv (+ position 2 (car range)))))))
            (+ position 2 length))))

(define (unpack-bigish-negative-integer bv code position)
  (let ((length (bitwise-xor (bytevector-u8-ref bv (+ position 1)) #xFF)))
    (values (let loop ((range (iota length))
                       (out 0))
              (if (null? range)
                  (+ (- out (arithmetic-shift 1 (* length 8))) 1)
                  (loop (cdr range) (+ (arithmetic-shift out 8)
                                       (bytevector-u8-ref bv (+ position 2 (car range)))))))
            (+ position 2 length))))

(define (unpack bv)
  (let loop ((position 0)
             (out '()))
    (if (= position (bytevector-length bv))
        (reverse! out)
        (let ((code (bytevector-u8-ref bv position)))
          (cond
           ;; null, true, false and zero
           ((= code *null-code*) (loop (+ position 1) (cons *null* out)))
           ((= code *true-code*) (loop (+ position 1) (cons #t out)))
           ((= code *false-code*) (loop (+ position 1) (cons #f out)))
           ((= code *int-zero-code*) (loop (+ position 1) (cons 0 out)))
           ;; variable length
           ((= code *bytes-code*)
            (call-with-values (lambda () (unpack-bytes bv (+ position 1)))
              (lambda (value position) (loop position (cons value out)))))
           ((= code *string-code*)
            (call-with-values (lambda () (unpack-bytes bv (+ position 1)))
              (lambda (value position) (loop position (cons (utf8->string value) out)))))
           ((= code *symbol-code*)
            (call-with-values (lambda () (unpack-bytes bv (+ position 1)))
              (lambda (value position) (loop position (cons (string->symbol (utf8->string value)) out)))))
           ;; integers
           ((and (> code *int-zero-code*) (< code *pos-int-end*))
            (call-with-values (lambda () (unpack-positive-integer bv code position))
              (lambda (value position) (loop position (cons value out)))))
           ((and (> code *neg-int-start*) (< code *int-zero-code*))
            (call-with-values (lambda () (unpack-negative-integer bv code position))
              (lambda (value position) (loop position (cons value out)))))
           ((= code *pos-int-end*)
            (call-with-values (lambda () (unpack-bigish-positive-integer bv code position))
              (lambda (value position) (loop position (cons value out)))))
           ((= code *neg-int-start*)
            (call-with-values (lambda () (unpack-bigish-negative-integer bv code position))
              (lambda (value position) (loop position (cons value out)))))
           ;; oops
           (else (error 'unpack "unsupported code" code)))))))

;;; Commentary
;;
;; SRFI-168: nstore
;;

;; helpers

(define (permutations s)
  ;; http://rosettacode.org/wiki/Permutations#Scheme
  (cond
   ((null? s) '(()))
   ((null? (cdr s)) (list s))
   (else ;; extract each item in list in turn and permutations the rest
    (let splice ((l '()) (m (car s)) (r (cdr s)))
      (append
       (map (lambda (x) (cons m x)) (permutations (append l r)))
       (if (null? r) '()
           (splice (cons m l) (car r) (cdr r))))))))

(define (combination k lst)
  (cond
   ((= k 0) '(()))
   ((null? lst) '())
   (else
    (let ((head (car lst))
          (tail (cdr lst)))
      (append (map (lambda (y) (cons head y)) (combination (- k 1) tail))
              (combination k tail))))))

(define (combinations lst)
  (if (null? lst) '(())
      (let* ((head (car lst))
             (tail (cdr lst))
             (s (combinations tail))
             (v (map (lambda (x) (cons head x)) s)))
        (append s v))))

;; make-indices will compute the minimum number of indices/tables
;; required to bind any pattern in one hop. The math behind this
;; computation is explained at:
;;
;;   https://math.stackexchange.com/q/3146568/23663
;;
;; make-indices will return the minimum list of permutations in
;; lexicographic order of the base index ie. (iota n) where n is
;; the length of ITEMS ie. the n in nstore.

(define (prefix? lst other)
  "Return #t if LST is prefix of OTHER"
  (let loop ((lst lst)
             (other other))
    (if (null? lst)
        #t
        (if (= (car lst) (car other))
            (loop (cdr lst) (cdr other))
            #f))))

(define (permutation-prefix? c o)
  (any (lambda (p) (prefix? p o)) (permutations c)))

(define (ok? combinations candidate)
  (every (lambda (c) (any (lambda (p) (permutation-prefix? c p)) candidate)) combinations))

(define (findij L)
  (let loop3 ((x L)
              (y '()))
    (if (or (null? x) (null? (cdr x)))
        (values #f (append (reverse! y) x) #f #f)
        (if (and (not (cdr (list-ref x 0))) (cdr (list-ref x 1)))
            (values #t
                    (append (cddr x) (reverse! y))
                    (car (list-ref x 0))
                    (car (list-ref x 1)))
            (loop3 (cdr x) (cons (car x) y))))))

(define (lex< a b)
  (let loop ((a a)
             (b b))
    (if (null? a)
        #t
        (if (not (= (car a) (car b)))
            (< (car a) (car b))
            (loop (cdr a) (cdr b))))))

(define (make-indices n)
  ;; This is based on:
  ;;
  ;;   https://math.stackexchange.com/a/3146793/23663
  ;;
  (let* ((tab (iota n))
         (cx (combination (floor (/ n 2)) tab)))
    (let loop1 ((cx cx)
                (out '()))
      (if (null? cx)
          (begin (assume (ok? (combinations tab) out))
                 (list-sort lex< out))
          (let loop2 ((L (map (lambda (i) (cons i (not (not (memv i (car cx)))))) tab))
                      (a '())
                      (b '()))
            (call-with-values (lambda () (findij L))
              (lambda (continue? L i j)
                (if continue?
                    (loop2 L (cons j a) (cons i b))
                    (loop1 (cdr cx)
                           (cons (append (reverse! a) (map car L) (reverse! b))
                                 out))))))))))

(define-record-type <engine>
  (nstore-engine ref set! delete! prefix)
  engine?
  (ref engine-ref)
  (set! engine-set!)
  (delete! engine-delete!)
  (prefix engine-prefix))

(define-record-type <nstore>
  (make-nstore engine prefix prefix-length indices n)
  nstore?
  (engine nstore-engine-ref)
  (prefix nstore-prefix)
  (prefix-length nstore-prefix-length)
  (indices nstore-indices)
  (n nstore-n))

(define (nstore engine prefix items)
  (make-nstore engine prefix (length prefix) (make-indices (length items)) (length items)))

(define nstore-ask?
  (lambda (transaction nstore items)
    (assume (= (length items) (nstore-n nstore)))
    ;; indices are sorted in lexicographic order, that is the first
    ;; index is always (iota n) also known as the base index. So that
    ;; there is no need to permute ITEMS.  zero in the following
    ;; cons* is the index of the base index in nstore-indices
    (let ((key (apply pack (append (nstore-prefix nstore) (list 0) items))))
      (not (not ((engine-ref (nstore-engine-ref nstore)) transaction key))))))

(define true (pack #t))

(define (make-tuple list permutation)
  ;; Construct a permutation of LIST based on PERMUTATION
  (let ((tuple (make-vector (length permutation))))
    (for-each (lambda (index value) (vector-set! tuple index value)) permutation list)
    (vector->list tuple)))

(define (permute items index)
  ;; make-tuple reverse operation
  (let ((items (list->vector items)))
    (let loop ((index index)
               (out '()))
      (if (null? index)
          (reverse! out)
          (loop (cdr index)
                (cons (vector-ref items (car index)) out))))))

(define nstore-add!
  (lambda (transaction nstore items)
    (assume (= (length items) (nstore-n nstore)))
    (let ((engine (nstore-engine-ref nstore))
          (nstore-prefix (nstore-prefix nstore)))
      ;; add ITEMS into the okvs and prefix each of the permutation
      ;; of ITEMS with the nstore-prefix and the index of the
      ;; permutation inside the list INDICES called SUBSPACE.
      (let loop ((indices (nstore-indices nstore))
                 (subspace 0))
        (unless (null? indices)
          (let ((key (apply pack (append nstore-prefix
                                         (list subspace)
                                         (permute items (car indices))))))
            ((engine-set! engine) transaction key true)
            (loop (cdr indices) (+ 1 subspace))))))))

(define nstore-delete!
  (lambda (transaction nstore items)
    (assume (= (length items) (nstore-n nstore)))
    (let ((engine (nstore-engine-ref nstore))
          (nstore-prefix (nstore-prefix nstore)))
      ;; Similar to the above but remove ITEMS
      (let loop ((indices (nstore-indices nstore))
                 (subspace 0))
        (unless (null? indices)
          (let ((key (apply pack (append nstore-prefix
                                         (list subspace)
                                         (permute items (car indices))))))
            ((engine-delete! engine) transaction key)
            (loop (cdr indices) (+ subspace 1))))))))

(define-record-type <nstore-var>
  (nstore-var name)
  nstore-var?
  (name nstore-var-name))

(define (bind* pattern tuple seed)
  ;; associate variables of PATTERN to value of TUPLE with SEED.
  (let loop ((tuple tuple)
             (pattern pattern)
             (out seed))
    (if (null? tuple)
        out
        (if (nstore-var? (car pattern)) ;; only bind variables
            (loop (cdr tuple)
                  (cdr pattern)
                  (hashmap-set out
                               (nstore-var-name (car pattern))
                               (car tuple)))
            (loop (cdr tuple) (cdr pattern) out)))))

(define (pattern->combination pattern)
  (let loop ((pattern pattern)
             (index 0)
             (out '()))
    (if (null? pattern)
        (reverse! out)
        (loop (cdr pattern)
              (+ 1 index)
              (if (nstore-var? (car pattern))
                  out
                  (cons index out))))))

(define (pattern->index pattern indices)
  ;; Retrieve the index that will allow to bind pattern in one
  ;; hop. This is done by getting all non-variable items of the
  ;; pattern and looking up the first index that is
  ;; permutation-prefix
  (let ((combination (pattern->combination pattern)))
    (let loop ((indices indices)
               (subspace 0))
      (if (null? indices)
          (error 'nstore "oops!")
          (if (permutation-prefix? combination (car indices))
              (values (car indices) subspace)
              (loop (cdr indices) (+ subspace 1)))))))

(define (pattern->prefix pattern index)
  ;; Return the list that correspond to INDEX, that is the items
  ;; of PATTERN that are not variables. This is used as the prefix
  ;; for the range query done later.
  (let loop ((index index)
             (out '()))
    (let ((v (list-ref pattern (car index))))
      (if (nstore-var? v)
          (reverse! out)
          (loop (cdr index) (cons v out))))))

(define (%from transaction nstore pattern seed config)
  (call-with-values (lambda () (pattern->index pattern (nstore-indices nstore)))
    (lambda (index subspace)
      (let ((prefix (append (nstore-prefix nstore)
                            (list subspace)
                            (pattern->prefix pattern index)))
            (engine (nstore-engine-ref nstore)))
        (gmap (lambda (pair)
                (bind* pattern
                       (make-tuple (drop (unpack (car pair))
                                         (+ (nstore-prefix-length nstore) 1))
                                   index)
                       seed))
              ((engine-prefix engine) transaction (apply pack prefix) config))))))

(define nstore-from
  (case-lambda
    ((transaction nstore pattern)
     (assume (= (length pattern) (nstore-n nstore)))
     (%from transaction nstore pattern (hashmap (make-eq-comparator)) '()))
    ((transaction nstore pattern config)
     (assume (= (length pattern) (nstore-n nstore)))
     (%from transaction nstore pattern (hashmap (make-eq-comparator)) config))))

(define (pattern-bind pattern seed)
  ;; Return a pattern where variables that have a binding in seed
  ;; are replaced with the associated value. In pratice, most of
  ;; the time, it is the same pattern with less variables.
  (map (lambda (item) (or (and (nstore-var? item)
                               (hashmap-ref/default seed
                                                    (nstore-var-name item)
                                                    #f))
                          item))
       pattern))

(define (gscatter generator)
  ;; Return a generator that yields the elements of the generators
  ;; produced by the given GENERATOR. Same as gflatten but
  ;; GENERATOR contains other generators instead of lists.
  (let ((state eof-object))
    (lambda ()
      (let ((value (state)))
        (if (eof-object? value)
            (let loop ((new (generator)))
              (if (eof-object? new)
                  new
                  (let ((value (new)))
                    (if (eof-object? value)
                        (loop (generator))
                        (begin (set! state new)
                               value)))))
            value)))))

(define nstore-where
  (lambda (transaction nstore pattern)
    (assume (= (length pattern) (nstore-n nstore)))
    (lambda (from)
      (gscatter
       (gmap (lambda (bindings) (%from transaction
                                       nstore
                                       (pattern-bind pattern bindings)
                                       bindings
                                       '()))
             from)))))

(define-syntax nstore-query
  (syntax-rules ()
    ((_ value) value)
    ((_ value f rest ...)
     (nstore-query (f value) rest ...))))


;;; Commentary
;;
;; TODO: add something insightful
;;

(define triplestore
  (let ((engine (nstore-engine okvs-ref okvs-set! okvs-delete! okvs-prefix)))
    (nstore engine '() '(uid key value))))

(define database (okvs #t))

;; ask
(pk (okvs-in-transaction
     database
     (lambda (transaction)
       (nstore-ask? transaction triplestore '("P4X432" blog/title "hyper.dev")))))

;; add
(okvs-in-transaction
 database
 (lambda (transaction)
   (nstore-add! transaction triplestore '("P4X432" blog/title "hyper.dev"))))

;; ask
(pk (okvs-in-transaction
     database
     (lambda (transaction)
       (nstore-ask? transaction triplestore '("P4X432" blog/title "hyper.dev")))))


(define (make-node tag options children)
  `(@ (tag . ,tag)
      (options . ,(cons '@ options))
      (children . ,children)))


(define (magic attrs next-identifier)
  ;; shake around the attrs to make them compatible with
  ;; react-hyperscript options, associate callbacks to integer
  ;; identifiers. The event on a given node is associated with an
  ;; integer, the integer is associated with a callback
  ;; procedure. Return both react-hyperscript options and
  ;; integer-to-callback alist named `callbacks`.
  (let loop ((attrs attrs)
             (next-identifier next-identifier)
             (out '())
             (callbacks '()))
    (if (null? attrs)
        (values out callbacks)
        (match attrs
          (((key value) rest ...)
           (if (procedure? value)
               (loop rest
                     (+ 1 next-identifier)
                     (acons key next-identifier out)
                     (acons next-identifier value callbacks))
               (loop rest
                     next-identifier
                     (acons key value out)
                     callbacks)))))))

(define (%sxml->hyperscript+callbacks sxml callbacks)
  (match sxml
    ((? string? string)
     (values string '()))
    ((tag ('@ attrs ...) rest ...)
     (call-with-values (lambda () (magic attrs (length callbacks)))
       (lambda (attrs new-callbacks)
         (let loop ((callbacks (append callbacks new-callbacks))
                    (rest rest)
                    (out '()))
           (if (null? rest)
               (values (make-node tag attrs (reverse out)) callbacks)
               (call-with-values (lambda () (%sxml->hyperscript+callbacks (car rest) callbacks))
                 (lambda (hyperscript new-callbacks)
                   (loop (append callbacks new-callbacks)
                         (cdr rest)
                         (cons hyperscript out)))))))))
    ((tag rest ...)
     ;; there is no magic but almost the same as above loop.
     (let loop ((callbacks callbacks)
                (rest rest)
                (out '()))
       (if (null? rest)
           (values (make-node tag '() (reverse out)) callbacks)
           (call-with-values (lambda () (%sxml->hyperscript+callbacks (car rest) callbacks))
             (lambda (hyperscript callbacks)
               (loop callbacks (cdr rest) (cons hyperscript out)))))))))

(define (sxml->hyperscript+callbacks sxml)
  (%sxml->hyperscript+callbacks sxml '()))

;;; style helpers:

;; make-style: translate css styles to reactjs styles

(define (->reactjs symbol)
  (let loop ((chars (string->list (symbol->string symbol)))
             (out '()))
    (if (null? chars)
        (string->symbol (list->string (reverse out)))
        (if (char=? (car chars) #\-)
            (loop (cddr chars) (cons (char-upcase (cadr chars)) out))
            (loop (cdr chars) (cons (car chars) out))))))

(define (%make-style alist)
  (let loop ((alist alist)
             (out '()))
    (if (null? alist)
        out
        (loop (cdr alist) (acons (->reactjs (caar alist)) (cdar alist) out)))))

(define (make-style alist)
  (cons '@ (%make-style alist)))

;; override

(define (%%merge first second)
  (let loop ((second second)
             (out first))
    (if (null? second)
        out
        (loop (cdr second) (set out (caar second) (cdar second))))))

(define (%merge first rest)
  (let loop ((rest rest)
             (out first))
    (if (null? rest)
        out
        (loop (cdr rest) (%%merge out (car rest))))))

(define (merge first second . other)
  (%merge first (cons second other)))

(define (recv-from-javascript)
  (json->sexp (string-eval-script "document.scheme_inbox")))

(define (send-to-javascript! obj)
  (eval-script! (string-append "document.javascript_inbox = " (sexp->json obj) ";")))

(define (render! model)
  (let ((sxml (view model)))
    (call-with-values (lambda () (sxml->hyperscript+callbacks sxml))
      (lambda (hyperscript callbacks)
        (send-to-javascript! (list "patch" hyperscript))
        callbacks))))

(define (xhr method path obj)
  (abort-to-prompt (list "xhr" (list method path obj))))

(define (update model callbacks event)
  (let* ((event* event)
         (identifier (ref event* 'identifier)))
    (let ((callback (ref callbacks identifier)))
      (callback model event*))))

(define (create-app init view)
  (let ((model (init)))
    (let loop1 ()
      (let ((callbacks (render! model)))
        (wait-on-event!) ;; yields control back to the browser
        (let loop2 ((event (recv-from-javascript))
                    (k #f))
          (cond
           ((and (string=? (car event) "xhr") k)
            (k (cadr event)))
           ((and (string=? (car event) "xhr") (not k))
            (error "Oops! Should not happen"))
           ((string=? (car event) "event")
            (when k
              (pk "User, your wish is my command!..."))
            (call-with-prompt
             (lambda ()
               (let ((new-model (update model callbacks (cadr event))))
                 (set! model new-model)
                 (loop1)))
             (lambda (k obj)
               (send-to-javascript! obj)
               (wait-on-event!)
               (loop2 (recv-from-javascript) k))))))))))

;; app

(define (eval-string string)
  (eval (string->scm string) (environment '(scheme base))))

(define (init)
  '((index . 0)
    (input . "")
    (convo . ())))

(define intro "Learning a new language is long adventure of correct and wrong.  Here through this interface that mimics an REPL you will learn Scheme programming language.")

(define exercices
  '(("What is (+ 41 1)" . 42)
    ("What is (+ 1 99 1)" . 101)
    ("What is (* 2 3 4)" . 24)
    ("What is (+ (* 100 10) 330 7)" . 1337)
    ("Err!!!..." '(please-fix-the-bug))))

(define (make-stdout string)
  `(div (@ (className "stdout")) ,(string-append ";; " string)))

(define (make-stdin string)
  `(div (@ (className "stdin")) ,string))

(define (onChange model event)
  (let ((input (ref (ref event 'event) 'target.value)))
    (set model 'input input)))

(define (clear-input model)
  (set model 'input ""))

(define (next-exercice model)
  (let* ((input (ref model 'input))
         (convo (ref model 'convo))
         (index (ref model 'index))
         (exercice (car (list-ref exercices index))))
    (let ((new (append convo (list (list exercice input "Ok!")))))
      (clear-input (set (set model 'convo new) 'index (+ 1 index))))))

(define (retry-exercice model)
  (let* ((input (ref model 'input))
         (convo (ref model 'convo))
         (index (ref model 'index))
         (exercice (car (list-ref exercices index))))
    (let ((new (append convo (list (list exercice input "Wrong?!")))))
      (clear-input (set model 'convo new)))))

(define (onSubmit model event)
  (pk "proof xhr GET foo.json works!" (xhr "GET" "foo.json" '()))
  (call/cc
   (lambda (k)
     (with-exception-handler
      (lambda _
        (k (retry-exercice model)))
      (lambda ()
        (let ((out (eval-string (ref model 'input))))
          (if (equal? out (cdr (list-ref exercices (ref model 'index))))
              (next-exercice model)
              (retry-exercice model))))))))


(define input-style '((marginTop . "15px")))

(define (view model)
  `(div
    ,(make-stdout intro)
    ,@(let loop ((convo (ref model 'convo))
                 (out '()))
        (match convo
          ('() out)
          (((exercice input response) rest ...)
           (loop rest
                 (append out (list (make-stdout exercice)
                                   (make-stdin input)
                                   (make-stdout response)))))))
    ,(make-stdout (car (list-ref exercices (ref model 'index))))
    (form (@ (onSubmit ,onSubmit))
          (input (@ (id "input")
                    (style ,(make-style input-style))
                    (autoFocus #t)
                    (type "text")
                    (value ,(ref model 'input))
                    (onChange ,onChange))))))

(create-app init view)

;; everything that follows is dead code
