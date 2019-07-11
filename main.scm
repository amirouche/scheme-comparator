(import (scheme base))
(import (scheme char))
(import (scheme charset))
(import (scheme cxr))
(import (scheme eval))
(import (scheme list))
(import (scheme read))
(import (scheme write))

(import (chibi emscripten))
(import (chibi match))
(import (chibi parse))


(write-string "Chibi Scheme is running...\n")

(eval-script! "document.resume = Module['resume']")

;; scheme helpers

(define-syntax define-syntax-rule
  (syntax-rules ()
    ((define-syntax-rule (keyword args ...) body)
     (define-syntax keyword
       (syntax-rules ()
         ((keyword args ...) body))))))

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
