(import (scheme base))
(import (scheme char))
(import (scheme eval))
(import (scheme read))
(import (scheme write))


(import (chibi emscripten))
(import (chibi match))
(import (chibi parse))


(write-string "Chibi Scheme is running...\n")

(eval-script! "document.resume = Module['resume']")

;; scheme helpers

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

;; parse json
;;
;; MIT License
;;
;; Copyright (c) 2018 Thunk NYC Corp.
;;
;; https://github.com/thunknyc/scm-json/blob/master/LICENSE
;;

(define-grammar json
  (space ((* ,(parse-char char-whitespace?))))

  ;;> The number parser is currently quite primitive; it reads a
  ;;> sequence of characters matching [-+0-9eE,.] and attempts to
  ;;> parse it as a Scheme number.

  (number ((-> n (+ (or ,(parse-char char-numeric?)
                        #\. #\- #\+ #\e #\E)))
           (string->number (list->string n))))

  (string ((: ,(parse-char #\")
              (-> s (* ,(parse-not-char #\")))
              ,(parse-char #\"))
           (list->string s)))

  (atom ((-> n ,number) n)
        ((-> s ,string) s)
        ("true" #t)
        ("false" #f))

  (datum ((or ,atom ,array ,hash)))

  (array-el ((: "," ,space (-> el ,datum)) el))

  (array ((: "[" ,space (-> el ,datum) ,space
             (-> els (* ,array-el)) ,space "]")
          (apply vector el els))
         ((: "[" ,space "]") (vector)))

  (hash-el ((: "," ,space (-> k ,string) ,space
               ":" ,space (-> v ,datum)) (cons (string->symbol k) v)))

  (hash ((: "{" ,space (-> k ,string) ,space
            ":" ,space (-> v ,datum) ,space
            (-> els (* ,hash-el)) ,space "}")
         (apply list (cons (string->symbol k) v) els))
        ((: "{" ,space "}") '()))

  (object ((: ,space (-> o ,datum) ,space) o)))

;;> Call the JSON parser on the \scheme{(chibi parse)} parse stream
;;> \var{source}, at index \var{index}, and return the result, or
;;> \scheme{#f} if parsing fails.

(define (json->sexp source . o)
  (let ((index (if (pair? o) (car o) 0)))
    (parse object source index)))

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

(define (sexp->json sexp)
  (match sexp
    (#f "false")
    (#t "true")
    ('() "undefined")
    (('@ rest ...) (assoc->json rest))
    ((? pair? sexp) (list->json sexp))
    ((? symbol? sexp) (string-append "\"" (symbol->string sexp) "\""))
    ((? number? sexp) (number->string sexp))
    ((? string? sexp) (string-append "\"" sexp "\""))))

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
           ((and (string=? (vector-ref event 0) "xhr") k)
            (k (vector-ref event 1)))
           ((and (string=? (vector-ref event 0) "xhr") (not k))
            (error "Oops! Should not happen"))
           ((string=? (vector-ref event 0) "event")
            (when k
              (pk "User, your wish is my command!..."))
            (call-with-prompt
             (lambda ()
               (let ((new-model (update model callbacks (vector-ref event 1))))
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
