;;1.1
;;input -> printed by interpreter
;;10 -> 10
;;(+ 5 3 4) -> 12
;;(- 9 1) -> 8
;;(/ 6 2) -> 3
;;(+ (* 2 4) (- 4 6)) -> 6
;;(define a 3) -> nothing
;;(define b (+ a 1)) -> nothing
;;(+ a b (* a b)) -> 19
;;(= a b) -> #f
;;(if (and (< b a) (< b (* a b)))
;;	b
;;	a) -> 3
;;(cond ((= a 4) 6)
;;	  ((= b 4) (+ 6 7 a))
;;	  (else 25)) -> 16
;;(+ 2 (if (> b a) b a)) -> 6
;;(* (cond ((> a b) a)
;;		 ((< a b) b)
;;		 (else -1))
;;   (+ a 1)) -> 16
   
;;1.2
(/ (+ 5 4 (- 2 (- 3 (+ 6 (/ 4 5))))) (* 3 (- 6 2) (- 2 7)))

;;1.3
(define (square a) (* a a))
(define (sum-of-squares a b) (+ (square a) (square b)))
(define (one-point-three a b c) 
        (if (and (< a b) (< a c)) (sum-of-squares b c)
                 (if (and (< b a) (< b c)) (sum-of-squares a c)
                     (if (and (< c b) (< c a)) (sum-of-squares a b) -1))))
					 
;;1.4
;;if b is positive, then the if statement will return +, which allows for the expression (+ a b) to be formed.
;;if b is negative, a - is returned instead, thus we have (- a b), which is effectively a + |b|

;;1.5 (review)
;;(define (p) (p))
;;(define (test x y)
;;  (if (= x 0)
;;      0
;;      y))
;;applicative order: this will result in an infinite loop
;;why? p is infinitely expanded to itself
;;applicative order has two steps
;;1. evaluate the subexpressions of the combination (until there are no more subexpressions)
;;2. apply the operator to the operands
;;i.e. recursion
;;so we have that:
;;(test 0 (p))
;;successfully expands the procedure `test`, doesn't need to expand `0` and fails to expand the procedure `p`
;;it fails because the procedure `p` never terminates
;;normal order: this will result in 0 being returned
;;why?
;;(test 0 (p))
;;(if (= 0 0) 0 (p))
;;(if #t 0 (p))
;;0

;;1.6
;;the program will run out of memory, as it will loop endlessly
;;the hint is the previous exercise
;;if is a special form because it is not subject to applicative-order evaluation
;;new-if follows applicative substitution, and for that reason, we loop
;;(i.e. it keeps calling sqrt-iter, which only _approximates_ the sqrt, never reaching it)

;;1.7
;;for 0.0...01 and 10...0 it doesn't produce the correct guess because of the tolerance
;;using the alternate strategy only makes it marginally more precise
;;the alternate strategies:
;;[using the "real computers" hint; uses the system precision]
(define (good-enough? guess x)
	    (= (improve guess x) guess))

;;[using the "look at difference between iterations" hint]
(define (good-enough? guess x)
  (< (abs (- (improve guess x) guess)) (* guess 0.001)))
		
;;1.8
(define (square x) (* x x))

(define (improve y x)
  (/ (+ (/ x (square y)) (* 2 y)) 3))

(define (good-enough? guess x)
	    (= (improve guess x) guess))

(define (qbrt-iter guess x)
  (if (good-enough? guess x)
      guess
      (qbrt-iter (improve guess x)
                 x)))

(define (qbrt x)
  (qbrt-iter 1.1 x))

;;1.9
;;p15 p36
;;(+ 4 5)
;;a!=0 so
;;(inc (+ (dec 4) 5)))
;;(inc (+ 3 5))
;;(+ 3 5)
;;a!=0 so
;;(inc (+ (dec 3) 5)))
;;(inc (+ 2 5))
;;(+ 2 5)
;;a!=0 so
;;(inc (+ (dec 2) 5)))
;;(inc (+ 1 5))
;;(+ 1 5)
;;a!=0 so
;;(inc (+ (dec 1) 5)))
;;(inc (+ 0 5))
;;a==0 so b
;;5
;;(inc 5)
;;6
;;(inc 6)
;;7
;;(inc 7)
;;8
;;(inc 8)
;;9

;;the first procedure is linear recursive


;;(+ 4 5)
;;a!=0 so
;;(+ (dec 4) (inc 5)))
;;(+ 3 6)
;;a!=0 so
;;(+ (dec 3) (inc 6)))
;;(+ 2 7)
;;a!=0 so
;;(+ (dec 2) (inc 7)))
;;(+ 1 8)
;;a!=0 so
;;(+ (dec 1) (inc 8)))
;;(+ 0 9)
;;a==0 so
;;9

;;the second procedure is linear iterative

;;1.10
;;Ackermann's function
;;(A 1 10)
;;x!=0 && y!=0 && y!=1 so
;;(A (0) (A 1 (9)))
;;(* 2 (A (0) (A 1 (8))))
;;(* 2 (* 2 (A (0) (A 1 (7)))))
;;(* 2 (* 2 (* 2 (A (0) (A 1 (6))))))
;;(* 2 (* 2 (* 2 (* 2 (A (0) (A 1 (5)))))))
;;...
;;(* 2 (* 2 (* 2 (* 2 (* 2 (* 2 (* 2 (* 2 (A (0) (A 1 (1)))))))))))))
;;(* 2 (* 2 (* 2 (* 2 (* 2 (* 2 (* 2 (* 2 (* 2 (2))))))))))))))
;;1024

;;(A 2 4)
;;(A 1 (A 2 3)
;;(A 0 (- (A 2 3) 1)
;;(* 2 (- (A 2 3) 1)
;;(* 2 (- (A 1 (A 2 2)) 1)
;;(* 2 (- (A 0 (- (A 2 2) 1)) 1)
;;(* 2 (- (* 2 (- (A 2 2) 1)) 1)
;;(* 2 (- (* 2 (- (A 1 (A 2 1)) 1)) 1)
;;(* 2 (- (* 2 (- (A 1 (2)) 1)) 1)
;;(* 2 (- (* 2 (- (A 0 (A 1 2)) 1)) 1)
;;(* 2 (- (* 2 (- (* 2 (A 1 2)) 1)) 1)
;;(* 2 (- (* 2 (- (* 2 (*2 (2))) 1)) 1)
;;(* 2 (- (* 2 (- (* 2 (4)) 1)) 1)
;;(* 2 (- (* 2 (- (8) 1)) 1)
;;(* 2 (- (* 2 (7)) 1)
;;(* 2 (- (14) 1)
;;(* 2 (13))
;;26
;;wrong, ans=65536
;;(A 2 4)
;;(A 1 (A 2 3))
;;(A 1 (A 1 (A 2 2)))
;;(A 1 (A 1 (A 1 (A 2 1))))
;;(A 1 (A 1 (A 1 2)))
;;(A 1 (A 1 (A 0 (A 1 1))))
;;(A 1 (A 1 (A 0 2)))
;;(A 1 (A 1 4))
;;(A 1 (A 0 (A 1 3)))
;;(A 1 (A 0 (A 0 (A 1 2))))
;;(A 1 (A 0 (A 0 (A 0 (A 1 1)))))
;;(A 1 (A 0 (A 0 (A 0 2))))
;;(A 1 (A 0 (A 0 4)))
;;(A 1 (A 0 8))
;;(A 1 16)
;;2^16
;;(from answer guide)

;;(A 3 3)
;;(A 2 (A 3 2))
;;(A 1 (- (A 3 2) 1))
;;(A 0 (- (A 3 2) 2))
;;(* 2 (- (A 3 2) 2))
;;(* 2 (- (A 2 (A 2 2)) 2))
;;(* 2 (- (A 1 (- (A 2 2) 1))2))
;;(* 2 (- (A 0 (- (A 2 2) 2))2))
;;(* 2 (- (* 2 (- (A 2 2) 2))2))
;;(* 2 (- (* 2 (- (A 1 (A 1 2)) 2))2))
;;messed up somewhere here, restart
;;ans=65536
;;(A 3 3)
;;(A 2 (A 3 2))
;;(A 2 (A 2 (A 3 1)))
;;(A 2 (A 2 2))
;;(A 2 (A 1 (A 2 1)))
;;(A 2 (A 1 2))
;;(A 2 (A 0 (A 1 1))
;;(A 2 (A 0 2))
;;(A 2 4)
;;thus we have 65536

(define (f n) (A 0 n))
;;f(n) = 2n
(define (g n) (A 1 n))
;;g(n) = 2^n
(define (k n) (A 2 n))
;;k(n) = 2^n^2


;;notes on the count-change procedure
;;all combinations of change without using first coin
;;plus
;;all combinations of change for amount minus value of first coin
;;this logic is contained in the else clause
;;in which we have
;;the sum of
;;cc amount (kinds-of-coins - 1) // without first coin
;;cc (amount - first coin) kinds-of-coin


;;1.11
;;f(n) = n if n < 3
;;f(n) = f(n-1) + 2f(n-2) + 3f(n-3) if n > 3

;;recursive procedure:
(define (one-eleven-rec n)
  (cond ((< n 3) n)
        ((> n 2)
         (+ (one-eleven-rec (- n 1))
            (* 2 (one-eleven-rec (- n 2)))
            (* 3 (one-eleven-rec (- n 3)))))))

;;iterative procedure
;;the essential question here is how many state variables do i need
;;current status:
(define (f n)
  (one-eleven-iter 0 0 n))
(define (one-eleven-iter count sum n) 1)
;;nb
;;how many iterations?
;;no, the right question is what is the transformation?
;;three moving parts:
;;a b c
;;a -> (a + 2b + 3c)
;;b -> a
;;c -> b

;;the solution from sicp-solutions:
 (define (f n) 
   (define (f-i a b c count) 
     (cond ((< n 3) n) 
           ((<= count 0) a) 
           (else (f-i (+ a (* 2 b) (* 3 c)) a b (- count 1))))) 
   (f-i 2 1 0 (- n 2))) 

;;a walkthrough:
;;f-i means iter
;;because the procedure is defined in the scope of f, we can use n
;;we use n as the count here
;;so if n is less than 3, return n as specified by the function definition
;;if count is 0, return a, the first term
;;else
;;modify b and c as specified by the function, then sum the terms
;;this sum takes the place of a as specified by the transformation
;;a takes place of b and b takes place of c
;;decrement the count by one

;;1.12
;;pascals triangle
;;nb. just the elements, not the elements in the shape of the triangle
;;each number is sum of two numbers above it
;;current implementation ripped from online and translated to r5rs:
(define (pascal row col)
  (if (and (= 0 row) (= 0 col)) 1
   (+ (pascal (- row 1) col)
      (pascal (- row 1) (- col 1)))))
;;runs out of memory for all but (pascal 0 0)
;;it's right but most implementations run out of memory fast
;;this is the best solution imo from sicp-solutions
 (define (pascal col depth) 
   (cond  
     ((= col 0) 1) 
     ((= col depth) 1) 
     (else (+ (pascal (- col 1) (- depth 1))  
              (pascal col ( - depth 1)))))) 
;;very similar to the one i found

;;1.13
;;Prove that Fib(n) is the closest integer to phi^n/sqrt(5) where phi=(1+sqrt(5))/2. By induction.

;;Let psi = (1-sqrt(5))/2
;;We observe that the definition of the fibonacci numbers is
;;0 if n = 0
;;1 if n = 1
;;Fib(n-1) + Fib(n-2) otherwise
;;WTS Fib(n) = (phi^n - psi^n)/sqrt(5)

;;Base case:
;;Induction Hypothesis:
;;Induction Step:
;;QED

;; 1.15
;; for n = 12.15, p is applied 5 times
;; because n is divided 5 times
(define (cube x) (* x x x))

(define (p x) (- (* 3 x) (* 4 (cube x))))

(define (sine angle)
  (if (not (> (abs angle) 0.1))
      angle
      (p (sine (/ angle 3.0)))))

;; 1.16
;; problem statement: write an iterative version
;; of the fast exponentiation algorithm.
;; keep an additional state variable a
;; such that ab^2 is unchanged from state to state
;; this answer is from community.schemewiki/?sicp-ex-1.16
(define (even? n)
  (= (remainder n 2) 0))

(define (fast-expt b n)
  (fast-expt-iter b n 1))

(define (fast-expt-iter b counter state)
  (cond ((= counter 0) state)
        ((even? counter) (fast-expt-iter (* b b) (/ counter 2) state))
        (else (fast-expt-iter b (- counter 1) (* b state)))))

;; 1.17
;; design a multiplication procedure analogous to fast-expt
;; that uses a logarithmic number of steps
;; using addition, `double` and `halve`
;; we would have:
;; 2b = b + b
;; 4b = 2b + 2b
;; 8b = 4b + 4b
;; and so on
;; this answer is from community.schemewiki/?sicp-ex-1.17
(define (double x) (+ x x))
(define (halve x) (/ x 2))

(define (fast-mult a b) 
  (cond ((= b 0) 0) 
        ((even? b) (fast-mult (double a) (halve b))) 
        (else (+ a (fast-mult a (- b 1)))))) 


;; 1.18
;; do 1.17 but iteratively
;; want to add a log b times
;; this answer is from community.schemewiki/?sicp-ex-1.18
(define (fm a b)
  (fm-iter a b 0))

(define (fm-iter a b acc)
  (cond ((= b 0) acc)
        ((even? b) (fm-iter (double a) (halve b) acc)) 
        (else (fm-iter a (- b 1) (+ a acc)))))


;; 1.19
;; finish the provided procedure
;; this answer is from community.schemewiki/?sicp-ex-1.19
;; p' = p^2 + q^2
;; q' = 2pq + q^2
;; this can be found using linear algebra
(define (fib n)
  (fib-iter 1 0 0 1 n))

(define (fib-iter a b p q count)
  (cond ((= count 0) b)
        ((even? count)
         (fib-iter a
                   b
                   (+ (* p p) (* q q))
                   (+ (* 2 p q) (* q q))
                   (/ count 2)))
        (else (fib-iter (+ (* b q) (* a q) (* a p))
                        (+ (* b p) (* a q))
                        p
                        q
                        (- count 1)))))

;; 1.20
;; in evaluating (gcd 206 40), how many remainder operations
;; are performed in:
;; normal-order evaluation? (expand then reduce) 18
;; above answer is from community.schemewiki/?sicp-ex-1.20
;; applicative order evaluation? (evaluate then apply) 4
;; (gcd 206 40)
;; (gcd 40 (remainder 206 40))
;; (gcd 40 6)
;; (gcd 6 (remainder 40 6))
;; (gcd 6 4)
;; (gcd 4 (remainder 6 4))
;; (gcd 4 2)
;; (gcd 2 (remainder 4 2))
;; (gcd 2 0)
;; 2

(define (square x) (* x x))

;; 1.21
;; use the provided smallest-divisor procedure to find
;; smallest divisor of 199, 1999, 19999
;; 199:199
;; 1999:1999
;; 19999:7
(define (smallest-divisor n)
  (find-divisor n 2))

(define (find-divisor n test-divisor)
  (cond ((> (square test-divisor) n) n)
        ((divides? test-divisor n) test-divisor)
        (else (find-divisor n (next test-divisor)))))

(define (divides? a b)
  (= (remainder b a) 0))

;; 1.22
;; provided code:
(define (prime? n)
  (= n (smallest-divisor n)))
  
(define (timed-prime-test n)
  (newline)
  (display n)
  (start-prime-test n (runtime)))

(define (start-prime-test n start-time)
  (if (fast-prime? n 100)
      (report-prime (- (runtime) start-time))))

(define (report-prime elapsed-time)
  (display " *** ")
  (display elapsed-time))
;; search-for-primes
;; find three smallest primes for a specified range
(define (search-for-primes lower upper)
  (define (prime-iter n)
    (cond ((<= n upper) (timed-prime-test n) (prime-iter (+ n 2))))) 
   (prime-iter (if (odd? lower) lower (+ lower 1))))


;; 1.23
(define (next n)
  (cond ((= n 2) 3)
        (else (+ n 2))))
;; modified smallest-divisor to use next instead of
;; (+ test-divisor 1)
;; 6ms (?)


;; 1.24
(define (expmod base exp m)
  (cond ((= exp 0) 1)
        ((even? exp)
         (remainder (square (expmod base (/ exp 2) m))
                    m))
        (else
         (remainder (* base (expmod base (- exp 1) m))
                    m))))

(define (fermat-test n)
  (define (try-it a)
    (= (expmod a n n) a))
  (try-it (+ 1 (random (- n 1)))))

(define (fast-prime? n times)
  (cond ((= times 0) true)
        ((fermat-test n) (fast-prime? n (- times 1)))
        (else false)))
;; modifying timed-prime-test to use fast-prime?
;; slower, 23ms (?), but using 10 times for fermat so


;; 1.25
;; no, because it makes us deal with bigger numbers

;; 1.26
;; calling square allows us to lean on applicative evaluation,
;; if we use * instead, we must evaluate each branch
;; so twice instead of once with square
;; i.e. tree recursion

;; 1.27
;; show that carmichael numbers fool fermat
;; answer from community.schemewiki/?sicp-ex-1.27
(define (carmichael? n)
  (define (iter a n)
    (if (= a n)
        (if (= (expmod a n n) a) (iter (+ a 1) n) false))) 
   (iter 1 n))

(define (test-carmichael n expected)
  (display (if (eq? (carmichael? n) expected) "OK" "FOOLED")))


;; 1.28
;; miller-rabin
;; solution from http://community.schemewiki.org/?sicp-ex-1.28
;; this solution rewrites expmod as a whole instead of modifying
(define (miller-rabin-expmod base exp m) 
  (define (squaremod-with-check x) 
    (define (check-nontrivial-sqrt1 x square) 
      (if (and (= square 1) 
               (not (= x 1)) 
               (not (= x (- m 1)))) 
          0 
          square)) 
    (check-nontrivial-sqrt1 x (remainder (square x) m))) 
  (cond ((= exp 0) 1) 
        ((even? exp) (squaremod-with-check 
                      (miller-rabin-expmod base (/ exp 2) m))) 
        (else 
         (remainder (* base (miller-rabin-expmod base (- exp 1) m)) 
                    m)))) 
  
(define (miller-rabin-test n) 
  (define (try-it a) 
    (define (check-it x) 
      (and (not (= x 0)) (= x 1))) 
    (check-it (miller-rabin-expmod a (- n 1) n))) 
  (try-it (+ 1 (random (- n 1)))))


;; 1.29
;; simpson's rule
(define (sum term a next b)
  (if (> a b)
      0
      (+ (term a)
         (sum term (next a) next b))))

(define (inc n) (+ n 1))

(define (simpson f a b n)
  (define h (/ n (- b a)))
  (define (yk k) (f (+ a (* k h))))
  (define (simpson-term k)
    (* (cond ((or (= 0 k) (= n k)) 1)
             ((even? k) 2)
             (else 4))
       (yk k)))
  (* (/ h 3) (sum simpson-term 0 inc n)))
  

;; 1.30
;; rewrite generic sum procedure to be iterative
(define (sum-iter term a next b)
  (define (iter a result)
    (if (> a b)
        result
        (iter (next a) (+ result (term a)))))
    (iter a 0))


;; 1.31
;; write a generic product procedure recursively and iteratively
;; over a given range
;; write define factorial in terms of this product procedure
;; compute approximations to pi
(define (product term a next b)
  (if (> a b)
      1
      (* (term a)
         (product term (next a) next b))))

(define (identity x) x)

(define (factorial n)
  (product identity 1 inc n))

(define (product-iter term a next b)
  (define (iter a result)
    (if (> a b)
        result
        (iter (next a) (* result (term a)))))
  (iter a 1))

;; from http://community.schemewiki.org/?sicp-ex-1.31
(define (wallis n)
  (if (even? n)
      (/ (+ n 2) (+ n 1))
      (/ (+ n 1) (+ n 2))))


;; 1.32
;; provide an even more general procedure called accumulate
;; show that sum and product can be defined as simple calls to this
(define (accumulate combiner null-value term a next b)
  (if (> a b)
      null-value
      (combiner (term a)
                (accumulate combiner null-value term (next a) next b))))

(define (acc-iter combiner null-value term a next b)
  (define (iter a result)
    (if (> a b)
        result
        (iter (next a) (combiner result (term a)))))
  (iter a null-value))

(define (add a b) (+ a b))

(define (mul a b) (* a b))

(define (sum-acc term a next b)
  (accumulate add 0 term a next b))

(define (prod-acc term a next b)
  (accumulate mul 1 term a next b))


;; 1.33
;; even more general version of accumulate
;; then implement:
;; sum of squares of prime numbers in [a,b]
;; product of all positive integers less than n that are relatively prime to n
(define (filtered-acc filter combiner null-value term a next b)
  (if (> a b)
      null-value
      (if (filter a)
          (combiner (term a)
                    (filtered-acc filter combiner null-value term (next a) next b))
          (combiner null-value
                    (filtered-acc filter combiner null-value term (next a) next b)))))

(define (sum-of-prime-squares a b)
  (filtered-acc prime? + 0 square a inc b))

(define (gcd a b)
  (if (= b 0)
      a
      (gcd b (remainder a b))))

(define (relatively-prime? m n)
  (= (gcd m n) 1))

(define (prod-rel-prime n)
  (define (relpri? x)
    (relatively-prime? x n))
  (filtered-acc relpri? * 1 identity 1 inc n))


;; 1.34
;; there will be an infinite chain of calls


;; 1.35
