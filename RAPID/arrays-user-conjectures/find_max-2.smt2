; main()
; {
;    i = 0 @l7
;    max = 0 @l8
;    while (i < alength) @l9
;    {
;       if (a[i] > max) @l11
;       {
;          max = a[i] @l13
;       }
;       else
;       {
;          skip @l17
;       }
;       i = (i) + (1) @l19
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Int) Int)
(declare-const alength Int)
(declare-fun i (Time) Int)
(declare-fun max (Time) Int)
(declare-const l7 Time)
(declare-const l8 Time)
(declare-fun l9 (Nat) Time)
(declare-const nl9 Nat)
(declare-fun l11 (Nat) Time)
(declare-fun l13 (Nat) Time)
(declare-fun l17 (Nat) Time)
(declare-fun l19 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-max-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-max-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-max-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-max-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-max-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-max-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-max-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-max-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-max-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-max-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-max-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-max-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l9 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l9 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-max-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-max-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-max-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-max-l9 () Bool)
(declare-lemma-predicate Prem-Intermed-max-l9 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-max-l9 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-max-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-max-l9 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l9
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l9 zero)) 0)
            (= (max (l9 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               (< (i (l9 Itl9)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               (and
                  ;Semantics of IfElse at location l11
                  (and
                     ;Semantics of left branch
                     (=>
                        (> (a (i (l9 Itl9))) (max (l9 Itl9)))
                        (= (max (l19 Itl9)) (a (i (l9 Itl9))))
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (> (a (i (l9 Itl9))) (max (l9 Itl9)))
                        )
                        (= (max (l19 Itl9)) (max (l9 Itl9)))
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l9 (s Itl9))) (+ (i (l9 Itl9)) 1))
                  ;Define value of variable max at beginning of next iteration
                  (= (max (l9 (s Itl9))) (max (l19 Itl9)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l9 nl9)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (= (max main_end) (max (l9 nl9)))
   )
)

; Definition: Premise for value-evolution-eq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (<= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (>= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-max-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-max-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (max (l9 boundL)) (max (l9 Itl9)))
               )
               (= (max (l9 boundL)) (max (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-max-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-max-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (max (l9 boundL)) (max (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-max-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-max-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (max (l9 boundL)) (max (l9 Itl9)))
               )
               (<= (max (l9 boundL)) (max (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-max-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-max-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (max (l9 boundL)) (max (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-max-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-max-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (max (l9 boundL)) (max (l9 Itl9)))
               )
               (>= (max (l9 boundL)) (max (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-max-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-max-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (max (l9 boundL)) (max (l9 boundR)))
         )
      )
   )
)

; Definition: Dense for i-l9
(assert
   (=
      Dense-i-l9
      (forall ((Itl9 Nat))
         (=>
            (Sub Itl9 nl9)
            (or
               (= (i (l9 (s Itl9))) (i (l9 Itl9)))
               (= (i (l9 (s Itl9))) (+ (i (l9 Itl9)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l9
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l9 xInt)
         (and
            (<= (i (l9 zero)) xInt)
            (< xInt (i (l9 nl9)))
            Dense-i-l9
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l9
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l9 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl9)
               (= (i (l9 it)) xInt)
               (= (i (l9 (s it))) (+ (i (l9 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for max-l9
(assert
   (=
      Dense-max-l9
      (forall ((Itl9 Nat))
         (=>
            (Sub Itl9 nl9)
            (or
               (= (max (l9 (s Itl9))) (max (l9 Itl9)))
               (= (max (l9 (s Itl9))) (+ (max (l9 Itl9)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-max-l9
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-max-l9 xInt)
         (and
            (<= (max (l9 zero)) xInt)
            (< xInt (max (l9 nl9)))
            Dense-max-l9
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-max-l9
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-max-l9 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl9)
               (= (max (l9 it)) xInt)
               (= (max (l9 (s it))) (+ (max (l9 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l9
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l9
            (= (i (l9 (s it1))) (+ (i (l9 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl9))
         )
         (not
            (= (i (l9 it1)) (i (l9 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-max-l9
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-max-l9
            (= (max (l9 (s it1))) (+ (max (l9 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl9))
         )
         (not
            (= (max (l9 it1)) (max (l9 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l9
(assert
   (=>
      (< (i (l9 zero)) alength)
      (exists ((Itl9 Nat))
         (= (s Itl9) nl9)
      )
   )
)

; Conjecture: user-conjecture-2
(assert-not
   (=>
      (and
         (<= 0 alength)
         (forall ((k Int))
            (=>
               (and
                  (<= 0 k)
                  (< k alength)
               )
               (not
                  (<= 0 (a k))
               )
            )
         )
      )
      (= (max main_end) 0)
   )
)

(check-sat)

