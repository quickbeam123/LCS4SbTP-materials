; main()
; {
;    i = 0 @l8
;    while (i < length) @l9
;    {
;       current = a[i] @l11
;       a[i] = b[i] @l12
;       b[i] = current @l13
;       i = (i) + (1) @l14
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Time Int) Int)
(declare-fun b (Time Int) Int)
(declare-const length Int)
(declare-fun i (Time) Int)
(declare-fun current (Time) Int)
(declare-const l8 Time)
(declare-fun l9 (Nat) Time)
(declare-const nl9 Nat)
(declare-fun l11 (Nat) Time)
(declare-fun l12 (Nat) Time)
(declare-fun l13 (Nat) Time)
(declare-fun l14 (Nat) Time)
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
(declare-lemma-predicate BC-AxEvol-eq-b-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l9 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l9 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l9 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l9
      (and
         ;Define variable values at beginning of loop
         (and
            (forall ((pos Int))
               (= (a (l9 zero) pos) (a l8 pos))
            )
            (= (i (l9 zero)) 0)
            (forall ((pos Int))
               (= (b (l9 zero) pos) (b l8 pos))
            )
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               (< (i (l9 Itl9)) length)
            )
         )
         ;Semantics of the body
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               (and
                  ;Update array variable a at location l12
                  (and
                     (= (a (l13 Itl9) (i (l9 Itl9))) (b (l9 Itl9) (i (l9 Itl9))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l9 Itl9)))
                           )
                           (= (a (l13 Itl9) pos) (a (l9 Itl9) pos))
                        )
                     )
                  )
                  ;Update array variable b at location l13
                  (and
                     (= (b (l14 Itl9) (i (l9 Itl9))) (a (l9 Itl9) (i (l9 Itl9))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l9 Itl9)))
                           )
                           (= (b (l14 Itl9) pos) (b (l9 Itl9) pos))
                        )
                     )
                  )
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l9 (s Itl9)) pos) (a (l13 Itl9) pos))
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l9 (s Itl9))) (+ (i (l9 Itl9)) 1))
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l9 (s Itl9)) pos) (b (l14 Itl9) pos))
                  )
                  ;Define value of variable current at beginning of next iteration
                  (= (current (l9 (s Itl9))) (a (l9 Itl9) (i (l9 Itl9))))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l9 nl9)) length)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (forall ((pos Int))
            (= (b main_end pos) (b (l9 nl9) pos))
         )
         (forall ((pos Int))
            (= (a main_end pos) (a (l9 nl9) pos))
         )
      )
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

; Definition: Premise for value-evolution-eq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (b (l9 boundL) pos) (b (l9 Itl9) pos))
               )
               (= (b (l9 boundL) pos) (b (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l9 boundL) pos) (b (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (b (l9 boundL) pos) (b (l9 Itl9) pos))
               )
               (<= (b (l9 boundL) pos) (b (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l9 boundL) pos) (b (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (b (l9 boundL) pos) (b (l9 Itl9) pos))
               )
               (>= (b (l9 boundL) pos) (b (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l9 boundL) pos) (b (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l9 boundL) pos) (a (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (<= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l9 boundL) pos) (a (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (>= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l9 boundL) pos) (a (l9 boundR) pos))
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

; Axiom: already-proven-lemma atLeastOneIteration-l9
(assert
   (=>
      (< (i (l9 zero)) length)
      (exists ((Itl9 Nat))
         (= (s Itl9) nl9)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (forall ((pos Int))
      (=>
         (and
            (<= 0 length)
            (<= 0 pos)
            (< pos length)
         )
         (= (a main_end pos) (b l8 pos))
      )
   )
)

(check-sat)

