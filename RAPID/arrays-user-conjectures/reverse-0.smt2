; main()
; {
;    i = 0 @l9
;    while (i < length) @l10
;    {
;       a[i] = b[((length) - (1)) - (i)] @l12
;       i = (i) + (1) @l13
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Time Int) Int)
(declare-fun b (Int) Int)
(declare-const length Int)
(declare-fun i (Time) Int)
(declare-const l9 Time)
(declare-fun l10 (Nat) Time)
(declare-const nl10 Nat)
(declare-fun l12 (Nat) Time)
(declare-fun l13 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l10 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l10 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l10 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l10 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l10
      (and
         ;Define variable values at beginning of loop
         (= (i (l10 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl10 Nat))
            (=>
               (Sub Itl10 nl10)
               (< (i (l10 Itl10)) length)
            )
         )
         ;Semantics of the body
         (forall ((Itl10 Nat))
            (=>
               (Sub Itl10 nl10)
               (and
                  ;Update array variable a at location l12
                  (and
                     (= (a (l13 Itl10) (i (l10 Itl10))) (b (- (- length 1) (i (l10 Itl10)))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l10 Itl10)))
                           )
                           (= (a (l13 Itl10) pos) (a (l10 Itl10) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l10 (s Itl10))) (+ (i (l10 Itl10)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l10 (s Itl10)) pos) (a (l13 Itl10) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l10 nl10)) length)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (forall ((pos Int))
         (= (a main_end pos) (a (l10 nl10) pos))
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (= (i (l10 boundL)) (i (l10 Itl10)))
               )
               (= (i (l10 boundL)) (i (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l10 boundL)) (i (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (<= (i (l10 boundL)) (i (l10 Itl10)))
               )
               (<= (i (l10 boundL)) (i (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l10 boundL)) (i (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (>= (i (l10 boundL)) (i (l10 Itl10)))
               )
               (>= (i (l10 boundL)) (i (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l10 boundL)) (i (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (= (a (l10 boundL) pos) (a (l10 Itl10) pos))
               )
               (= (a (l10 boundL) pos) (a (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l10 boundL) pos) (a (l10 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (<= (a (l10 boundL) pos) (a (l10 Itl10) pos))
               )
               (<= (a (l10 boundL) pos) (a (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l10 boundL) pos) (a (l10 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (>= (a (l10 boundL) pos) (a (l10 Itl10) pos))
               )
               (>= (a (l10 boundL) pos) (a (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l10 boundL) pos) (a (l10 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l10
(assert
   (=
      Dense-i-l10
      (forall ((Itl10 Nat))
         (=>
            (Sub Itl10 nl10)
            (or
               (= (i (l10 (s Itl10))) (i (l10 Itl10)))
               (= (i (l10 (s Itl10))) (+ (i (l10 Itl10)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l10
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l10 xInt)
         (and
            (<= (i (l10 zero)) xInt)
            (< xInt (i (l10 nl10)))
            Dense-i-l10
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l10
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l10 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl10)
               (= (i (l10 it)) xInt)
               (= (i (l10 (s it))) (+ (i (l10 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l10
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l10
            (= (i (l10 (s it1))) (+ (i (l10 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl10))
         )
         (not
            (= (i (l10 it1)) (i (l10 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l10
(assert
   (=>
      (< (i (l10 zero)) length)
      (exists ((Itl10 Nat))
         (= (s Itl10) nl10)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (forall ((j Int))
      (=>
         (and
            (<= 0 length)
            (<= 0 j)
            (< j length)
         )
         (= (a main_end j) (b (- (- length 1) j)))
      )
   )
)

(check-sat)

