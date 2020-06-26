; main()
; {
;    alength = 0 @l4
;    while (alength < k) @l9
;    {
;       a[alength] = b[alength] @l11
;       alength = (alength) + (1) @l12
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Time Int) Int)
(declare-fun alength (Time) Int)
(declare-fun b (Int) Int)
(declare-const blength Int)
(declare-const k Int)
(declare-const l4 Time)
(declare-fun l9 (Nat) Time)
(declare-const nl9 Nat)
(declare-fun l11 (Nat) Time)
(declare-fun l12 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-alength-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-alength-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-alength-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-alength-l9 (Nat Nat) Bool)
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
(declare-lemma-predicate BC-Ax-Intermed-alength-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-alength-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-alength-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-alength-l9 () Bool)
(declare-lemma-predicate Prem-Intermed-alength-l9 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-alength-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-alength-l9 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l9
      (and
         ;Define variable values at beginning of loop
         (= (alength (l9 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               (< (alength (l9 Itl9)) k)
            )
         )
         ;Semantics of the body
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               (and
                  ;Update array variable a at location l11
                  (and
                     (= (a (l12 Itl9) (alength (l9 Itl9))) (b (alength (l9 Itl9))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (alength (l9 Itl9)))
                           )
                           (= (a (l12 Itl9) pos) (a (l9 Itl9) pos))
                        )
                     )
                  )
                  ;Define value of variable alength at beginning of next iteration
                  (= (alength (l9 (s Itl9))) (+ (alength (l9 Itl9)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l9 (s Itl9)) pos) (a (l12 Itl9) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (alength (l9 nl9)) k)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (forall ((pos Int))
         (= (a main_end pos) (a (l9 nl9) pos))
      )
   )
)

; Definition: Premise for value-evolution-eq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-alength-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (alength (l9 boundL)) (alength (l9 Itl9)))
               )
               (= (alength (l9 boundL)) (alength (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-alength-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (alength (l9 boundL)) (alength (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-alength-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (alength (l9 boundL)) (alength (l9 Itl9)))
               )
               (<= (alength (l9 boundL)) (alength (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-alength-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (alength (l9 boundL)) (alength (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-alength-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (alength (l9 boundL)) (alength (l9 Itl9)))
               )
               (>= (alength (l9 boundL)) (alength (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-alength-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (alength (l9 boundL)) (alength (l9 boundR)))
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

; Definition: Dense for alength-l9
(assert
   (=
      Dense-alength-l9
      (forall ((Itl9 Nat))
         (=>
            (Sub Itl9 nl9)
            (or
               (= (alength (l9 (s Itl9))) (alength (l9 Itl9)))
               (= (alength (l9 (s Itl9))) (+ (alength (l9 Itl9)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-alength-l9
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-alength-l9 xInt)
         (and
            (<= (alength (l9 zero)) xInt)
            (< xInt (alength (l9 nl9)))
            Dense-alength-l9
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-alength-l9
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-alength-l9 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl9)
               (= (alength (l9 it)) xInt)
               (= (alength (l9 (s it))) (+ (alength (l9 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-alength-l9
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-alength-l9
            (= (alength (l9 (s it1))) (+ (alength (l9 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl9))
         )
         (not
            (= (alength (l9 it1)) (alength (l9 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l9
(assert
   (=>
      (< (alength (l9 zero)) k)
      (exists ((Itl9 Nat))
         (= (s Itl9) nl9)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (=>
      (<= k blength)
      (forall ((j Int))
         (=>
            (and
               (<= 0 j)
               (< j k)
            )
            (= (a main_end j) (b j))
         )
      )
   )
)

(check-sat)

