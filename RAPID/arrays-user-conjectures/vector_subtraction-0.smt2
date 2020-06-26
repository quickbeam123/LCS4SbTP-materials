; main()
; {
;    i = 0 @l12
;    while (i < length) @l13
;    {
;       c[i] = (a[i]) - (b[i]) @l15
;       i = (i) + (1) @l16
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(declare-fun c (Time Int) Int)
(declare-const length Int)
(declare-fun i (Time) Int)
(declare-const l12 Time)
(declare-fun l13 (Nat) Time)
(declare-const nl13 Nat)
(declare-fun l15 (Nat) Time)
(declare-fun l16 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-c-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-c-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-c-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-c-l13 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-c-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-c-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-c-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-c-l13 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-c-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-c-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-c-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-c-l13 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l13 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l13 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l13 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l13 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l13
      (and
         ;Define variable values at beginning of loop
         (= (i (l13 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl13 Nat))
            (=>
               (Sub Itl13 nl13)
               (< (i (l13 Itl13)) length)
            )
         )
         ;Semantics of the body
         (forall ((Itl13 Nat))
            (=>
               (Sub Itl13 nl13)
               (and
                  ;Update array variable c at location l15
                  (and
                     (= (c (l16 Itl13) (i (l13 Itl13))) (- (a (i (l13 Itl13))) (b (i (l13 Itl13)))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l13 Itl13)))
                           )
                           (= (c (l16 Itl13) pos) (c (l13 Itl13) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l13 (s Itl13))) (+ (i (l13 Itl13)) 1))
                  ;Define value of array variable c at beginning of next iteration
                  (forall ((pos Int))
                     (= (c (l13 (s Itl13)) pos) (c (l16 Itl13) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l13 nl13)) length)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (forall ((pos Int))
         (= (c main_end pos) (c (l13 nl13) pos))
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (= (i (l13 boundL)) (i (l13 Itl13)))
               )
               (= (i (l13 boundL)) (i (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l13 boundL)) (i (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (<= (i (l13 boundL)) (i (l13 Itl13)))
               )
               (<= (i (l13 boundL)) (i (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l13 boundL)) (i (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (>= (i (l13 boundL)) (i (l13 Itl13)))
               )
               (>= (i (l13 boundL)) (i (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l13 boundL)) (i (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-c-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-c-l13 pos boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (= (c (l13 boundL) pos) (c (l13 Itl13) pos))
               )
               (= (c (l13 boundL) pos) (c (l13 (s Itl13)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-c-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-c-l13 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (c (l13 boundL) pos) (c (l13 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-c-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-c-l13 pos boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (<= (c (l13 boundL) pos) (c (l13 Itl13) pos))
               )
               (<= (c (l13 boundL) pos) (c (l13 (s Itl13)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-c-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-c-l13 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (c (l13 boundL) pos) (c (l13 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-c-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-c-l13 pos boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (>= (c (l13 boundL) pos) (c (l13 Itl13) pos))
               )
               (>= (c (l13 boundL) pos) (c (l13 (s Itl13)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-c-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-c-l13 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (c (l13 boundL) pos) (c (l13 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l13
(assert
   (=
      Dense-i-l13
      (forall ((Itl13 Nat))
         (=>
            (Sub Itl13 nl13)
            (or
               (= (i (l13 (s Itl13))) (i (l13 Itl13)))
               (= (i (l13 (s Itl13))) (+ (i (l13 Itl13)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l13
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l13 xInt)
         (and
            (<= (i (l13 zero)) xInt)
            (< xInt (i (l13 nl13)))
            Dense-i-l13
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l13
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l13 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl13)
               (= (i (l13 it)) xInt)
               (= (i (l13 (s it))) (+ (i (l13 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l13
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l13
            (= (i (l13 (s it1))) (+ (i (l13 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl13))
         )
         (not
            (= (i (l13 it1)) (i (l13 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l13
(assert
   (=>
      (< (i (l13 zero)) length)
      (exists ((Itl13 Nat))
         (= (s Itl13) nl13)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (forall ((j Int))
      (=>
         (and
            (<= 0 j)
            (< j length)
            (<= 0 length)
         )
         (= (c main_end j) (- (a j) (b j)))
      )
   )
)

(check-sat)

