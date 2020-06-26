; main()
; {
;    i = 0 @l11
;    j = 0 @l12
;    while (i < alength) @l13
;    {
;       i = (i) + (1) @l15
;       j = 1 @l16
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
(declare-fun j (Time) Int)
(declare-const l11 Time)
(declare-const l12 Time)
(declare-fun l13 (Nat) Time)
(declare-const nl13 Nat)
(declare-fun l15 (Nat) Time)
(declare-fun l16 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-j-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-j-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-j-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-j-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-j-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-j-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-j-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-j-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-j-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-j-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-j-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-j-l13 (Nat Nat) Bool)
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
(declare-lemma-predicate BC-Ax-Intermed-j-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-j-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-j-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-j-l13 () Bool)
(declare-lemma-predicate Prem-Intermed-j-l13 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l13 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l13 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-j-l13 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-j-l13 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-j-l13 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l13 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l13 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l13
      (and
         ;Define variable values at beginning of loop
         (and
            (= (j (l13 zero)) 0)
            (= (i (l13 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl13 Nat))
            (=>
               (Sub Itl13 nl13)
               (< (i (l13 Itl13)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl13 Nat))
            (=>
               (Sub Itl13 nl13)
               (and
                  ;Define value of variable j at beginning of next iteration
                  (= (j (l13 (s Itl13))) 1)
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l13 (s Itl13))) (+ (i (l13 Itl13)) 1))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l13 nl13)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (= (j main_end) (j (l13 nl13)))
   )
)

; Definition: Premise for value-evolution-eq-j-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-j-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (= (j (l13 boundL)) (j (l13 Itl13)))
               )
               (= (j (l13 boundL)) (j (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-j-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-j-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (j (l13 boundL)) (j (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-j-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-j-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (<= (j (l13 boundL)) (j (l13 Itl13)))
               )
               (<= (j (l13 boundL)) (j (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-j-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-j-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (j (l13 boundL)) (j (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-j-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-j-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (>= (j (l13 boundL)) (j (l13 Itl13)))
               )
               (>= (j (l13 boundL)) (j (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-j-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-j-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (j (l13 boundL)) (j (l13 boundR)))
         )
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

; Definition: Dense for j-l13
(assert
   (=
      Dense-j-l13
      (forall ((Itl13 Nat))
         (=>
            (Sub Itl13 nl13)
            (or
               (= (j (l13 (s Itl13))) (j (l13 Itl13)))
               (= (j (l13 (s Itl13))) (+ (j (l13 Itl13)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-j-l13
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-j-l13 xInt)
         (and
            (<= (j (l13 zero)) xInt)
            (< xInt (j (l13 nl13)))
            Dense-j-l13
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-j-l13
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-j-l13 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl13)
               (= (j (l13 it)) xInt)
               (= (j (l13 (s it))) (+ (j (l13 it)) 1))
            )
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

; Axiom: already-proven-lemma iterator-injectivity-j-l13
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-j-l13
            (= (j (l13 (s it1))) (+ (j (l13 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl13))
         )
         (not
            (= (j (l13 it1)) (j (l13 it2)))
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
      (< (i (l13 zero)) alength)
      (exists ((Itl13 Nat))
         (= (s Itl13) nl13)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (=>
      (< 0 alength)
      (= (j main_end) 1)
   )
)

(check-sat)

