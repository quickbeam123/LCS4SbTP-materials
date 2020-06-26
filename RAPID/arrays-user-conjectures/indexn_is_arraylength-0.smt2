; main()
; {
;    i = 0 @l12
;    while (i < alength) @l14
;    {
;       i = (i) + (1) @l16
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-const alength Int)
(declare-fun i (Time) Int)
(declare-const l12 Time)
(declare-fun l14 (Nat) Time)
(declare-const nl14 Nat)
(declare-fun l16 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l14 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l14 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l14 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l14 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l14 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l14
      (and
         ;Define variable values at beginning of loop
         (= (i (l14 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl14 Nat))
            (=>
               (Sub Itl14 nl14)
               (< (i (l14 Itl14)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl14 Nat))
            (=>
               (Sub Itl14 nl14)
               ;Define value of variable i at beginning of next iteration
               (= (i (l14 (s Itl14))) (+ (i (l14 Itl14)) 1))
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l14 nl14)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (= (i main_end) (i (l14 nl14)))
   )
)

; Definition: Premise for value-evolution-eq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (= (i (l14 boundL)) (i (l14 Itl14)))
               )
               (= (i (l14 boundL)) (i (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l14 boundL)) (i (l14 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (<= (i (l14 boundL)) (i (l14 Itl14)))
               )
               (<= (i (l14 boundL)) (i (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l14 boundL)) (i (l14 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (>= (i (l14 boundL)) (i (l14 Itl14)))
               )
               (>= (i (l14 boundL)) (i (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l14 boundL)) (i (l14 boundR)))
         )
      )
   )
)

; Definition: Dense for i-l14
(assert
   (=
      Dense-i-l14
      (forall ((Itl14 Nat))
         (=>
            (Sub Itl14 nl14)
            (or
               (= (i (l14 (s Itl14))) (i (l14 Itl14)))
               (= (i (l14 (s Itl14))) (+ (i (l14 Itl14)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l14
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l14 xInt)
         (and
            (<= (i (l14 zero)) xInt)
            (< xInt (i (l14 nl14)))
            Dense-i-l14
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l14
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l14 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl14)
               (= (i (l14 it)) xInt)
               (= (i (l14 (s it))) (+ (i (l14 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l14
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l14
            (= (i (l14 (s it1))) (+ (i (l14 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl14))
         )
         (not
            (= (i (l14 it1)) (i (l14 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l14
(assert
   (=>
      (< (i (l14 zero)) alength)
      (exists ((Itl14 Nat))
         (= (s Itl14) nl14)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (not
      (< (i main_end) alength)
   )
)

(check-sat)

