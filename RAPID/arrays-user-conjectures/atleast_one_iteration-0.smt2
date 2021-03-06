; main()
; {
;    i = 0 @l6
;    j = 0 @l7
;    while (i < alength) @l8
;    {
;       i = (i) + (1) @l10
;       j = 1 @l11
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
(declare-const l6 Time)
(declare-const l7 Time)
(declare-fun l8 (Nat) Time)
(declare-const nl8 Nat)
(declare-fun l10 (Nat) Time)
(declare-fun l11 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-j-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-j-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-j-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-j-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-j-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-j-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-j-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-j-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-j-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-j-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-j-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-j-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-j-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-j-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-j-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-j-l8 () Bool)
(declare-lemma-predicate Prem-Intermed-j-l8 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l8 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l8 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-j-l8 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-j-l8 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-j-l8 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l8 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l8 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l8
      (and
         ;Define variable values at beginning of loop
         (and
            (= (j (l8 zero)) 0)
            (= (i (l8 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl8 Nat))
            (=>
               (Sub Itl8 nl8)
               (< (i (l8 Itl8)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl8 Nat))
            (=>
               (Sub Itl8 nl8)
               (and
                  ;Define value of variable j at beginning of next iteration
                  (= (j (l8 (s Itl8))) 1)
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l8 (s Itl8))) (+ (i (l8 Itl8)) 1))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l8 nl8)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (= (j main_end) (j (l8 nl8)))
   )
)

; Definition: Premise for value-evolution-eq-j-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-j-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (= (j (l8 boundL)) (j (l8 Itl8)))
               )
               (= (j (l8 boundL)) (j (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-j-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-j-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (j (l8 boundL)) (j (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-j-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-j-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (<= (j (l8 boundL)) (j (l8 Itl8)))
               )
               (<= (j (l8 boundL)) (j (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-j-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-j-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (j (l8 boundL)) (j (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-j-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-j-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (>= (j (l8 boundL)) (j (l8 Itl8)))
               )
               (>= (j (l8 boundL)) (j (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-j-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-j-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (j (l8 boundL)) (j (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (= (i (l8 boundL)) (i (l8 Itl8)))
               )
               (= (i (l8 boundL)) (i (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l8 boundL)) (i (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (<= (i (l8 boundL)) (i (l8 Itl8)))
               )
               (<= (i (l8 boundL)) (i (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l8 boundL)) (i (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (>= (i (l8 boundL)) (i (l8 Itl8)))
               )
               (>= (i (l8 boundL)) (i (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l8 boundL)) (i (l8 boundR)))
         )
      )
   )
)

; Definition: Dense for j-l8
(assert
   (=
      Dense-j-l8
      (forall ((Itl8 Nat))
         (=>
            (Sub Itl8 nl8)
            (or
               (= (j (l8 (s Itl8))) (j (l8 Itl8)))
               (= (j (l8 (s Itl8))) (+ (j (l8 Itl8)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-j-l8
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-j-l8 xInt)
         (and
            (<= (j (l8 zero)) xInt)
            (< xInt (j (l8 nl8)))
            Dense-j-l8
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-j-l8
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-j-l8 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl8)
               (= (j (l8 it)) xInt)
               (= (j (l8 (s it))) (+ (j (l8 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l8
(assert
   (=
      Dense-i-l8
      (forall ((Itl8 Nat))
         (=>
            (Sub Itl8 nl8)
            (or
               (= (i (l8 (s Itl8))) (i (l8 Itl8)))
               (= (i (l8 (s Itl8))) (+ (i (l8 Itl8)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l8
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l8 xInt)
         (and
            (<= (i (l8 zero)) xInt)
            (< xInt (i (l8 nl8)))
            Dense-i-l8
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l8
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l8 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl8)
               (= (i (l8 it)) xInt)
               (= (i (l8 (s it))) (+ (i (l8 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-j-l8
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-j-l8
            (= (j (l8 (s it1))) (+ (j (l8 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl8))
         )
         (not
            (= (j (l8 it1)) (j (l8 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l8
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l8
            (= (i (l8 (s it1))) (+ (i (l8 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl8))
         )
         (not
            (= (i (l8 it1)) (i (l8 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l8
(assert
   (=>
      (< (i (l8 zero)) alength)
      (exists ((Itl8 Nat))
         (= (s Itl8) nl8)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (=>
      (= 0 alength)
      (= (j main_end) 0)
   )
)

(check-sat)

