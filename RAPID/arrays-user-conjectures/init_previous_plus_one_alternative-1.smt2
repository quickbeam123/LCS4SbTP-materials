; main()
; {
;    a[0] = v @l10
;    i = 1 @l11
;    while (i < alength) @l12
;    {
;       a[i] = (a[(i) - (1)]) + (1) @l14
;       i = (i) + (1) @l15
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Time Int) Int)
(declare-const alength Int)
(declare-const v Int)
(declare-fun i (Time) Int)
(declare-const l10 Time)
(declare-const l11 Time)
(declare-fun l12 (Nat) Time)
(declare-const nl12 Nat)
(declare-fun l14 (Nat) Time)
(declare-fun l15 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l12 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l12 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l12 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l12 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l12 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l12 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l12 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l12 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l12 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l12 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l12 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l12 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l12 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l12 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l12 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l12 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l12 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l12 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l12 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l12 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l12 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l12 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l12 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l12 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l12 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l12 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l12 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l12 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l12 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l12 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l12 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l12 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Update array variable a at location l10
      (and
         (= (a l11 0) v)
         (forall ((pos Int))
            (=>
               (not
                  (= pos 0)
               )
               (= (a l11 pos) (a l10 pos))
            )
         )
      )
      ;Loop at location l12
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l12 zero)) 1)
            (forall ((pos Int))
               (= (a (l12 zero) pos) (a l11 pos))
            )
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl12 Nat))
            (=>
               (Sub Itl12 nl12)
               (< (i (l12 Itl12)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl12 Nat))
            (=>
               (Sub Itl12 nl12)
               (and
                  ;Update array variable a at location l14
                  (and
                     (= (a (l15 Itl12) (i (l12 Itl12))) (+ (a (l12 Itl12) (- (i (l12 Itl12)) 1)) 1))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l12 Itl12)))
                           )
                           (= (a (l15 Itl12) pos) (a (l12 Itl12) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l12 (s Itl12))) (+ (i (l12 Itl12)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l12 (s Itl12)) pos) (a (l15 Itl12) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l12 nl12)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (forall ((pos Int))
         (= (a main_end pos) (a (l12 nl12) pos))
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l12
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l12 boundL boundR)
         (forall ((Itl12 Nat))
            (=>
               (and
                  (Sub boundL (s Itl12))
                  (Sub Itl12 boundR)
                  (= (i (l12 boundL)) (i (l12 Itl12)))
               )
               (= (i (l12 boundL)) (i (l12 (s Itl12))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l12
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l12 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l12 boundL)) (i (l12 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l12
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l12 boundL boundR)
         (forall ((Itl12 Nat))
            (=>
               (and
                  (Sub boundL (s Itl12))
                  (Sub Itl12 boundR)
                  (<= (i (l12 boundL)) (i (l12 Itl12)))
               )
               (<= (i (l12 boundL)) (i (l12 (s Itl12))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l12
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l12 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l12 boundL)) (i (l12 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l12
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l12 boundL boundR)
         (forall ((Itl12 Nat))
            (=>
               (and
                  (Sub boundL (s Itl12))
                  (Sub Itl12 boundR)
                  (>= (i (l12 boundL)) (i (l12 Itl12)))
               )
               (>= (i (l12 boundL)) (i (l12 (s Itl12))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l12
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l12 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l12 boundL)) (i (l12 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l12
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l12 pos boundL boundR)
         (forall ((Itl12 Nat))
            (=>
               (and
                  (Sub boundL (s Itl12))
                  (Sub Itl12 boundR)
                  (= (a (l12 boundL) pos) (a (l12 Itl12) pos))
               )
               (= (a (l12 boundL) pos) (a (l12 (s Itl12)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l12
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l12 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l12 boundL) pos) (a (l12 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l12
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l12 pos boundL boundR)
         (forall ((Itl12 Nat))
            (=>
               (and
                  (Sub boundL (s Itl12))
                  (Sub Itl12 boundR)
                  (<= (a (l12 boundL) pos) (a (l12 Itl12) pos))
               )
               (<= (a (l12 boundL) pos) (a (l12 (s Itl12)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l12
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l12 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l12 boundL) pos) (a (l12 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l12
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l12 pos boundL boundR)
         (forall ((Itl12 Nat))
            (=>
               (and
                  (Sub boundL (s Itl12))
                  (Sub Itl12 boundR)
                  (>= (a (l12 boundL) pos) (a (l12 Itl12) pos))
               )
               (>= (a (l12 boundL) pos) (a (l12 (s Itl12)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l12
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l12 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l12 boundL) pos) (a (l12 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l12
(assert
   (=
      Dense-i-l12
      (forall ((Itl12 Nat))
         (=>
            (Sub Itl12 nl12)
            (or
               (= (i (l12 (s Itl12))) (i (l12 Itl12)))
               (= (i (l12 (s Itl12))) (+ (i (l12 Itl12)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l12
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l12 xInt)
         (and
            (<= (i (l12 zero)) xInt)
            (< xInt (i (l12 nl12)))
            Dense-i-l12
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l12
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l12 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl12)
               (= (i (l12 it)) xInt)
               (= (i (l12 (s it))) (+ (i (l12 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l12
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l12
            (= (i (l12 (s it1))) (+ (i (l12 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl12))
         )
         (not
            (= (i (l12 it1)) (i (l12 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l12
(assert
   (=>
      (< (i (l12 zero)) alength)
      (exists ((Itl12 Nat))
         (= (s Itl12) nl12)
      )
   )
)

; Conjecture: user-conjecture-1
(assert-not
   (forall ((pos Int))
      (=>
         (and
            (<= 0 pos)
            (< (+ pos 1) alength)
            (<= 0 alength)
         )
         (< (a main_end pos) (a main_end (+ pos 1)))
      )
   )
)

(check-sat)

