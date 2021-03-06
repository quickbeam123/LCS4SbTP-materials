; main()
; {
;    i = 0 @l14
;    while (i < alength) @l15
;    {
;       a[i] = (i) + (v) @l17
;       i = (i) + (1) @l18
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
(declare-const l14 Time)
(declare-fun l15 (Nat) Time)
(declare-const nl15 Nat)
(declare-fun l17 (Nat) Time)
(declare-fun l18 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l15 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l15 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l15 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l15 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l15 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l15 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l15 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l15 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l15 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l15 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l15 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l15 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l15 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l15 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l15 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l15 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l15 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l15 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l15 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l15 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l15 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l15 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l15
      (and
         ;Define variable values at beginning of loop
         (= (i (l15 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl15 Nat))
            (=>
               (Sub Itl15 nl15)
               (< (i (l15 Itl15)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl15 Nat))
            (=>
               (Sub Itl15 nl15)
               (and
                  ;Update array variable a at location l17
                  (and
                     (= (a (l18 Itl15) (i (l15 Itl15))) (+ (i (l15 Itl15)) v))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l15 Itl15)))
                           )
                           (= (a (l18 Itl15) pos) (a (l15 Itl15) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l15 (s Itl15))) (+ (i (l15 Itl15)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l15 (s Itl15)) pos) (a (l18 Itl15) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l15 nl15)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (forall ((pos Int))
         (= (a main_end pos) (a (l15 nl15) pos))
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l15 boundL boundR)
         (forall ((Itl15 Nat))
            (=>
               (and
                  (Sub boundL (s Itl15))
                  (Sub Itl15 boundR)
                  (= (i (l15 boundL)) (i (l15 Itl15)))
               )
               (= (i (l15 boundL)) (i (l15 (s Itl15))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l15 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l15 boundL)) (i (l15 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l15 boundL boundR)
         (forall ((Itl15 Nat))
            (=>
               (and
                  (Sub boundL (s Itl15))
                  (Sub Itl15 boundR)
                  (<= (i (l15 boundL)) (i (l15 Itl15)))
               )
               (<= (i (l15 boundL)) (i (l15 (s Itl15))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l15 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l15 boundL)) (i (l15 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l15 boundL boundR)
         (forall ((Itl15 Nat))
            (=>
               (and
                  (Sub boundL (s Itl15))
                  (Sub Itl15 boundR)
                  (>= (i (l15 boundL)) (i (l15 Itl15)))
               )
               (>= (i (l15 boundL)) (i (l15 (s Itl15))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l15 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l15 boundL)) (i (l15 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l15
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l15 pos boundL boundR)
         (forall ((Itl15 Nat))
            (=>
               (and
                  (Sub boundL (s Itl15))
                  (Sub Itl15 boundR)
                  (= (a (l15 boundL) pos) (a (l15 Itl15) pos))
               )
               (= (a (l15 boundL) pos) (a (l15 (s Itl15)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l15
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l15 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l15 boundL) pos) (a (l15 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l15
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l15 pos boundL boundR)
         (forall ((Itl15 Nat))
            (=>
               (and
                  (Sub boundL (s Itl15))
                  (Sub Itl15 boundR)
                  (<= (a (l15 boundL) pos) (a (l15 Itl15) pos))
               )
               (<= (a (l15 boundL) pos) (a (l15 (s Itl15)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l15
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l15 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l15 boundL) pos) (a (l15 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l15
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l15 pos boundL boundR)
         (forall ((Itl15 Nat))
            (=>
               (and
                  (Sub boundL (s Itl15))
                  (Sub Itl15 boundR)
                  (>= (a (l15 boundL) pos) (a (l15 Itl15) pos))
               )
               (>= (a (l15 boundL) pos) (a (l15 (s Itl15)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l15
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l15 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l15 boundL) pos) (a (l15 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l15
(assert
   (=
      Dense-i-l15
      (forall ((Itl15 Nat))
         (=>
            (Sub Itl15 nl15)
            (or
               (= (i (l15 (s Itl15))) (i (l15 Itl15)))
               (= (i (l15 (s Itl15))) (+ (i (l15 Itl15)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l15
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l15 xInt)
         (and
            (<= (i (l15 zero)) xInt)
            (< xInt (i (l15 nl15)))
            Dense-i-l15
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l15
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l15 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl15)
               (= (i (l15 it)) xInt)
               (= (i (l15 (s it))) (+ (i (l15 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l15
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l15
            (= (i (l15 (s it1))) (+ (i (l15 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl15))
         )
         (not
            (= (i (l15 it1)) (i (l15 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l15
(assert
   (=>
      (< (i (l15 zero)) alength)
      (exists ((Itl15 Nat))
         (= (s Itl15) nl15)
      )
   )
)

; Conjecture: user-conjecture-2
(assert-not
   (forall ((pos Int))
      (=>
         (and
            (<= 0 alength)
            (<= 0 pos)
            (< pos alength)
            (< 0 v)
         )
         (< pos (a main_end pos))
      )
   )
)

(check-sat)

