; main()
; {
;    i = 0 @l7
;    while ((i < length) && (!(b[i] == 0))) @l8
;    {
;       a[i] = b[i] @l10
;       i = (i) + (1) @l11
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
(declare-const l7 Time)
(declare-fun l8 (Nat) Time)
(declare-const nl8 Nat)
(declare-fun l10 (Nat) Time)
(declare-fun l11 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
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
(declare-lemma-predicate BC-AxEvol-eq-a-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l8 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l8 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l8 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l8 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l8 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l8 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l8
      (and
         ;Define variable values at beginning of loop
         (= (i (l8 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl8 Nat))
            (=>
               (Sub Itl8 nl8)
               (and
                  (< (i (l8 Itl8)) length)
                  (not
                     (= (b (i (l8 Itl8))) 0)
                  )
               )
            )
         )
         ;Semantics of the body
         (forall ((Itl8 Nat))
            (=>
               (Sub Itl8 nl8)
               (and
                  ;Update array variable a at location l10
                  (and
                     (= (a (l11 Itl8) (i (l8 Itl8))) (b (i (l8 Itl8))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l8 Itl8)))
                           )
                           (= (a (l11 Itl8) pos) (a (l8 Itl8) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l8 (s Itl8))) (+ (i (l8 Itl8)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l8 (s Itl8)) pos) (a (l11 Itl8) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (and
               (< (i (l8 nl8)) length)
               (not
                  (= (b (i (l8 nl8))) 0)
               )
            )
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (i main_end) (i (l8 nl8)))
         (forall ((pos Int))
            (= (a main_end pos) (a (l8 nl8) pos))
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

; Definition: Premise for value-evolution-eq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (= (a (l8 boundL) pos) (a (l8 Itl8) pos))
               )
               (= (a (l8 boundL) pos) (a (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l8 boundL) pos) (a (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (<= (a (l8 boundL) pos) (a (l8 Itl8) pos))
               )
               (<= (a (l8 boundL) pos) (a (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l8 boundL) pos) (a (l8 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l8 pos boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (>= (a (l8 boundL) pos) (a (l8 Itl8) pos))
               )
               (>= (a (l8 boundL) pos) (a (l8 (s Itl8)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l8
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l8 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l8 boundL) pos) (a (l8 boundR) pos))
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
      (and
         (< (i (l8 zero)) length)
         (not
            (= (b (i (l8 zero))) 0)
         )
      )
      (exists ((Itl8 Nat))
         (= (s Itl8) nl8)
      )
   )
)

; Conjecture: user-conjecture-3
(assert-not
   (=>
      (and
         (<= 0 length)
         (< (i main_end) length)
      )
      (= (b (i main_end)) 0)
   )
)

(check-sat)

