; main()
; {
;    i = 0 @l6
;    min = 0 @l7
;    while (i < alength) @l8
;    {
;       if (a[i] < min) @l10
;       {
;          min = a[i] @l12
;       }
;       else
;       {
;          skip @l16
;       }
;       i = (i) + (1) @l18
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
(declare-fun min (Time) Int)
(declare-const l6 Time)
(declare-const l7 Time)
(declare-fun l8 (Nat) Time)
(declare-const nl8 Nat)
(declare-fun l10 (Nat) Time)
(declare-fun l12 (Nat) Time)
(declare-fun l16 (Nat) Time)
(declare-fun l18 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-min-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-min-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-min-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-min-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-min-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-min-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-min-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-min-l8 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-min-l8 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-min-l8 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-min-l8 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-min-l8 (Nat Nat) Bool)
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
(declare-lemma-predicate BC-Ax-Intermed-min-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-min-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-min-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-min-l8 () Bool)
(declare-lemma-predicate Prem-Intermed-min-l8 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l8 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l8 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l8 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l8 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-min-l8 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-min-l8 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-min-l8 (Nat Nat Nat) Bool)
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
            (= (i (l8 zero)) 0)
            (= (min (l8 zero)) 0)
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
                  ;Semantics of IfElse at location l10
                  (and
                     ;Semantics of left branch
                     (=>
                        (< (a (i (l8 Itl8))) (min (l8 Itl8)))
                        (= (min (l18 Itl8)) (a (i (l8 Itl8))))
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (< (a (i (l8 Itl8))) (min (l8 Itl8)))
                        )
                        (= (min (l18 Itl8)) (min (l8 Itl8)))
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l8 (s Itl8))) (+ (i (l8 Itl8)) 1))
                  ;Define value of variable min at beginning of next iteration
                  (= (min (l8 (s Itl8))) (min (l18 Itl8)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l8 nl8)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (= (min main_end) (min (l8 nl8)))
   )
)

; Definition: Premise for value-evolution-eq-min-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-min-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (= (min (l8 boundL)) (min (l8 Itl8)))
               )
               (= (min (l8 boundL)) (min (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-min-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-min-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (min (l8 boundL)) (min (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-min-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-min-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (<= (min (l8 boundL)) (min (l8 Itl8)))
               )
               (<= (min (l8 boundL)) (min (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-min-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-min-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (min (l8 boundL)) (min (l8 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-min-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-min-l8 boundL boundR)
         (forall ((Itl8 Nat))
            (=>
               (and
                  (Sub boundL (s Itl8))
                  (Sub Itl8 boundR)
                  (>= (min (l8 boundL)) (min (l8 Itl8)))
               )
               (>= (min (l8 boundL)) (min (l8 (s Itl8))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-min-l8
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-min-l8 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (min (l8 boundL)) (min (l8 boundR)))
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

; Definition: Dense for min-l8
(assert
   (=
      Dense-min-l8
      (forall ((Itl8 Nat))
         (=>
            (Sub Itl8 nl8)
            (or
               (= (min (l8 (s Itl8))) (min (l8 Itl8)))
               (= (min (l8 (s Itl8))) (+ (min (l8 Itl8)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-min-l8
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-min-l8 xInt)
         (and
            (<= (min (l8 zero)) xInt)
            (< xInt (min (l8 nl8)))
            Dense-min-l8
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-min-l8
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-min-l8 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl8)
               (= (min (l8 it)) xInt)
               (= (min (l8 (s it))) (+ (min (l8 it)) 1))
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

; Axiom: already-proven-lemma iterator-injectivity-min-l8
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-min-l8
            (= (min (l8 (s it1))) (+ (min (l8 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl8))
         )
         (not
            (= (min (l8 it1)) (min (l8 it2)))
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

; Conjecture: user-conjecture-2
(assert-not
   (=>
      (and
         (<= 0 alength)
         (forall ((k Int))
            (=>
               (and
                  (<= 0 k)
                  (< k alength)
               )
               (not
                  (<= (a k) 0)
               )
            )
         )
      )
      (= (min main_end) 0)
   )
)

(check-sat)

