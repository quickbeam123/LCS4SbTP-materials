; main()
; {
;    i = 0 @l14
;    r = alength @l15
;    while ((i < alength) && (r == alength)) @l17
;    {
;       if (a[i] == v) @l19
;       {
;          r = i @l21
;       }
;       else
;       {
;          skip @l25
;       }
;       i = (i) + (1) @l27
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Int) Int)
(declare-const alength Int)
(declare-const v Int)
(declare-fun i (Time) Int)
(declare-fun r (Time) Int)
(declare-const l14 Time)
(declare-const l15 Time)
(declare-fun l17 (Nat) Time)
(declare-const nl17 Nat)
(declare-fun l19 (Nat) Time)
(declare-fun l21 (Nat) Time)
(declare-fun l25 (Nat) Time)
(declare-fun l27 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l17 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l17 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l17 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-r-l17 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-r-l17 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-r-l17 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-r-l17 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-r-l17 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-r-l17 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-r-l17 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-r-l17 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-r-l17 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-r-l17 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-r-l17 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-r-l17 (Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l17 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l17 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l17 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-r-l17 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-r-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-r-l17 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-r-l17 () Bool)
(declare-lemma-predicate Prem-Intermed-r-l17 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l17 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l17 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l17 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-r-l17 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-r-l17 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-r-l17 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l17
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l17 zero)) 0)
            (= (r (l17 zero)) alength)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl17 Nat))
            (=>
               (Sub Itl17 nl17)
               (and
                  (< (i (l17 Itl17)) alength)
                  (= (r (l17 Itl17)) alength)
               )
            )
         )
         ;Semantics of the body
         (forall ((Itl17 Nat))
            (=>
               (Sub Itl17 nl17)
               (and
                  ;Semantics of IfElse at location l19
                  (and
                     ;Semantics of left branch
                     (=>
                        (= (a (i (l17 Itl17))) v)
                        (= (r (l27 Itl17)) (i (l17 Itl17)))
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (= (a (i (l17 Itl17))) v)
                        )
                        (= (r (l27 Itl17)) (r (l17 Itl17)))
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l17 (s Itl17))) (+ (i (l17 Itl17)) 1))
                  ;Define value of variable r at beginning of next iteration
                  (= (r (l17 (s Itl17))) (r (l27 Itl17)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (and
               (< (i (l17 nl17)) alength)
               (= (r (l17 nl17)) alength)
            )
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (= (r main_end) (r (l17 nl17)))
   )
)

; Definition: Premise for value-evolution-eq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l17 boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (= (i (l17 boundL)) (i (l17 Itl17)))
               )
               (= (i (l17 boundL)) (i (l17 (s Itl17))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l17 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l17 boundL)) (i (l17 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l17 boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (<= (i (l17 boundL)) (i (l17 Itl17)))
               )
               (<= (i (l17 boundL)) (i (l17 (s Itl17))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l17 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l17 boundL)) (i (l17 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l17 boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (>= (i (l17 boundL)) (i (l17 Itl17)))
               )
               (>= (i (l17 boundL)) (i (l17 (s Itl17))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l17 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l17 boundL)) (i (l17 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-r-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-r-l17 boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (= (r (l17 boundL)) (r (l17 Itl17)))
               )
               (= (r (l17 boundL)) (r (l17 (s Itl17))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-r-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-r-l17 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (r (l17 boundL)) (r (l17 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-r-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-r-l17 boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (<= (r (l17 boundL)) (r (l17 Itl17)))
               )
               (<= (r (l17 boundL)) (r (l17 (s Itl17))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-r-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-r-l17 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (r (l17 boundL)) (r (l17 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-r-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-r-l17 boundL boundR)
         (forall ((Itl17 Nat))
            (=>
               (and
                  (Sub boundL (s Itl17))
                  (Sub Itl17 boundR)
                  (>= (r (l17 boundL)) (r (l17 Itl17)))
               )
               (>= (r (l17 boundL)) (r (l17 (s Itl17))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-r-l17
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-r-l17 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (r (l17 boundL)) (r (l17 boundR)))
         )
      )
   )
)

; Definition: Dense for i-l17
(assert
   (=
      Dense-i-l17
      (forall ((Itl17 Nat))
         (=>
            (Sub Itl17 nl17)
            (or
               (= (i (l17 (s Itl17))) (i (l17 Itl17)))
               (= (i (l17 (s Itl17))) (+ (i (l17 Itl17)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l17
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l17 xInt)
         (and
            (<= (i (l17 zero)) xInt)
            (< xInt (i (l17 nl17)))
            Dense-i-l17
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l17
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l17 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl17)
               (= (i (l17 it)) xInt)
               (= (i (l17 (s it))) (+ (i (l17 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for r-l17
(assert
   (=
      Dense-r-l17
      (forall ((Itl17 Nat))
         (=>
            (Sub Itl17 nl17)
            (or
               (= (r (l17 (s Itl17))) (r (l17 Itl17)))
               (= (r (l17 (s Itl17))) (+ (r (l17 Itl17)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-r-l17
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-r-l17 xInt)
         (and
            (<= (r (l17 zero)) xInt)
            (< xInt (r (l17 nl17)))
            Dense-r-l17
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-r-l17
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-r-l17 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl17)
               (= (r (l17 it)) xInt)
               (= (r (l17 (s it))) (+ (r (l17 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l17
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l17
            (= (i (l17 (s it1))) (+ (i (l17 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl17))
         )
         (not
            (= (i (l17 it1)) (i (l17 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-r-l17
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-r-l17
            (= (r (l17 (s it1))) (+ (r (l17 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl17))
         )
         (not
            (= (r (l17 it1)) (r (l17 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l17
(assert
   (=>
      (and
         (< (i (l17 zero)) alength)
         (= (r (l17 zero)) alength)
      )
      (exists ((Itl17 Nat))
         (= (s Itl17) nl17)
      )
   )
)

; Conjecture: user-conjecture-2
(assert-not
   (=>
      (and
         (<= 0 alength)
         (not
            (= (r main_end) alength)
         )
      )
      (exists ((pos Int))
         (= (a pos) v)
      )
   )
)

(check-sat)

