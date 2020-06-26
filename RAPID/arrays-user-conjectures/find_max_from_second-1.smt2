; main()
; {
;    i = 1 @l9
;    max = a[0] @l10
;    while (i < alength) @l11
;    {
;       if (a[i] > max) @l13
;       {
;          max = a[i] @l15
;       }
;       else
;       {
;          skip @l19
;       }
;       i = (i) + (1) @l21
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
(declare-fun max (Time) Int)
(declare-const l9 Time)
(declare-const l10 Time)
(declare-fun l11 (Nat) Time)
(declare-const nl11 Nat)
(declare-fun l13 (Nat) Time)
(declare-fun l15 (Nat) Time)
(declare-fun l19 (Nat) Time)
(declare-fun l21 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-max-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-max-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-max-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-max-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-max-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-max-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-max-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-max-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-max-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-max-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-max-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-max-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l11 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l11 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-max-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-max-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-max-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-max-l11 () Bool)
(declare-lemma-predicate Prem-Intermed-max-l11 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l11 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l11 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-max-l11 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-max-l11 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-max-l11 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l11
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l11 zero)) 1)
            (= (max (l11 zero)) (a 0))
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl11 Nat))
            (=>
               (Sub Itl11 nl11)
               (< (i (l11 Itl11)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl11 Nat))
            (=>
               (Sub Itl11 nl11)
               (and
                  ;Semantics of IfElse at location l13
                  (and
                     ;Semantics of left branch
                     (=>
                        (> (a (i (l11 Itl11))) (max (l11 Itl11)))
                        (= (max (l21 Itl11)) (a (i (l11 Itl11))))
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (> (a (i (l11 Itl11))) (max (l11 Itl11)))
                        )
                        (= (max (l21 Itl11)) (max (l11 Itl11)))
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l11 (s Itl11))) (+ (i (l11 Itl11)) 1))
                  ;Define value of variable max at beginning of next iteration
                  (= (max (l11 (s Itl11))) (max (l21 Itl11)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l11 nl11)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (= (max main_end) (max (l11 nl11)))
   )
)

; Definition: Premise for value-evolution-eq-i-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (= (i (l11 boundL)) (i (l11 Itl11)))
               )
               (= (i (l11 boundL)) (i (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l11 boundL)) (i (l11 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (<= (i (l11 boundL)) (i (l11 Itl11)))
               )
               (<= (i (l11 boundL)) (i (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l11 boundL)) (i (l11 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (>= (i (l11 boundL)) (i (l11 Itl11)))
               )
               (>= (i (l11 boundL)) (i (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l11 boundL)) (i (l11 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-max-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-max-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (= (max (l11 boundL)) (max (l11 Itl11)))
               )
               (= (max (l11 boundL)) (max (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-max-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-max-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (max (l11 boundL)) (max (l11 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-max-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-max-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (<= (max (l11 boundL)) (max (l11 Itl11)))
               )
               (<= (max (l11 boundL)) (max (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-max-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-max-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (max (l11 boundL)) (max (l11 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-max-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-max-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (>= (max (l11 boundL)) (max (l11 Itl11)))
               )
               (>= (max (l11 boundL)) (max (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-max-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-max-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (max (l11 boundL)) (max (l11 boundR)))
         )
      )
   )
)

; Definition: Dense for i-l11
(assert
   (=
      Dense-i-l11
      (forall ((Itl11 Nat))
         (=>
            (Sub Itl11 nl11)
            (or
               (= (i (l11 (s Itl11))) (i (l11 Itl11)))
               (= (i (l11 (s Itl11))) (+ (i (l11 Itl11)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l11
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l11 xInt)
         (and
            (<= (i (l11 zero)) xInt)
            (< xInt (i (l11 nl11)))
            Dense-i-l11
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l11
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l11 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl11)
               (= (i (l11 it)) xInt)
               (= (i (l11 (s it))) (+ (i (l11 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for max-l11
(assert
   (=
      Dense-max-l11
      (forall ((Itl11 Nat))
         (=>
            (Sub Itl11 nl11)
            (or
               (= (max (l11 (s Itl11))) (max (l11 Itl11)))
               (= (max (l11 (s Itl11))) (+ (max (l11 Itl11)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-max-l11
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-max-l11 xInt)
         (and
            (<= (max (l11 zero)) xInt)
            (< xInt (max (l11 nl11)))
            Dense-max-l11
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-max-l11
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-max-l11 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl11)
               (= (max (l11 it)) xInt)
               (= (max (l11 (s it))) (+ (max (l11 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l11
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l11
            (= (i (l11 (s it1))) (+ (i (l11 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl11))
         )
         (not
            (= (i (l11 it1)) (i (l11 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-max-l11
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-max-l11
            (= (max (l11 (s it1))) (+ (max (l11 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl11))
         )
         (not
            (= (max (l11 it1)) (max (l11 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l11
(assert
   (=>
      (< (i (l11 zero)) alength)
      (exists ((Itl11 Nat))
         (= (s Itl11) nl11)
      )
   )
)

; Conjecture: user-conjecture-1
(assert-not
   (=>
      (<= 0 alength)
      (exists ((k Int))
         (and
            (<= 0 k)
            (< k alength)
            (= (a k) (max main_end))
         )
      )
   )
)

(check-sat)

