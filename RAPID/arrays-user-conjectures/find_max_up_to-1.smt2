; main()
; {
;    i = 0 @l8
;    m = 0 @l9
;    while (i < alength) @l10
;    {
;       if (a[i] > a[m]) @l12
;       {
;          b[i] = a[i] @l14
;          m = i @l15
;       }
;       else
;       {
;          b[i] = a[m] @l19
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
(declare-fun b (Time Int) Int)
(declare-fun i (Time) Int)
(declare-fun m (Time) Int)
(declare-const l8 Time)
(declare-const l9 Time)
(declare-fun l10 (Nat) Time)
(declare-const nl10 Nat)
(declare-fun l12 (Nat) Time)
(declare-fun l14 (Nat) Time)
(declare-fun l15 (Nat) Time)
(declare-fun l19 (Nat) Time)
(declare-fun l21 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-m-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-m-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-m-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-m-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-m-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-m-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-m-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-m-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-m-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-m-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-m-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-m-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-m-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-m-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-m-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-m-l10 () Bool)
(declare-lemma-predicate Prem-Intermed-m-l10 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l10 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l10 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-m-l10 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-m-l10 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-m-l10 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l10 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l10 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l10 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l10
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l10 zero)) 0)
            (= (m (l10 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl10 Nat))
            (=>
               (Sub Itl10 nl10)
               (< (i (l10 Itl10)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl10 Nat))
            (=>
               (Sub Itl10 nl10)
               (and
                  ;Semantics of IfElse at location l12
                  (and
                     ;Semantics of left branch
                     (=>
                        (> (a (i (l10 Itl10))) (a (m (l10 Itl10))))
                        (and
                           ;Update array variable b at location l14
                           (and
                              (= (b (l15 Itl10) (i (l10 Itl10))) (a (i (l10 Itl10))))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (i (l10 Itl10)))
                                    )
                                    (= (b (l15 Itl10) pos) (b (l10 Itl10) pos))
                                 )
                              )
                           )
                           (forall ((pos Int))
                              (= (b (l21 Itl10) pos) (b (l15 Itl10) pos))
                           )
                           (= (m (l21 Itl10)) (i (l10 Itl10)))
                        )
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (> (a (i (l10 Itl10))) (a (m (l10 Itl10))))
                        )
                        (and
                           ;Update array variable b at location l19
                           (and
                              (= (b (l21 Itl10) (i (l10 Itl10))) (a (m (l10 Itl10))))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (i (l10 Itl10)))
                                    )
                                    (= (b (l21 Itl10) pos) (b (l10 Itl10) pos))
                                 )
                              )
                           )
                           (= (m (l21 Itl10)) (m (l10 Itl10)))
                        )
                     )
                  )
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l10 (s Itl10)) pos) (b (l21 Itl10) pos))
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l10 (s Itl10))) (+ (i (l10 Itl10)) 1))
                  ;Define value of variable m at beginning of next iteration
                  (= (m (l10 (s Itl10))) (m (l21 Itl10)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l10 nl10)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (forall ((pos Int))
         (= (b main_end pos) (b (l10 nl10) pos))
      )
   )
)

; Definition: Premise for value-evolution-eq-m-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-m-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (= (m (l10 boundL)) (m (l10 Itl10)))
               )
               (= (m (l10 boundL)) (m (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-m-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-m-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (m (l10 boundL)) (m (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-m-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-m-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (<= (m (l10 boundL)) (m (l10 Itl10)))
               )
               (<= (m (l10 boundL)) (m (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-m-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-m-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (m (l10 boundL)) (m (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-m-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-m-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (>= (m (l10 boundL)) (m (l10 Itl10)))
               )
               (>= (m (l10 boundL)) (m (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-m-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-m-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (m (l10 boundL)) (m (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (= (i (l10 boundL)) (i (l10 Itl10)))
               )
               (= (i (l10 boundL)) (i (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l10 boundL)) (i (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (<= (i (l10 boundL)) (i (l10 Itl10)))
               )
               (<= (i (l10 boundL)) (i (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l10 boundL)) (i (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (>= (i (l10 boundL)) (i (l10 Itl10)))
               )
               (>= (i (l10 boundL)) (i (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l10 boundL)) (i (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (= (b (l10 boundL) pos) (b (l10 Itl10) pos))
               )
               (= (b (l10 boundL) pos) (b (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l10 boundL) pos) (b (l10 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (<= (b (l10 boundL) pos) (b (l10 Itl10) pos))
               )
               (<= (b (l10 boundL) pos) (b (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l10 boundL) pos) (b (l10 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (>= (b (l10 boundL) pos) (b (l10 Itl10) pos))
               )
               (>= (b (l10 boundL) pos) (b (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l10 boundL) pos) (b (l10 boundR) pos))
         )
      )
   )
)

; Definition: Dense for m-l10
(assert
   (=
      Dense-m-l10
      (forall ((Itl10 Nat))
         (=>
            (Sub Itl10 nl10)
            (or
               (= (m (l10 (s Itl10))) (m (l10 Itl10)))
               (= (m (l10 (s Itl10))) (+ (m (l10 Itl10)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-m-l10
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-m-l10 xInt)
         (and
            (<= (m (l10 zero)) xInt)
            (< xInt (m (l10 nl10)))
            Dense-m-l10
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-m-l10
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-m-l10 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl10)
               (= (m (l10 it)) xInt)
               (= (m (l10 (s it))) (+ (m (l10 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l10
(assert
   (=
      Dense-i-l10
      (forall ((Itl10 Nat))
         (=>
            (Sub Itl10 nl10)
            (or
               (= (i (l10 (s Itl10))) (i (l10 Itl10)))
               (= (i (l10 (s Itl10))) (+ (i (l10 Itl10)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l10
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l10 xInt)
         (and
            (<= (i (l10 zero)) xInt)
            (< xInt (i (l10 nl10)))
            Dense-i-l10
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l10
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l10 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl10)
               (= (i (l10 it)) xInt)
               (= (i (l10 (s it))) (+ (i (l10 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-m-l10
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-m-l10
            (= (m (l10 (s it1))) (+ (m (l10 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl10))
         )
         (not
            (= (m (l10 it1)) (m (l10 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l10
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l10
            (= (i (l10 (s it1))) (+ (i (l10 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl10))
         )
         (not
            (= (i (l10 it1)) (i (l10 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l10
(assert
   (=>
      (< (i (l10 zero)) alength)
      (exists ((Itl10 Nat))
         (= (s Itl10) nl10)
      )
   )
)

; Conjecture: user-conjecture-1
(assert-not
   (forall ((j Int))
      (exists ((k Int))
         (=>
            (and
               (<= 0 alength)
               (<= 0 j)
               (< j alength)
            )
            (and
               (<= 0 k)
               (<= k j)
               (= (b main_end j) (a k))
            )
         )
      )
   )
)

(check-sat)

