; main()
; {
;    blength = 0 @l15
;    i = 0 @l17
;    while (i < alength) @l18
;    {
;       if (a1[i] == a2[i]) @l20
;       {
;          b[blength] = i @l22
;          blength = (blength) + (1) @l23
;       }
;       else
;       {
;          skip @l27
;       }
;       i = (i) + (1) @l29
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a1 (Int) Int)
(declare-fun a2 (Int) Int)
(declare-const alength Int)
(declare-fun b (Time Int) Int)
(declare-fun blength (Time) Int)
(declare-fun i (Time) Int)
(declare-const l15 Time)
(declare-const l17 Time)
(declare-fun l18 (Nat) Time)
(declare-const nl18 Nat)
(declare-fun l20 (Nat) Time)
(declare-fun l22 (Nat) Time)
(declare-fun l23 (Nat) Time)
(declare-fun l27 (Nat) Time)
(declare-fun l29 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-blength-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-blength-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-blength-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-blength-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-blength-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-blength-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-blength-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-blength-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-blength-l18 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-blength-l18 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-blength-l18 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-blength-l18 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l18 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l18 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l18 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l18 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l18 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-blength-l18 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-blength-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-blength-l18 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-blength-l18 () Bool)
(declare-lemma-predicate Prem-Intermed-blength-l18 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l18 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l18 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l18 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-blength-l18 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-blength-l18 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-blength-l18 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l18
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l18 zero)) 0)
            (= (blength (l18 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl18 Nat))
            (=>
               (Sub Itl18 nl18)
               (< (i (l18 Itl18)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl18 Nat))
            (=>
               (Sub Itl18 nl18)
               (and
                  ;Semantics of IfElse at location l20
                  (and
                     ;Semantics of left branch
                     (=>
                        (= (a1 (i (l18 Itl18))) (a2 (i (l18 Itl18))))
                        (and
                           ;Update array variable b at location l22
                           (and
                              (= (b (l23 Itl18) (blength (l18 Itl18))) (i (l18 Itl18)))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (blength (l18 Itl18)))
                                    )
                                    (= (b (l23 Itl18) pos) (b (l18 Itl18) pos))
                                 )
                              )
                           )
                           (forall ((pos Int))
                              (= (b (l29 Itl18) pos) (b (l23 Itl18) pos))
                           )
                           (= (blength (l29 Itl18)) (+ (blength (l18 Itl18)) 1))
                        )
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (= (a1 (i (l18 Itl18))) (a2 (i (l18 Itl18))))
                        )
                        (and
                           (forall ((pos Int))
                              (= (b (l29 Itl18) pos) (b (l18 Itl18) pos))
                           )
                           (= (blength (l29 Itl18)) (blength (l18 Itl18)))
                        )
                     )
                  )
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l18 (s Itl18)) pos) (b (l29 Itl18) pos))
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l18 (s Itl18))) (+ (i (l18 Itl18)) 1))
                  ;Define value of variable blength at beginning of next iteration
                  (= (blength (l18 (s Itl18))) (blength (l29 Itl18)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l18 nl18)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (blength main_end) (blength (l18 nl18)))
         (forall ((pos Int))
            (= (b main_end pos) (b (l18 nl18) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (= (i (l18 boundL)) (i (l18 Itl18)))
               )
               (= (i (l18 boundL)) (i (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l18 boundL)) (i (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (<= (i (l18 boundL)) (i (l18 Itl18)))
               )
               (<= (i (l18 boundL)) (i (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l18 boundL)) (i (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (>= (i (l18 boundL)) (i (l18 Itl18)))
               )
               (>= (i (l18 boundL)) (i (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l18 boundL)) (i (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-blength-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-blength-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (= (blength (l18 boundL)) (blength (l18 Itl18)))
               )
               (= (blength (l18 boundL)) (blength (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-blength-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-blength-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (blength (l18 boundL)) (blength (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-blength-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-blength-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (<= (blength (l18 boundL)) (blength (l18 Itl18)))
               )
               (<= (blength (l18 boundL)) (blength (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-blength-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-blength-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (blength (l18 boundL)) (blength (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-blength-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-blength-l18 boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (>= (blength (l18 boundL)) (blength (l18 Itl18)))
               )
               (>= (blength (l18 boundL)) (blength (l18 (s Itl18))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-blength-l18
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-blength-l18 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (blength (l18 boundL)) (blength (l18 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l18 pos boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (= (b (l18 boundL) pos) (b (l18 Itl18) pos))
               )
               (= (b (l18 boundL) pos) (b (l18 (s Itl18)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l18 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l18 boundL) pos) (b (l18 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l18 pos boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (<= (b (l18 boundL) pos) (b (l18 Itl18) pos))
               )
               (<= (b (l18 boundL) pos) (b (l18 (s Itl18)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l18 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l18 boundL) pos) (b (l18 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l18 pos boundL boundR)
         (forall ((Itl18 Nat))
            (=>
               (and
                  (Sub boundL (s Itl18))
                  (Sub Itl18 boundR)
                  (>= (b (l18 boundL) pos) (b (l18 Itl18) pos))
               )
               (>= (b (l18 boundL) pos) (b (l18 (s Itl18)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l18
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l18 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l18 boundL) pos) (b (l18 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l18
(assert
   (=
      Dense-i-l18
      (forall ((Itl18 Nat))
         (=>
            (Sub Itl18 nl18)
            (or
               (= (i (l18 (s Itl18))) (i (l18 Itl18)))
               (= (i (l18 (s Itl18))) (+ (i (l18 Itl18)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l18
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l18 xInt)
         (and
            (<= (i (l18 zero)) xInt)
            (< xInt (i (l18 nl18)))
            Dense-i-l18
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l18
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l18 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl18)
               (= (i (l18 it)) xInt)
               (= (i (l18 (s it))) (+ (i (l18 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for blength-l18
(assert
   (=
      Dense-blength-l18
      (forall ((Itl18 Nat))
         (=>
            (Sub Itl18 nl18)
            (or
               (= (blength (l18 (s Itl18))) (blength (l18 Itl18)))
               (= (blength (l18 (s Itl18))) (+ (blength (l18 Itl18)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-blength-l18
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-blength-l18 xInt)
         (and
            (<= (blength (l18 zero)) xInt)
            (< xInt (blength (l18 nl18)))
            Dense-blength-l18
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-blength-l18
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-blength-l18 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl18)
               (= (blength (l18 it)) xInt)
               (= (blength (l18 (s it))) (+ (blength (l18 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l18
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l18
            (= (i (l18 (s it1))) (+ (i (l18 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl18))
         )
         (not
            (= (i (l18 it1)) (i (l18 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-blength-l18
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-blength-l18
            (= (blength (l18 (s it1))) (+ (blength (l18 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl18))
         )
         (not
            (= (blength (l18 it1)) (blength (l18 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l18
(assert
   (=>
      (< (i (l18 zero)) alength)
      (exists ((Itl18 Nat))
         (= (s Itl18) nl18)
      )
   )
)

; Conjecture: user-conjecture-3
(assert-not
   (forall ((pos Int))
      (=>
         (and
            (<= 0 alength)
            (<= 0 pos)
            (< pos alength)
            (= (a1 pos) (a2 pos))
         )
         (exists ((pos2 Int))
            (and
               (<= 0 pos2)
               (< pos2 (blength main_end))
               (= (b main_end pos2) pos)
            )
         )
      )
   )
)

(check-sat)

