; main()
; {
;    i = 0 @l7
;    alength = 0 @l8
;    while (i < blength) @l9
;    {
;       if (b[i] >= 0) @l11
;       {
;          a[alength] = b[i] @l13
;          alength = (alength) + (1) @l14
;       }
;       else
;       {
;          skip @l18
;       }
;       i = (i) + (1) @l20
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Time Int) Int)
(declare-fun b (Int) Int)
(declare-const blength Int)
(declare-fun i (Time) Int)
(declare-fun alength (Time) Int)
(declare-const l7 Time)
(declare-const l8 Time)
(declare-fun l9 (Nat) Time)
(declare-const nl9 Nat)
(declare-fun l11 (Nat) Time)
(declare-fun l13 (Nat) Time)
(declare-fun l14 (Nat) Time)
(declare-fun l18 (Nat) Time)
(declare-fun l20 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-alength-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-alength-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-alength-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l9 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l9 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-alength-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-alength-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-alength-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-alength-l9 () Bool)
(declare-lemma-predicate Prem-Intermed-alength-l9 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l9 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l9 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l9 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l9 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-alength-l9 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-alength-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-alength-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l9 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l9 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l9 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l9
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l9 zero)) 0)
            (= (alength (l9 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               (< (i (l9 Itl9)) blength)
            )
         )
         ;Semantics of the body
         (forall ((Itl9 Nat))
            (=>
               (Sub Itl9 nl9)
               (and
                  ;Semantics of IfElse at location l11
                  (and
                     ;Semantics of left branch
                     (=>
                        (>= (b (i (l9 Itl9))) 0)
                        (and
                           ;Update array variable a at location l13
                           (and
                              (= (a (l14 Itl9) (alength (l9 Itl9))) (b (i (l9 Itl9))))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (alength (l9 Itl9)))
                                    )
                                    (= (a (l14 Itl9) pos) (a (l9 Itl9) pos))
                                 )
                              )
                           )
                           (forall ((pos Int))
                              (= (a (l20 Itl9) pos) (a (l14 Itl9) pos))
                           )
                           (= (alength (l20 Itl9)) (+ (alength (l9 Itl9)) 1))
                        )
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (>= (b (i (l9 Itl9))) 0)
                        )
                        (and
                           (forall ((pos Int))
                              (= (a (l20 Itl9) pos) (a (l9 Itl9) pos))
                           )
                           (= (alength (l20 Itl9)) (alength (l9 Itl9)))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l9 (s Itl9))) (+ (i (l9 Itl9)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l9 (s Itl9)) pos) (a (l20 Itl9) pos))
                  )
                  ;Define value of variable alength at beginning of next iteration
                  (= (alength (l9 (s Itl9))) (alength (l20 Itl9)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l9 nl9)) blength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (alength main_end) (alength (l9 nl9)))
         (forall ((pos Int))
            (= (a main_end pos) (a (l9 nl9) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-alength-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (alength (l9 boundL)) (alength (l9 Itl9)))
               )
               (= (alength (l9 boundL)) (alength (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-alength-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (alength (l9 boundL)) (alength (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-alength-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (alength (l9 boundL)) (alength (l9 Itl9)))
               )
               (<= (alength (l9 boundL)) (alength (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-alength-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (alength (l9 boundL)) (alength (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-alength-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (alength (l9 boundL)) (alength (l9 Itl9)))
               )
               (>= (alength (l9 boundL)) (alength (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-alength-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-alength-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (alength (l9 boundL)) (alength (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (<= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l9 boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (i (l9 boundL)) (i (l9 Itl9)))
               )
               (>= (i (l9 boundL)) (i (l9 (s Itl9))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l9
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l9 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l9 boundL)) (i (l9 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l9 boundL) pos) (a (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (<= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (<= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l9 boundL) pos) (a (l9 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l9 pos boundL boundR)
         (forall ((Itl9 Nat))
            (=>
               (and
                  (Sub boundL (s Itl9))
                  (Sub Itl9 boundR)
                  (>= (a (l9 boundL) pos) (a (l9 Itl9) pos))
               )
               (>= (a (l9 boundL) pos) (a (l9 (s Itl9)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l9
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l9 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l9 boundL) pos) (a (l9 boundR) pos))
         )
      )
   )
)

; Definition: Dense for alength-l9
(assert
   (=
      Dense-alength-l9
      (forall ((Itl9 Nat))
         (=>
            (Sub Itl9 nl9)
            (or
               (= (alength (l9 (s Itl9))) (alength (l9 Itl9)))
               (= (alength (l9 (s Itl9))) (+ (alength (l9 Itl9)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-alength-l9
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-alength-l9 xInt)
         (and
            (<= (alength (l9 zero)) xInt)
            (< xInt (alength (l9 nl9)))
            Dense-alength-l9
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-alength-l9
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-alength-l9 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl9)
               (= (alength (l9 it)) xInt)
               (= (alength (l9 (s it))) (+ (alength (l9 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l9
(assert
   (=
      Dense-i-l9
      (forall ((Itl9 Nat))
         (=>
            (Sub Itl9 nl9)
            (or
               (= (i (l9 (s Itl9))) (i (l9 Itl9)))
               (= (i (l9 (s Itl9))) (+ (i (l9 Itl9)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l9
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l9 xInt)
         (and
            (<= (i (l9 zero)) xInt)
            (< xInt (i (l9 nl9)))
            Dense-i-l9
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l9
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l9 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl9)
               (= (i (l9 it)) xInt)
               (= (i (l9 (s it))) (+ (i (l9 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-alength-l9
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-alength-l9
            (= (alength (l9 (s it1))) (+ (alength (l9 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl9))
         )
         (not
            (= (alength (l9 it1)) (alength (l9 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l9
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l9
            (= (i (l9 (s it1))) (+ (i (l9 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl9))
         )
         (not
            (= (i (l9 it1)) (i (l9 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l9
(assert
   (=>
      (< (i (l9 zero)) blength)
      (exists ((Itl9 Nat))
         (= (s Itl9) nl9)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (forall ((k Int))
      (=>
         (and
            (<= 0 k)
            (< k (alength main_end))
            (<= 0 blength)
         )
         (<= 0 (a main_end k))
      )
   )
)

(check-sat)

