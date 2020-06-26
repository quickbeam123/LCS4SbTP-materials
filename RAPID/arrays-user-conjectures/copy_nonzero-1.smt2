; main()
; {
;    i = 0 @l8
;    alength = 0 @l9
;    while (i < blength) @l10
;    {
;       if (!(b[i] == 0)) @l12
;       {
;          a[alength] = b[i] @l14
;          alength = (alength) + (1) @l15
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
(declare-fun a (Time Int) Int)
(declare-fun b (Int) Int)
(declare-const blength Int)
(declare-fun i (Time) Int)
(declare-fun alength (Time) Int)
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
(declare-lemma-predicate BC-AxEvol-eq-alength-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-alength-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-alength-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-alength-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-alength-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-alength-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-alength-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-alength-l10 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-alength-l10 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-alength-l10 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-alength-l10 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-alength-l10 (Nat Nat) Bool)
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
(declare-lemma-predicate BC-AxEvol-eq-a-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l10 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-alength-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-alength-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-alength-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-alength-l10 () Bool)
(declare-lemma-predicate Prem-Intermed-alength-l10 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l10 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l10 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l10 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l10 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-alength-l10 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-alength-l10 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-alength-l10 (Nat Nat Nat) Bool)
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
            (= (alength (l10 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl10 Nat))
            (=>
               (Sub Itl10 nl10)
               (< (i (l10 Itl10)) blength)
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
                        (not
                           (= (b (i (l10 Itl10))) 0)
                        )
                        (and
                           ;Update array variable a at location l14
                           (and
                              (= (a (l15 Itl10) (alength (l10 Itl10))) (b (i (l10 Itl10))))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (alength (l10 Itl10)))
                                    )
                                    (= (a (l15 Itl10) pos) (a (l10 Itl10) pos))
                                 )
                              )
                           )
                           (forall ((pos Int))
                              (= (a (l21 Itl10) pos) (a (l15 Itl10) pos))
                           )
                           (= (alength (l21 Itl10)) (+ (alength (l10 Itl10)) 1))
                        )
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (not
                              (= (b (i (l10 Itl10))) 0)
                           )
                        )
                        (and
                           (forall ((pos Int))
                              (= (a (l21 Itl10) pos) (a (l10 Itl10) pos))
                           )
                           (= (alength (l21 Itl10)) (alength (l10 Itl10)))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l10 (s Itl10))) (+ (i (l10 Itl10)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l10 (s Itl10)) pos) (a (l21 Itl10) pos))
                  )
                  ;Define value of variable alength at beginning of next iteration
                  (= (alength (l10 (s Itl10))) (alength (l21 Itl10)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l10 nl10)) blength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (alength main_end) (alength (l10 nl10)))
         (forall ((pos Int))
            (= (a main_end pos) (a (l10 nl10) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-alength-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-alength-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (= (alength (l10 boundL)) (alength (l10 Itl10)))
               )
               (= (alength (l10 boundL)) (alength (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-alength-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-alength-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (alength (l10 boundL)) (alength (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-alength-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-alength-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (<= (alength (l10 boundL)) (alength (l10 Itl10)))
               )
               (<= (alength (l10 boundL)) (alength (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-alength-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-alength-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (alength (l10 boundL)) (alength (l10 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-alength-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-alength-l10 boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (>= (alength (l10 boundL)) (alength (l10 Itl10)))
               )
               (>= (alength (l10 boundL)) (alength (l10 (s Itl10))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-alength-l10
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-alength-l10 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (alength (l10 boundL)) (alength (l10 boundR)))
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

; Definition: Premise for value-evolution-eq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (= (a (l10 boundL) pos) (a (l10 Itl10) pos))
               )
               (= (a (l10 boundL) pos) (a (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l10 boundL) pos) (a (l10 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (<= (a (l10 boundL) pos) (a (l10 Itl10) pos))
               )
               (<= (a (l10 boundL) pos) (a (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l10 boundL) pos) (a (l10 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l10 pos boundL boundR)
         (forall ((Itl10 Nat))
            (=>
               (and
                  (Sub boundL (s Itl10))
                  (Sub Itl10 boundR)
                  (>= (a (l10 boundL) pos) (a (l10 Itl10) pos))
               )
               (>= (a (l10 boundL) pos) (a (l10 (s Itl10)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l10
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l10 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l10 boundL) pos) (a (l10 boundR) pos))
         )
      )
   )
)

; Definition: Dense for alength-l10
(assert
   (=
      Dense-alength-l10
      (forall ((Itl10 Nat))
         (=>
            (Sub Itl10 nl10)
            (or
               (= (alength (l10 (s Itl10))) (alength (l10 Itl10)))
               (= (alength (l10 (s Itl10))) (+ (alength (l10 Itl10)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-alength-l10
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-alength-l10 xInt)
         (and
            (<= (alength (l10 zero)) xInt)
            (< xInt (alength (l10 nl10)))
            Dense-alength-l10
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-alength-l10
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-alength-l10 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl10)
               (= (alength (l10 it)) xInt)
               (= (alength (l10 (s it))) (+ (alength (l10 it)) 1))
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

; Axiom: already-proven-lemma iterator-injectivity-alength-l10
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-alength-l10
            (= (alength (l10 (s it1))) (+ (alength (l10 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl10))
         )
         (not
            (= (alength (l10 it1)) (alength (l10 it2)))
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
      (< (i (l10 zero)) blength)
      (exists ((Itl10 Nat))
         (= (s Itl10) nl10)
      )
   )
)

; Conjecture: user-conjecture-1
(assert-not
   (forall ((k Int))
      (exists ((l Int))
         (=>
            (and
               (<= 0 k)
               (<= 0 blength)
               (< k (alength main_end))
            )
            (= (a main_end k) (b l))
         )
      )
   )
)

(check-sat)

