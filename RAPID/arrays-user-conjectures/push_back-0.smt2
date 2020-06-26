; main()
; {
;    alength = 0 @l9
;    i = 0 @l10
;    while (i < blength) @l11
;    {
;       a[i] = b[i] @l13
;       alength = (alength) + (1) @l14
;       i = (i) + (1) @l15
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
(declare-fun alength (Time) Int)
(declare-fun i (Time) Int)
(declare-const l9 Time)
(declare-const l10 Time)
(declare-fun l11 (Nat) Time)
(declare-const nl11 Nat)
(declare-fun l13 (Nat) Time)
(declare-fun l14 (Nat) Time)
(declare-fun l15 (Nat) Time)
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
(declare-lemma-predicate BC-AxEvol-eq-alength-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-alength-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-alength-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-alength-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-alength-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-alength-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-alength-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-alength-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-alength-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-alength-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-alength-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-alength-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-a-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-a-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-a-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-a-l11 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-a-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-a-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-a-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-a-l11 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-a-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-a-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-a-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-a-l11 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l11 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l11 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-alength-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-alength-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-alength-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-alength-l11 () Bool)
(declare-lemma-predicate Prem-Intermed-alength-l11 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l11 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l11 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-alength-l11 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-alength-l11 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-alength-l11 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l11
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l11 zero)) 0)
            (= (alength (l11 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl11 Nat))
            (=>
               (Sub Itl11 nl11)
               (< (i (l11 Itl11)) blength)
            )
         )
         ;Semantics of the body
         (forall ((Itl11 Nat))
            (=>
               (Sub Itl11 nl11)
               (and
                  ;Update array variable a at location l13
                  (and
                     (= (a (l14 Itl11) (i (l11 Itl11))) (b (i (l11 Itl11))))
                     (forall ((pos Int))
                        (=>
                           (not
                              (= pos (i (l11 Itl11)))
                           )
                           (= (a (l14 Itl11) pos) (a (l11 Itl11) pos))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l11 (s Itl11))) (+ (i (l11 Itl11)) 1))
                  ;Define value of variable alength at beginning of next iteration
                  (= (alength (l11 (s Itl11))) (+ (alength (l11 Itl11)) 1))
                  ;Define value of array variable a at beginning of next iteration
                  (forall ((pos Int))
                     (= (a (l11 (s Itl11)) pos) (a (l14 Itl11) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l11 nl11)) blength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (alength main_end) (alength (l11 nl11)))
         (forall ((pos Int))
            (= (a main_end pos) (a (l11 nl11) pos))
         )
      )
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

; Definition: Premise for value-evolution-eq-alength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-alength-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (= (alength (l11 boundL)) (alength (l11 Itl11)))
               )
               (= (alength (l11 boundL)) (alength (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-alength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-alength-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (alength (l11 boundL)) (alength (l11 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-alength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-alength-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (<= (alength (l11 boundL)) (alength (l11 Itl11)))
               )
               (<= (alength (l11 boundL)) (alength (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-alength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-alength-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (alength (l11 boundL)) (alength (l11 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-alength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-alength-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (>= (alength (l11 boundL)) (alength (l11 Itl11)))
               )
               (>= (alength (l11 boundL)) (alength (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-alength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-alength-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (alength (l11 boundL)) (alength (l11 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-a-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-a-l11 pos boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (= (a (l11 boundL) pos) (a (l11 Itl11) pos))
               )
               (= (a (l11 boundL) pos) (a (l11 (s Itl11)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-a-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-a-l11 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (a (l11 boundL) pos) (a (l11 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-a-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-a-l11 pos boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (<= (a (l11 boundL) pos) (a (l11 Itl11) pos))
               )
               (<= (a (l11 boundL) pos) (a (l11 (s Itl11)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-a-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-a-l11 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (a (l11 boundL) pos) (a (l11 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-a-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-a-l11 pos boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (>= (a (l11 boundL) pos) (a (l11 Itl11) pos))
               )
               (>= (a (l11 boundL) pos) (a (l11 (s Itl11)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-a-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-a-l11 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (a (l11 boundL) pos) (a (l11 boundR) pos))
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

; Definition: Dense for alength-l11
(assert
   (=
      Dense-alength-l11
      (forall ((Itl11 Nat))
         (=>
            (Sub Itl11 nl11)
            (or
               (= (alength (l11 (s Itl11))) (alength (l11 Itl11)))
               (= (alength (l11 (s Itl11))) (+ (alength (l11 Itl11)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-alength-l11
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-alength-l11 xInt)
         (and
            (<= (alength (l11 zero)) xInt)
            (< xInt (alength (l11 nl11)))
            Dense-alength-l11
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-alength-l11
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-alength-l11 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl11)
               (= (alength (l11 it)) xInt)
               (= (alength (l11 (s it))) (+ (alength (l11 it)) 1))
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

; Axiom: already-proven-lemma iterator-injectivity-alength-l11
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-alength-l11
            (= (alength (l11 (s it1))) (+ (alength (l11 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl11))
         )
         (not
            (= (alength (l11 it1)) (alength (l11 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l11
(assert
   (=>
      (< (i (l11 zero)) blength)
      (exists ((Itl11 Nat))
         (= (s Itl11) nl11)
      )
   )
)

; Axiom: user-axiom-0
(assert
   (forall ((it Nat))
      (<= (alength (l11 it)) (i (l11 it)))
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (forall ((j Int))
      (=>
         (and
            (<= 0 blength)
            (<= 0 j)
            (< j (alength main_end))
         )
         (= (a main_end j) (b j))
      )
   )
)

(check-sat)

