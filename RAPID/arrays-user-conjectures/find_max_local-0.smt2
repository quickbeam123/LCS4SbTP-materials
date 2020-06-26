; main()
; {
;    b[0] = a[0] @l8
;    blength = 1 @l9
;    i = 1 @l11
;    m = 0 @l12
;    while (i < alength) @l13
;    {
;       if (a[i] > a[m]) @l15
;       {
;          b[i] = a[i] @l17
;          blength = (blength) + (1) @l18
;          m = i @l19
;       }
;       else
;       {
;          skip @l23
;       }
;       i = (i) + (1) @l25
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
(declare-fun blength (Time) Int)
(declare-fun i (Time) Int)
(declare-fun m (Time) Int)
(declare-const l8 Time)
(declare-const l9 Time)
(declare-const l11 Time)
(declare-const l12 Time)
(declare-fun l13 (Nat) Time)
(declare-const nl13 Nat)
(declare-fun l15 (Nat) Time)
(declare-fun l17 (Nat) Time)
(declare-fun l18 (Nat) Time)
(declare-fun l19 (Nat) Time)
(declare-fun l23 (Nat) Time)
(declare-fun l25 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-m-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-m-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-m-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-m-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-m-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-m-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-m-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-m-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-m-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-m-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-m-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-m-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-blength-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-blength-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-blength-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-blength-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-blength-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-blength-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-blength-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-blength-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-blength-l13 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-blength-l13 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-blength-l13 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-blength-l13 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l13 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l13 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l13 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l13 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l13 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-m-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-m-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-m-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-m-l13 () Bool)
(declare-lemma-predicate Prem-Intermed-m-l13 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-blength-l13 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-blength-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-blength-l13 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-blength-l13 () Bool)
(declare-lemma-predicate Prem-Intermed-blength-l13 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l13 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l13 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l13 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-m-l13 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-m-l13 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-m-l13 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-blength-l13 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-blength-l13 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-blength-l13 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Update array variable b at location l8
      (and
         (= (b l9 0) (a 0))
         (forall ((pos Int))
            (=>
               (not
                  (= pos 0)
               )
               (= (b l9 pos) (b l8 pos))
            )
         )
      )
      ;Loop at location l13
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l13 zero)) 1)
            (forall ((pos Int))
               (= (b (l13 zero) pos) (b l9 pos))
            )
            (= (m (l13 zero)) 0)
            (= (blength (l13 zero)) 1)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl13 Nat))
            (=>
               (Sub Itl13 nl13)
               (< (i (l13 Itl13)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl13 Nat))
            (=>
               (Sub Itl13 nl13)
               (and
                  ;Semantics of IfElse at location l15
                  (and
                     ;Semantics of left branch
                     (=>
                        (> (a (i (l13 Itl13))) (a (m (l13 Itl13))))
                        (and
                           ;Update array variable b at location l17
                           (and
                              (= (b (l18 Itl13) (i (l13 Itl13))) (a (i (l13 Itl13))))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (i (l13 Itl13)))
                                    )
                                    (= (b (l18 Itl13) pos) (b (l13 Itl13) pos))
                                 )
                              )
                           )
                           (= (blength (l25 Itl13)) (+ (blength (l13 Itl13)) 1))
                           (forall ((pos Int))
                              (= (b (l25 Itl13) pos) (b (l18 Itl13) pos))
                           )
                           (= (m (l25 Itl13)) (i (l13 Itl13)))
                        )
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (> (a (i (l13 Itl13))) (a (m (l13 Itl13))))
                        )
                        (and
                           (= (blength (l25 Itl13)) (blength (l13 Itl13)))
                           (forall ((pos Int))
                              (= (b (l25 Itl13) pos) (b (l13 Itl13) pos))
                           )
                           (= (m (l25 Itl13)) (m (l13 Itl13)))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l13 (s Itl13))) (+ (i (l13 Itl13)) 1))
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l13 (s Itl13)) pos) (b (l25 Itl13) pos))
                  )
                  ;Define value of variable m at beginning of next iteration
                  (= (m (l13 (s Itl13))) (m (l25 Itl13)))
                  ;Define value of variable blength at beginning of next iteration
                  (= (blength (l13 (s Itl13))) (blength (l25 Itl13)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l13 nl13)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (blength main_end) (blength (l13 nl13)))
         (forall ((pos Int))
            (= (b main_end pos) (b (l13 nl13) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (= (i (l13 boundL)) (i (l13 Itl13)))
               )
               (= (i (l13 boundL)) (i (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l13 boundL)) (i (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (<= (i (l13 boundL)) (i (l13 Itl13)))
               )
               (<= (i (l13 boundL)) (i (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l13 boundL)) (i (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (>= (i (l13 boundL)) (i (l13 Itl13)))
               )
               (>= (i (l13 boundL)) (i (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l13 boundL)) (i (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-m-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-m-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (= (m (l13 boundL)) (m (l13 Itl13)))
               )
               (= (m (l13 boundL)) (m (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-m-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-m-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (m (l13 boundL)) (m (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-m-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-m-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (<= (m (l13 boundL)) (m (l13 Itl13)))
               )
               (<= (m (l13 boundL)) (m (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-m-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-m-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (m (l13 boundL)) (m (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-m-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-m-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (>= (m (l13 boundL)) (m (l13 Itl13)))
               )
               (>= (m (l13 boundL)) (m (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-m-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-m-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (m (l13 boundL)) (m (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-blength-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-blength-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (= (blength (l13 boundL)) (blength (l13 Itl13)))
               )
               (= (blength (l13 boundL)) (blength (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-blength-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-blength-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (blength (l13 boundL)) (blength (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-blength-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-blength-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (<= (blength (l13 boundL)) (blength (l13 Itl13)))
               )
               (<= (blength (l13 boundL)) (blength (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-blength-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-blength-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (blength (l13 boundL)) (blength (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-blength-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-blength-l13 boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (>= (blength (l13 boundL)) (blength (l13 Itl13)))
               )
               (>= (blength (l13 boundL)) (blength (l13 (s Itl13))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-blength-l13
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-blength-l13 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (blength (l13 boundL)) (blength (l13 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l13 pos boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (= (b (l13 boundL) pos) (b (l13 Itl13) pos))
               )
               (= (b (l13 boundL) pos) (b (l13 (s Itl13)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l13 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l13 boundL) pos) (b (l13 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l13 pos boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (<= (b (l13 boundL) pos) (b (l13 Itl13) pos))
               )
               (<= (b (l13 boundL) pos) (b (l13 (s Itl13)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l13 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l13 boundL) pos) (b (l13 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l13 pos boundL boundR)
         (forall ((Itl13 Nat))
            (=>
               (and
                  (Sub boundL (s Itl13))
                  (Sub Itl13 boundR)
                  (>= (b (l13 boundL) pos) (b (l13 Itl13) pos))
               )
               (>= (b (l13 boundL) pos) (b (l13 (s Itl13)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l13
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l13 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l13 boundL) pos) (b (l13 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l13
(assert
   (=
      Dense-i-l13
      (forall ((Itl13 Nat))
         (=>
            (Sub Itl13 nl13)
            (or
               (= (i (l13 (s Itl13))) (i (l13 Itl13)))
               (= (i (l13 (s Itl13))) (+ (i (l13 Itl13)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l13
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l13 xInt)
         (and
            (<= (i (l13 zero)) xInt)
            (< xInt (i (l13 nl13)))
            Dense-i-l13
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l13
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l13 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl13)
               (= (i (l13 it)) xInt)
               (= (i (l13 (s it))) (+ (i (l13 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for m-l13
(assert
   (=
      Dense-m-l13
      (forall ((Itl13 Nat))
         (=>
            (Sub Itl13 nl13)
            (or
               (= (m (l13 (s Itl13))) (m (l13 Itl13)))
               (= (m (l13 (s Itl13))) (+ (m (l13 Itl13)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-m-l13
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-m-l13 xInt)
         (and
            (<= (m (l13 zero)) xInt)
            (< xInt (m (l13 nl13)))
            Dense-m-l13
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-m-l13
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-m-l13 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl13)
               (= (m (l13 it)) xInt)
               (= (m (l13 (s it))) (+ (m (l13 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for blength-l13
(assert
   (=
      Dense-blength-l13
      (forall ((Itl13 Nat))
         (=>
            (Sub Itl13 nl13)
            (or
               (= (blength (l13 (s Itl13))) (blength (l13 Itl13)))
               (= (blength (l13 (s Itl13))) (+ (blength (l13 Itl13)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-blength-l13
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-blength-l13 xInt)
         (and
            (<= (blength (l13 zero)) xInt)
            (< xInt (blength (l13 nl13)))
            Dense-blength-l13
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-blength-l13
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-blength-l13 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl13)
               (= (blength (l13 it)) xInt)
               (= (blength (l13 (s it))) (+ (blength (l13 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l13
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l13
            (= (i (l13 (s it1))) (+ (i (l13 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl13))
         )
         (not
            (= (i (l13 it1)) (i (l13 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-m-l13
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-m-l13
            (= (m (l13 (s it1))) (+ (m (l13 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl13))
         )
         (not
            (= (m (l13 it1)) (m (l13 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-blength-l13
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-blength-l13
            (= (blength (l13 (s it1))) (+ (blength (l13 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl13))
         )
         (not
            (= (blength (l13 it1)) (blength (l13 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l13
(assert
   (=>
      (< (i (l13 zero)) alength)
      (exists ((Itl13 Nat))
         (= (s Itl13) nl13)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (forall ((k Int))
      (=>
         (and
            (<= 1 alength)
            (<= 0 k)
            (< k alength)
            (forall ((l Int))
               (=>
                  (and
                     (<= 0 l)
                     (< l k)
                  )
                  (< (a l) (a k))
               )
            )
         )
         (exists ((j Int))
            (and
               (<= 0 j)
               (< j (blength main_end))
               (= (a k) (b main_end j))
            )
         )
      )
   )
)

(check-sat)

