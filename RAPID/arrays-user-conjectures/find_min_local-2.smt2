; main()
; {
;    b[0] = a[0] @l9
;    blength = 1 @l10
;    i = 0 @l12
;    m = 0 @l13
;    while (i < alength) @l14
;    {
;       if (a[i] < a[m]) @l16
;       {
;          b[i] = a[i] @l18
;          blength = (blength) + (1) @l19
;          m = i @l20
;       }
;       else
;       {
;          skip @l24
;       }
;       i = (i) + (1) @l26
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
(declare-const l9 Time)
(declare-const l10 Time)
(declare-const l12 Time)
(declare-const l13 Time)
(declare-fun l14 (Nat) Time)
(declare-const nl14 Nat)
(declare-fun l16 (Nat) Time)
(declare-fun l18 (Nat) Time)
(declare-fun l19 (Nat) Time)
(declare-fun l20 (Nat) Time)
(declare-fun l24 (Nat) Time)
(declare-fun l26 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-m-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-m-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-m-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-m-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-m-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-m-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-m-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-m-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-m-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-m-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-m-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-m-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-blength-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-blength-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-blength-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-blength-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-blength-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-blength-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-blength-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-blength-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-blength-l14 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-blength-l14 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-blength-l14 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-blength-l14 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l14 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l14 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l14 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l14 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l14 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l14 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l14 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l14 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l14 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-m-l14 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-m-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-m-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-m-l14 () Bool)
(declare-lemma-predicate Prem-Intermed-m-l14 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-blength-l14 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-blength-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-blength-l14 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-blength-l14 () Bool)
(declare-lemma-predicate Prem-Intermed-blength-l14 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l14 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l14 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l14 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-m-l14 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-m-l14 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-m-l14 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-blength-l14 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-blength-l14 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-blength-l14 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Update array variable b at location l9
      (and
         (= (b l10 0) (a 0))
         (forall ((pos Int))
            (=>
               (not
                  (= pos 0)
               )
               (= (b l10 pos) (b l9 pos))
            )
         )
      )
      ;Loop at location l14
      (and
         ;Define variable values at beginning of loop
         (and
            (forall ((pos Int))
               (= (b (l14 zero) pos) (b l10 pos))
            )
            (= (blength (l14 zero)) 1)
            (= (i (l14 zero)) 0)
            (= (m (l14 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl14 Nat))
            (=>
               (Sub Itl14 nl14)
               (< (i (l14 Itl14)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl14 Nat))
            (=>
               (Sub Itl14 nl14)
               (and
                  ;Semantics of IfElse at location l16
                  (and
                     ;Semantics of left branch
                     (=>
                        (< (a (i (l14 Itl14))) (a (m (l14 Itl14))))
                        (and
                           ;Update array variable b at location l18
                           (and
                              (= (b (l19 Itl14) (i (l14 Itl14))) (a (i (l14 Itl14))))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (i (l14 Itl14)))
                                    )
                                    (= (b (l19 Itl14) pos) (b (l14 Itl14) pos))
                                 )
                              )
                           )
                           (forall ((pos Int))
                              (= (b (l26 Itl14) pos) (b (l19 Itl14) pos))
                           )
                           (= (blength (l26 Itl14)) (+ (blength (l14 Itl14)) 1))
                           (= (m (l26 Itl14)) (i (l14 Itl14)))
                        )
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (< (a (i (l14 Itl14))) (a (m (l14 Itl14))))
                        )
                        (and
                           (forall ((pos Int))
                              (= (b (l26 Itl14) pos) (b (l14 Itl14) pos))
                           )
                           (= (blength (l26 Itl14)) (blength (l14 Itl14)))
                           (= (m (l26 Itl14)) (m (l14 Itl14)))
                        )
                     )
                  )
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l14 (s Itl14)) pos) (b (l26 Itl14) pos))
                  )
                  ;Define value of variable blength at beginning of next iteration
                  (= (blength (l14 (s Itl14))) (blength (l26 Itl14)))
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l14 (s Itl14))) (+ (i (l14 Itl14)) 1))
                  ;Define value of variable m at beginning of next iteration
                  (= (m (l14 (s Itl14))) (m (l26 Itl14)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l14 nl14)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (blength main_end) (blength (l14 nl14)))
         (forall ((pos Int))
            (= (b main_end pos) (b (l14 nl14) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (= (i (l14 boundL)) (i (l14 Itl14)))
               )
               (= (i (l14 boundL)) (i (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l14 boundL)) (i (l14 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (<= (i (l14 boundL)) (i (l14 Itl14)))
               )
               (<= (i (l14 boundL)) (i (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l14 boundL)) (i (l14 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (>= (i (l14 boundL)) (i (l14 Itl14)))
               )
               (>= (i (l14 boundL)) (i (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l14 boundL)) (i (l14 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-m-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-m-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (= (m (l14 boundL)) (m (l14 Itl14)))
               )
               (= (m (l14 boundL)) (m (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-m-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-m-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (m (l14 boundL)) (m (l14 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-m-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-m-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (<= (m (l14 boundL)) (m (l14 Itl14)))
               )
               (<= (m (l14 boundL)) (m (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-m-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-m-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (m (l14 boundL)) (m (l14 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-m-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-m-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (>= (m (l14 boundL)) (m (l14 Itl14)))
               )
               (>= (m (l14 boundL)) (m (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-m-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-m-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (m (l14 boundL)) (m (l14 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-blength-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-blength-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (= (blength (l14 boundL)) (blength (l14 Itl14)))
               )
               (= (blength (l14 boundL)) (blength (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-blength-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-blength-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (blength (l14 boundL)) (blength (l14 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-blength-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-blength-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (<= (blength (l14 boundL)) (blength (l14 Itl14)))
               )
               (<= (blength (l14 boundL)) (blength (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-blength-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-blength-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (blength (l14 boundL)) (blength (l14 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-blength-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-blength-l14 boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (>= (blength (l14 boundL)) (blength (l14 Itl14)))
               )
               (>= (blength (l14 boundL)) (blength (l14 (s Itl14))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-blength-l14
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-blength-l14 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (blength (l14 boundL)) (blength (l14 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l14
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l14 pos boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (= (b (l14 boundL) pos) (b (l14 Itl14) pos))
               )
               (= (b (l14 boundL) pos) (b (l14 (s Itl14)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l14
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l14 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l14 boundL) pos) (b (l14 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l14
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l14 pos boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (<= (b (l14 boundL) pos) (b (l14 Itl14) pos))
               )
               (<= (b (l14 boundL) pos) (b (l14 (s Itl14)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l14
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l14 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l14 boundL) pos) (b (l14 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l14
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l14 pos boundL boundR)
         (forall ((Itl14 Nat))
            (=>
               (and
                  (Sub boundL (s Itl14))
                  (Sub Itl14 boundR)
                  (>= (b (l14 boundL) pos) (b (l14 Itl14) pos))
               )
               (>= (b (l14 boundL) pos) (b (l14 (s Itl14)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l14
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l14 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l14 boundL) pos) (b (l14 boundR) pos))
         )
      )
   )
)

; Definition: Dense for i-l14
(assert
   (=
      Dense-i-l14
      (forall ((Itl14 Nat))
         (=>
            (Sub Itl14 nl14)
            (or
               (= (i (l14 (s Itl14))) (i (l14 Itl14)))
               (= (i (l14 (s Itl14))) (+ (i (l14 Itl14)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l14
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l14 xInt)
         (and
            (<= (i (l14 zero)) xInt)
            (< xInt (i (l14 nl14)))
            Dense-i-l14
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l14
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l14 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl14)
               (= (i (l14 it)) xInt)
               (= (i (l14 (s it))) (+ (i (l14 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for m-l14
(assert
   (=
      Dense-m-l14
      (forall ((Itl14 Nat))
         (=>
            (Sub Itl14 nl14)
            (or
               (= (m (l14 (s Itl14))) (m (l14 Itl14)))
               (= (m (l14 (s Itl14))) (+ (m (l14 Itl14)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-m-l14
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-m-l14 xInt)
         (and
            (<= (m (l14 zero)) xInt)
            (< xInt (m (l14 nl14)))
            Dense-m-l14
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-m-l14
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-m-l14 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl14)
               (= (m (l14 it)) xInt)
               (= (m (l14 (s it))) (+ (m (l14 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for blength-l14
(assert
   (=
      Dense-blength-l14
      (forall ((Itl14 Nat))
         (=>
            (Sub Itl14 nl14)
            (or
               (= (blength (l14 (s Itl14))) (blength (l14 Itl14)))
               (= (blength (l14 (s Itl14))) (+ (blength (l14 Itl14)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-blength-l14
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-blength-l14 xInt)
         (and
            (<= (blength (l14 zero)) xInt)
            (< xInt (blength (l14 nl14)))
            Dense-blength-l14
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-blength-l14
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-blength-l14 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl14)
               (= (blength (l14 it)) xInt)
               (= (blength (l14 (s it))) (+ (blength (l14 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l14
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l14
            (= (i (l14 (s it1))) (+ (i (l14 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl14))
         )
         (not
            (= (i (l14 it1)) (i (l14 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-m-l14
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-m-l14
            (= (m (l14 (s it1))) (+ (m (l14 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl14))
         )
         (not
            (= (m (l14 it1)) (m (l14 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-blength-l14
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-blength-l14
            (= (blength (l14 (s it1))) (+ (blength (l14 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl14))
         )
         (not
            (= (blength (l14 it1)) (blength (l14 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l14
(assert
   (=>
      (< (i (l14 zero)) alength)
      (exists ((Itl14 Nat))
         (= (s Itl14) nl14)
      )
   )
)

; Conjecture: user-conjecture-2
(assert-not
   (forall ((j Int)(k Int))
      (=>
         (and
            (<= 1 alength)
            (<= 0 j)
            (<= 0 k)
            (<= j k)
            (< k (blength main_end))
         )
         (<= (b main_end k) (b main_end j))
      )
   )
)

(check-sat)

