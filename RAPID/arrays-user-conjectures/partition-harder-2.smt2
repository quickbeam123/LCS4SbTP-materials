; main()
; {
;    blength = 0 @l14
;    clength = 0 @l16
;    i = 0 @l18
;    while (i < alength) @l19
;    {
;       if (a[i] >= 0) @l21
;       {
;          b[blength] = a[i] @l23
;          blength = (blength) + (1) @l24
;       }
;       else
;       {
;          c[clength] = a[i] @l28
;          clength = (clength) + (1) @l29
;       }
;       i = (i) + (1) @l31
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
(declare-fun c (Time Int) Int)
(declare-fun clength (Time) Int)
(declare-fun i (Time) Int)
(declare-const l14 Time)
(declare-const l16 Time)
(declare-const l18 Time)
(declare-fun l19 (Nat) Time)
(declare-const nl19 Nat)
(declare-fun l21 (Nat) Time)
(declare-fun l23 (Nat) Time)
(declare-fun l24 (Nat) Time)
(declare-fun l28 (Nat) Time)
(declare-fun l29 (Nat) Time)
(declare-fun l31 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-clength-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-clength-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-clength-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-clength-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-clength-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-clength-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-clength-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-clength-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-clength-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-clength-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-clength-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-clength-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-blength-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-blength-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-blength-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-blength-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-blength-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-blength-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-blength-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-blength-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-blength-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-blength-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-blength-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-blength-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l19 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-c-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-c-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-c-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-c-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-c-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-c-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-c-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-c-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-c-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-c-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-c-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-c-l19 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-clength-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-clength-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-clength-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-clength-l19 () Bool)
(declare-lemma-predicate Prem-Intermed-clength-l19 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-blength-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-blength-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-blength-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-blength-l19 () Bool)
(declare-lemma-predicate Prem-Intermed-blength-l19 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l19 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l19 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l19 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l19 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-clength-l19 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-clength-l19 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-clength-l19 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-blength-l19 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-blength-l19 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-blength-l19 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l19 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l19 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l19 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l19
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l19 zero)) 0)
            (= (clength (l19 zero)) 0)
            (= (blength (l19 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl19 Nat))
            (=>
               (Sub Itl19 nl19)
               (< (i (l19 Itl19)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl19 Nat))
            (=>
               (Sub Itl19 nl19)
               (and
                  ;Semantics of IfElse at location l21
                  (and
                     ;Semantics of left branch
                     (=>
                        (>= (a (i (l19 Itl19))) 0)
                        (and
                           ;Update array variable b at location l23
                           (and
                              (= (b (l24 Itl19) (blength (l19 Itl19))) (a (i (l19 Itl19))))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (blength (l19 Itl19)))
                                    )
                                    (= (b (l24 Itl19) pos) (b (l19 Itl19) pos))
                                 )
                              )
                           )
                           (forall ((pos Int))
                              (= (c (l31 Itl19) pos) (c (l19 Itl19) pos))
                           )
                           (forall ((pos Int))
                              (= (b (l31 Itl19) pos) (b (l24 Itl19) pos))
                           )
                           (= (clength (l31 Itl19)) (clength (l19 Itl19)))
                           (= (blength (l31 Itl19)) (+ (blength (l19 Itl19)) 1))
                        )
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (>= (a (i (l19 Itl19))) 0)
                        )
                        (and
                           ;Update array variable c at location l28
                           (and
                              (= (c (l29 Itl19) (clength (l19 Itl19))) (a (i (l19 Itl19))))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (clength (l19 Itl19)))
                                    )
                                    (= (c (l29 Itl19) pos) (c (l19 Itl19) pos))
                                 )
                              )
                           )
                           (forall ((pos Int))
                              (= (c (l31 Itl19) pos) (c (l29 Itl19) pos))
                           )
                           (forall ((pos Int))
                              (= (b (l31 Itl19) pos) (b (l19 Itl19) pos))
                           )
                           (= (clength (l31 Itl19)) (+ (clength (l19 Itl19)) 1))
                           (= (blength (l31 Itl19)) (blength (l19 Itl19)))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l19 (s Itl19))) (+ (i (l19 Itl19)) 1))
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l19 (s Itl19)) pos) (b (l31 Itl19) pos))
                  )
                  ;Define value of variable clength at beginning of next iteration
                  (= (clength (l19 (s Itl19))) (clength (l31 Itl19)))
                  ;Define value of variable blength at beginning of next iteration
                  (= (blength (l19 (s Itl19))) (blength (l31 Itl19)))
                  ;Define value of array variable c at beginning of next iteration
                  (forall ((pos Int))
                     (= (c (l19 (s Itl19)) pos) (c (l31 Itl19) pos))
                  )
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l19 nl19)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (clength main_end) (clength (l19 nl19)))
         (= (blength main_end) (blength (l19 nl19)))
         (forall ((pos Int))
            (= (b main_end pos) (b (l19 nl19) pos))
         )
         (forall ((pos Int))
            (= (c main_end pos) (c (l19 nl19) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-clength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-clength-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (= (clength (l19 boundL)) (clength (l19 Itl19)))
               )
               (= (clength (l19 boundL)) (clength (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-clength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-clength-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (clength (l19 boundL)) (clength (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-clength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-clength-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (<= (clength (l19 boundL)) (clength (l19 Itl19)))
               )
               (<= (clength (l19 boundL)) (clength (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-clength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-clength-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (clength (l19 boundL)) (clength (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-clength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-clength-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (>= (clength (l19 boundL)) (clength (l19 Itl19)))
               )
               (>= (clength (l19 boundL)) (clength (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-clength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-clength-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (clength (l19 boundL)) (clength (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-blength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-blength-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (= (blength (l19 boundL)) (blength (l19 Itl19)))
               )
               (= (blength (l19 boundL)) (blength (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-blength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-blength-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (blength (l19 boundL)) (blength (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-blength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-blength-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (<= (blength (l19 boundL)) (blength (l19 Itl19)))
               )
               (<= (blength (l19 boundL)) (blength (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-blength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-blength-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (blength (l19 boundL)) (blength (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-blength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-blength-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (>= (blength (l19 boundL)) (blength (l19 Itl19)))
               )
               (>= (blength (l19 boundL)) (blength (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-blength-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-blength-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (blength (l19 boundL)) (blength (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (= (i (l19 boundL)) (i (l19 Itl19)))
               )
               (= (i (l19 boundL)) (i (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l19 boundL)) (i (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (<= (i (l19 boundL)) (i (l19 Itl19)))
               )
               (<= (i (l19 boundL)) (i (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l19 boundL)) (i (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l19 boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (>= (i (l19 boundL)) (i (l19 Itl19)))
               )
               (>= (i (l19 boundL)) (i (l19 (s Itl19))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l19
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l19 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l19 boundL)) (i (l19 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (= (b (l19 boundL) pos) (b (l19 Itl19) pos))
               )
               (= (b (l19 boundL) pos) (b (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l19 boundL) pos) (b (l19 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (<= (b (l19 boundL) pos) (b (l19 Itl19) pos))
               )
               (<= (b (l19 boundL) pos) (b (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l19 boundL) pos) (b (l19 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (>= (b (l19 boundL) pos) (b (l19 Itl19) pos))
               )
               (>= (b (l19 boundL) pos) (b (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l19 boundL) pos) (b (l19 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-c-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-c-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (= (c (l19 boundL) pos) (c (l19 Itl19) pos))
               )
               (= (c (l19 boundL) pos) (c (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-c-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-c-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (c (l19 boundL) pos) (c (l19 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-c-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-c-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (<= (c (l19 boundL) pos) (c (l19 Itl19) pos))
               )
               (<= (c (l19 boundL) pos) (c (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-c-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-c-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (c (l19 boundL) pos) (c (l19 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-c-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-c-l19 pos boundL boundR)
         (forall ((Itl19 Nat))
            (=>
               (and
                  (Sub boundL (s Itl19))
                  (Sub Itl19 boundR)
                  (>= (c (l19 boundL) pos) (c (l19 Itl19) pos))
               )
               (>= (c (l19 boundL) pos) (c (l19 (s Itl19)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-c-l19
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-c-l19 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (c (l19 boundL) pos) (c (l19 boundR) pos))
         )
      )
   )
)

; Definition: Dense for clength-l19
(assert
   (=
      Dense-clength-l19
      (forall ((Itl19 Nat))
         (=>
            (Sub Itl19 nl19)
            (or
               (= (clength (l19 (s Itl19))) (clength (l19 Itl19)))
               (= (clength (l19 (s Itl19))) (+ (clength (l19 Itl19)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-clength-l19
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-clength-l19 xInt)
         (and
            (<= (clength (l19 zero)) xInt)
            (< xInt (clength (l19 nl19)))
            Dense-clength-l19
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-clength-l19
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-clength-l19 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl19)
               (= (clength (l19 it)) xInt)
               (= (clength (l19 (s it))) (+ (clength (l19 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for blength-l19
(assert
   (=
      Dense-blength-l19
      (forall ((Itl19 Nat))
         (=>
            (Sub Itl19 nl19)
            (or
               (= (blength (l19 (s Itl19))) (blength (l19 Itl19)))
               (= (blength (l19 (s Itl19))) (+ (blength (l19 Itl19)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-blength-l19
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-blength-l19 xInt)
         (and
            (<= (blength (l19 zero)) xInt)
            (< xInt (blength (l19 nl19)))
            Dense-blength-l19
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-blength-l19
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-blength-l19 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl19)
               (= (blength (l19 it)) xInt)
               (= (blength (l19 (s it))) (+ (blength (l19 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l19
(assert
   (=
      Dense-i-l19
      (forall ((Itl19 Nat))
         (=>
            (Sub Itl19 nl19)
            (or
               (= (i (l19 (s Itl19))) (i (l19 Itl19)))
               (= (i (l19 (s Itl19))) (+ (i (l19 Itl19)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l19
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l19 xInt)
         (and
            (<= (i (l19 zero)) xInt)
            (< xInt (i (l19 nl19)))
            Dense-i-l19
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l19
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l19 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl19)
               (= (i (l19 it)) xInt)
               (= (i (l19 (s it))) (+ (i (l19 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-clength-l19
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-clength-l19
            (= (clength (l19 (s it1))) (+ (clength (l19 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl19))
         )
         (not
            (= (clength (l19 it1)) (clength (l19 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-blength-l19
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-blength-l19
            (= (blength (l19 (s it1))) (+ (blength (l19 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl19))
         )
         (not
            (= (blength (l19 it1)) (blength (l19 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l19
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l19
            (= (i (l19 (s it1))) (+ (i (l19 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl19))
         )
         (not
            (= (i (l19 it1)) (i (l19 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l19
(assert
   (=>
      (< (i (l19 zero)) alength)
      (exists ((Itl19 Nat))
         (= (s Itl19) nl19)
      )
   )
)

; Axiom: user-axiom-0
(assert
   (forall ((it Nat))
      (<= (blength (l19 it)) (i (l19 it)))
   )
)

; Axiom: user-axiom-1
(assert
   (forall ((it Nat))
      (<= (clength (l19 it)) (i (l19 it)))
   )
)

; Conjecture: user-conjecture-2
(assert-not
   (forall ((pos Int))
      (=>
         (and
            (<= 0 alength)
            (<= 0 pos)
            (< pos alength)
            (<= 0 (a pos))
         )
         (exists ((pos2 Int))
            (and
               (<= 0 pos2)
               (< pos2 (blength main_end))
               (= (b main_end pos2) (a pos))
            )
         )
      )
   )
)

(check-sat)

