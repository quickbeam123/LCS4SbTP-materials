; main()
; {
;    blength = 0 @l16
;    clength = 0 @l18
;    i = 0 @l20
;    while (i < alength) @l21
;    {
;       if (a[i] >= 0) @l23
;       {
;          b[blength] = a[i] @l25
;          blength = (blength) + (1) @l26
;       }
;       else
;       {
;          c[clength] = a[i] @l30
;          clength = (clength) + (1) @l31
;       }
;       i = (i) + (1) @l33
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
(declare-const l16 Time)
(declare-const l18 Time)
(declare-const l20 Time)
(declare-fun l21 (Nat) Time)
(declare-const nl21 Nat)
(declare-fun l23 (Nat) Time)
(declare-fun l25 (Nat) Time)
(declare-fun l26 (Nat) Time)
(declare-fun l30 (Nat) Time)
(declare-fun l31 (Nat) Time)
(declare-fun l33 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-clength-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-clength-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-clength-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-clength-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-clength-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-clength-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-clength-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-clength-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-clength-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-clength-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-clength-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-clength-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-blength-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-blength-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-blength-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-blength-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-blength-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-blength-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-blength-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-blength-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-blength-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-blength-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-blength-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-blength-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-i-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l21 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-b-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-b-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-b-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-b-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-b-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-b-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-b-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-c-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-c-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-c-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-c-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-c-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-c-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-c-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-c-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-c-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-c-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-c-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-c-l21 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-clength-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-clength-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-clength-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-clength-l21 () Bool)
(declare-lemma-predicate Prem-Intermed-clength-l21 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-blength-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-blength-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-blength-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-blength-l21 () Bool)
(declare-lemma-predicate Prem-Intermed-blength-l21 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l21 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l21 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l21 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l21 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-clength-l21 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-clength-l21 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-clength-l21 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-blength-l21 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-blength-l21 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-blength-l21 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l21 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l21 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l21 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l21
      (and
         ;Define variable values at beginning of loop
         (and
            (= (blength (l21 zero)) 0)
            (= (i (l21 zero)) 0)
            (= (clength (l21 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl21 Nat))
            (=>
               (Sub Itl21 nl21)
               (< (i (l21 Itl21)) alength)
            )
         )
         ;Semantics of the body
         (forall ((Itl21 Nat))
            (=>
               (Sub Itl21 nl21)
               (and
                  ;Semantics of IfElse at location l23
                  (and
                     ;Semantics of left branch
                     (=>
                        (>= (a (i (l21 Itl21))) 0)
                        (and
                           ;Update array variable b at location l25
                           (and
                              (= (b (l26 Itl21) (blength (l21 Itl21))) (a (i (l21 Itl21))))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (blength (l21 Itl21)))
                                    )
                                    (= (b (l26 Itl21) pos) (b (l21 Itl21) pos))
                                 )
                              )
                           )
                           (forall ((pos Int))
                              (= (b (l33 Itl21) pos) (b (l26 Itl21) pos))
                           )
                           (forall ((pos Int))
                              (= (c (l33 Itl21) pos) (c (l21 Itl21) pos))
                           )
                           (= (clength (l33 Itl21)) (clength (l21 Itl21)))
                           (= (blength (l33 Itl21)) (+ (blength (l21 Itl21)) 1))
                        )
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (>= (a (i (l21 Itl21))) 0)
                        )
                        (and
                           ;Update array variable c at location l30
                           (and
                              (= (c (l31 Itl21) (clength (l21 Itl21))) (a (i (l21 Itl21))))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (clength (l21 Itl21)))
                                    )
                                    (= (c (l31 Itl21) pos) (c (l21 Itl21) pos))
                                 )
                              )
                           )
                           (forall ((pos Int))
                              (= (b (l33 Itl21) pos) (b (l21 Itl21) pos))
                           )
                           (forall ((pos Int))
                              (= (c (l33 Itl21) pos) (c (l31 Itl21) pos))
                           )
                           (= (clength (l33 Itl21)) (+ (clength (l21 Itl21)) 1))
                           (= (blength (l33 Itl21)) (blength (l21 Itl21)))
                        )
                     )
                  )
                  ;Define value of array variable b at beginning of next iteration
                  (forall ((pos Int))
                     (= (b (l21 (s Itl21)) pos) (b (l33 Itl21) pos))
                  )
                  ;Define value of variable blength at beginning of next iteration
                  (= (blength (l21 (s Itl21))) (blength (l33 Itl21)))
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l21 (s Itl21))) (+ (i (l21 Itl21)) 1))
                  ;Define value of array variable c at beginning of next iteration
                  (forall ((pos Int))
                     (= (c (l21 (s Itl21)) pos) (c (l33 Itl21) pos))
                  )
                  ;Define value of variable clength at beginning of next iteration
                  (= (clength (l21 (s Itl21))) (clength (l33 Itl21)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l21 nl21)) alength)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (clength main_end) (clength (l21 nl21)))
         (= (blength main_end) (blength (l21 nl21)))
         (forall ((pos Int))
            (= (b main_end pos) (b (l21 nl21) pos))
         )
         (forall ((pos Int))
            (= (c main_end pos) (c (l21 nl21) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-clength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-clength-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (= (clength (l21 boundL)) (clength (l21 Itl21)))
               )
               (= (clength (l21 boundL)) (clength (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-clength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-clength-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (clength (l21 boundL)) (clength (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-clength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-clength-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (<= (clength (l21 boundL)) (clength (l21 Itl21)))
               )
               (<= (clength (l21 boundL)) (clength (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-clength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-clength-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (clength (l21 boundL)) (clength (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-clength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-clength-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (>= (clength (l21 boundL)) (clength (l21 Itl21)))
               )
               (>= (clength (l21 boundL)) (clength (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-clength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-clength-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (clength (l21 boundL)) (clength (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-blength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-blength-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (= (blength (l21 boundL)) (blength (l21 Itl21)))
               )
               (= (blength (l21 boundL)) (blength (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-blength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-blength-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (blength (l21 boundL)) (blength (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-blength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-blength-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (<= (blength (l21 boundL)) (blength (l21 Itl21)))
               )
               (<= (blength (l21 boundL)) (blength (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-blength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-blength-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (blength (l21 boundL)) (blength (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-blength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-blength-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (>= (blength (l21 boundL)) (blength (l21 Itl21)))
               )
               (>= (blength (l21 boundL)) (blength (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-blength-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-blength-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (blength (l21 boundL)) (blength (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (= (i (l21 boundL)) (i (l21 Itl21)))
               )
               (= (i (l21 boundL)) (i (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l21 boundL)) (i (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (<= (i (l21 boundL)) (i (l21 Itl21)))
               )
               (<= (i (l21 boundL)) (i (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l21 boundL)) (i (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l21 boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (>= (i (l21 boundL)) (i (l21 Itl21)))
               )
               (>= (i (l21 boundL)) (i (l21 (s Itl21))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l21
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l21 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l21 boundL)) (i (l21 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-b-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (= (b (l21 boundL) pos) (b (l21 Itl21) pos))
               )
               (= (b (l21 boundL) pos) (b (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-b-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (b (l21 boundL) pos) (b (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-b-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (<= (b (l21 boundL) pos) (b (l21 Itl21) pos))
               )
               (<= (b (l21 boundL) pos) (b (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-b-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (b (l21 boundL) pos) (b (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-b-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (>= (b (l21 boundL) pos) (b (l21 Itl21) pos))
               )
               (>= (b (l21 boundL) pos) (b (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-b-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-b-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (b (l21 boundL) pos) (b (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-c-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-c-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (= (c (l21 boundL) pos) (c (l21 Itl21) pos))
               )
               (= (c (l21 boundL) pos) (c (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-c-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-c-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (c (l21 boundL) pos) (c (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-c-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-c-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (<= (c (l21 boundL) pos) (c (l21 Itl21) pos))
               )
               (<= (c (l21 boundL) pos) (c (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-c-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-c-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (c (l21 boundL) pos) (c (l21 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-c-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-c-l21 pos boundL boundR)
         (forall ((Itl21 Nat))
            (=>
               (and
                  (Sub boundL (s Itl21))
                  (Sub Itl21 boundR)
                  (>= (c (l21 boundL) pos) (c (l21 Itl21) pos))
               )
               (>= (c (l21 boundL) pos) (c (l21 (s Itl21)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-c-l21
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-c-l21 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (c (l21 boundL) pos) (c (l21 boundR) pos))
         )
      )
   )
)

; Definition: Dense for clength-l21
(assert
   (=
      Dense-clength-l21
      (forall ((Itl21 Nat))
         (=>
            (Sub Itl21 nl21)
            (or
               (= (clength (l21 (s Itl21))) (clength (l21 Itl21)))
               (= (clength (l21 (s Itl21))) (+ (clength (l21 Itl21)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-clength-l21
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-clength-l21 xInt)
         (and
            (<= (clength (l21 zero)) xInt)
            (< xInt (clength (l21 nl21)))
            Dense-clength-l21
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-clength-l21
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-clength-l21 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl21)
               (= (clength (l21 it)) xInt)
               (= (clength (l21 (s it))) (+ (clength (l21 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for blength-l21
(assert
   (=
      Dense-blength-l21
      (forall ((Itl21 Nat))
         (=>
            (Sub Itl21 nl21)
            (or
               (= (blength (l21 (s Itl21))) (blength (l21 Itl21)))
               (= (blength (l21 (s Itl21))) (+ (blength (l21 Itl21)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-blength-l21
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-blength-l21 xInt)
         (and
            (<= (blength (l21 zero)) xInt)
            (< xInt (blength (l21 nl21)))
            Dense-blength-l21
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-blength-l21
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-blength-l21 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl21)
               (= (blength (l21 it)) xInt)
               (= (blength (l21 (s it))) (+ (blength (l21 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for i-l21
(assert
   (=
      Dense-i-l21
      (forall ((Itl21 Nat))
         (=>
            (Sub Itl21 nl21)
            (or
               (= (i (l21 (s Itl21))) (i (l21 Itl21)))
               (= (i (l21 (s Itl21))) (+ (i (l21 Itl21)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l21
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l21 xInt)
         (and
            (<= (i (l21 zero)) xInt)
            (< xInt (i (l21 nl21)))
            Dense-i-l21
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l21
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l21 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl21)
               (= (i (l21 it)) xInt)
               (= (i (l21 (s it))) (+ (i (l21 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-clength-l21
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-clength-l21
            (= (clength (l21 (s it1))) (+ (clength (l21 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl21))
         )
         (not
            (= (clength (l21 it1)) (clength (l21 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-blength-l21
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-blength-l21
            (= (blength (l21 (s it1))) (+ (blength (l21 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl21))
         )
         (not
            (= (blength (l21 it1)) (blength (l21 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l21
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l21
            (= (i (l21 (s it1))) (+ (i (l21 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl21))
         )
         (not
            (= (i (l21 it1)) (i (l21 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l21
(assert
   (=>
      (< (i (l21 zero)) alength)
      (exists ((Itl21 Nat))
         (= (s Itl21) nl21)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (forall ((pos Int))
      (=>
         (and
            (<= 0 alength)
            (<= 0 pos)
            (< pos (blength main_end))
         )
         (<= 0 (b main_end pos))
      )
   )
)

(check-sat)

