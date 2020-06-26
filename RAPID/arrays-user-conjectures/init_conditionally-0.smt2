; main()
; {
;    i = 0 @l9
;    clength = 0 @l10
;    while (i < length) @l11
;    {
;       if (a[i] == b[i]) @l13
;       {
;          c[clength] = i @l15
;          clength = (clength) + (1) @l16
;       }
;       else
;       {
;          skip @l20
;       }
;       i = (i) + (1) @l22
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(declare-fun c (Time Int) Int)
(declare-const length Int)
(declare-fun i (Time) Int)
(declare-fun clength (Time) Int)
(declare-const l9 Time)
(declare-const l10 Time)
(declare-fun l11 (Nat) Time)
(declare-const nl11 Nat)
(declare-fun l13 (Nat) Time)
(declare-fun l15 (Nat) Time)
(declare-fun l16 (Nat) Time)
(declare-fun l20 (Nat) Time)
(declare-fun l22 (Nat) Time)
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
(declare-lemma-predicate BC-AxEvol-eq-clength-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-clength-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-clength-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-clength-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-clength-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-clength-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-clength-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-clength-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-clength-l11 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-clength-l11 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-clength-l11 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-clength-l11 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-c-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-eq-c-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-eq-c-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-eq-c-l11 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-c-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-leq-c-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-leq-c-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-leq-c-l11 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-c-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-AxEvol-geq-c-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-AxEvol-geq-c-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate PremEvol-geq-c-l11 (Int Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l11 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l11 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-clength-l11 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-clength-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-clength-l11 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-clength-l11 () Bool)
(declare-lemma-predicate Prem-Intermed-clength-l11 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l11 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l11 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l11 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-clength-l11 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-clength-l11 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-clength-l11 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l11
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l11 zero)) 0)
            (= (clength (l11 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl11 Nat))
            (=>
               (Sub Itl11 nl11)
               (< (i (l11 Itl11)) length)
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
                        (= (a (i (l11 Itl11))) (b (i (l11 Itl11))))
                        (and
                           ;Update array variable c at location l15
                           (and
                              (= (c (l16 Itl11) (clength (l11 Itl11))) (i (l11 Itl11)))
                              (forall ((pos Int))
                                 (=>
                                    (not
                                       (= pos (clength (l11 Itl11)))
                                    )
                                    (= (c (l16 Itl11) pos) (c (l11 Itl11) pos))
                                 )
                              )
                           )
                           (forall ((pos Int))
                              (= (c (l22 Itl11) pos) (c (l16 Itl11) pos))
                           )
                           (= (clength (l22 Itl11)) (+ (clength (l11 Itl11)) 1))
                        )
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (= (a (i (l11 Itl11))) (b (i (l11 Itl11))))
                        )
                        (and
                           (forall ((pos Int))
                              (= (c (l22 Itl11) pos) (c (l11 Itl11) pos))
                           )
                           (= (clength (l22 Itl11)) (clength (l11 Itl11)))
                        )
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l11 (s Itl11))) (+ (i (l11 Itl11)) 1))
                  ;Define value of array variable c at beginning of next iteration
                  (forall ((pos Int))
                     (= (c (l11 (s Itl11)) pos) (c (l22 Itl11) pos))
                  )
                  ;Define value of variable clength at beginning of next iteration
                  (= (clength (l11 (s Itl11))) (clength (l22 Itl11)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l11 nl11)) length)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (and
         (= (clength main_end) (clength (l11 nl11)))
         (forall ((pos Int))
            (= (c main_end pos) (c (l11 nl11) pos))
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

; Definition: Premise for value-evolution-eq-clength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-clength-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (= (clength (l11 boundL)) (clength (l11 Itl11)))
               )
               (= (clength (l11 boundL)) (clength (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-clength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-clength-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (clength (l11 boundL)) (clength (l11 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-clength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-clength-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (<= (clength (l11 boundL)) (clength (l11 Itl11)))
               )
               (<= (clength (l11 boundL)) (clength (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-clength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-clength-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (clength (l11 boundL)) (clength (l11 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-clength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-clength-l11 boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (>= (clength (l11 boundL)) (clength (l11 Itl11)))
               )
               (>= (clength (l11 boundL)) (clength (l11 (s Itl11))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-clength-l11
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-clength-l11 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (clength (l11 boundL)) (clength (l11 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-c-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-c-l11 pos boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (= (c (l11 boundL) pos) (c (l11 Itl11) pos))
               )
               (= (c (l11 boundL) pos) (c (l11 (s Itl11)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-c-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-c-l11 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (c (l11 boundL) pos) (c (l11 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-c-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-c-l11 pos boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (<= (c (l11 boundL) pos) (c (l11 Itl11) pos))
               )
               (<= (c (l11 boundL) pos) (c (l11 (s Itl11)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-c-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-c-l11 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (c (l11 boundL) pos) (c (l11 boundR) pos))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-c-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-c-l11 pos boundL boundR)
         (forall ((Itl11 Nat))
            (=>
               (and
                  (Sub boundL (s Itl11))
                  (Sub Itl11 boundR)
                  (>= (c (l11 boundL) pos) (c (l11 Itl11) pos))
               )
               (>= (c (l11 boundL) pos) (c (l11 (s Itl11)) pos))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-c-l11
(assert
   (forall ((pos Int)(boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-c-l11 pos boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (c (l11 boundL) pos) (c (l11 boundR) pos))
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

; Definition: Dense for clength-l11
(assert
   (=
      Dense-clength-l11
      (forall ((Itl11 Nat))
         (=>
            (Sub Itl11 nl11)
            (or
               (= (clength (l11 (s Itl11))) (clength (l11 Itl11)))
               (= (clength (l11 (s Itl11))) (+ (clength (l11 Itl11)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-clength-l11
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-clength-l11 xInt)
         (and
            (<= (clength (l11 zero)) xInt)
            (< xInt (clength (l11 nl11)))
            Dense-clength-l11
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-clength-l11
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-clength-l11 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl11)
               (= (clength (l11 it)) xInt)
               (= (clength (l11 (s it))) (+ (clength (l11 it)) 1))
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

; Axiom: already-proven-lemma iterator-injectivity-clength-l11
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-clength-l11
            (= (clength (l11 (s it1))) (+ (clength (l11 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl11))
         )
         (not
            (= (clength (l11 it1)) (clength (l11 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l11
(assert
   (=>
      (< (i (l11 zero)) length)
      (exists ((Itl11 Nat))
         (= (s Itl11) nl11)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (forall ((pos Int))
      (=>
         (and
            (<= 0 pos)
            (< pos (clength main_end))
            (<= 0 length)
         )
         (= (a (c main_end pos)) (b (c main_end pos)))
      )
   )
)

(check-sat)

