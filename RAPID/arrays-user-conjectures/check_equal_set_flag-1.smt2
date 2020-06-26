; main()
; {
;    r = 0 @l14
;    i = 0 @l15
;    while (i < length) @l16
;    {
;       if (!(a[i] == b[i])) @l18
;       {
;          r = 1 @l20
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
(declare-fun b (Int) Int)
(declare-const length Int)
(declare-fun r (Time) Int)
(declare-fun i (Time) Int)
(declare-const l14 Time)
(declare-const l15 Time)
(declare-fun l16 (Nat) Time)
(declare-const nl16 Nat)
(declare-fun l18 (Nat) Time)
(declare-fun l20 (Nat) Time)
(declare-fun l24 (Nat) Time)
(declare-fun l26 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l16 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l16 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l16 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-eq-r-l16 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-r-l16 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-r-l16 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-r-l16 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-r-l16 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-r-l16 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-r-l16 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-r-l16 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-r-l16 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-r-l16 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-r-l16 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-r-l16 (Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l16 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l16 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l16 (Int) Bool)
(declare-lemma-predicate BC-Ax-Intermed-r-l16 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-r-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-r-l16 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-r-l16 () Bool)
(declare-lemma-predicate Prem-Intermed-r-l16 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l16 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l16 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l16 (Nat Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Injec-r-l16 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-r-l16 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-r-l16 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l16
      (and
         ;Define variable values at beginning of loop
         (and
            (= (i (l16 zero)) 0)
            (= (r (l16 zero)) 0)
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl16 Nat))
            (=>
               (Sub Itl16 nl16)
               (< (i (l16 Itl16)) length)
            )
         )
         ;Semantics of the body
         (forall ((Itl16 Nat))
            (=>
               (Sub Itl16 nl16)
               (and
                  ;Semantics of IfElse at location l18
                  (and
                     ;Semantics of left branch
                     (=>
                        (not
                           (= (a (i (l16 Itl16))) (b (i (l16 Itl16))))
                        )
                        (= (r (l26 Itl16)) 1)
                     )
                     ;Semantics of right branch
                     (=>
                        (not
                           (not
                              (= (a (i (l16 Itl16))) (b (i (l16 Itl16))))
                           )
                        )
                        (= (r (l26 Itl16)) (r (l16 Itl16)))
                     )
                  )
                  ;Define value of variable i at beginning of next iteration
                  (= (i (l16 (s Itl16))) (+ (i (l16 Itl16)) 1))
                  ;Define value of variable r at beginning of next iteration
                  (= (r (l16 (s Itl16))) (r (l26 Itl16)))
               )
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (i (l16 nl16)) length)
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (= (r main_end) (r (l16 nl16)))
   )
)

; Definition: Premise for value-evolution-eq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l16 boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (= (i (l16 boundL)) (i (l16 Itl16)))
               )
               (= (i (l16 boundL)) (i (l16 (s Itl16))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l16 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l16 boundL)) (i (l16 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l16 boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (<= (i (l16 boundL)) (i (l16 Itl16)))
               )
               (<= (i (l16 boundL)) (i (l16 (s Itl16))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l16 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l16 boundL)) (i (l16 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l16 boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (>= (i (l16 boundL)) (i (l16 Itl16)))
               )
               (>= (i (l16 boundL)) (i (l16 (s Itl16))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l16 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l16 boundL)) (i (l16 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-eq-r-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-r-l16 boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (= (r (l16 boundL)) (r (l16 Itl16)))
               )
               (= (r (l16 boundL)) (r (l16 (s Itl16))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-r-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-r-l16 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (r (l16 boundL)) (r (l16 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-r-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-r-l16 boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (<= (r (l16 boundL)) (r (l16 Itl16)))
               )
               (<= (r (l16 boundL)) (r (l16 (s Itl16))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-r-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-r-l16 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (r (l16 boundL)) (r (l16 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-r-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-r-l16 boundL boundR)
         (forall ((Itl16 Nat))
            (=>
               (and
                  (Sub boundL (s Itl16))
                  (Sub Itl16 boundR)
                  (>= (r (l16 boundL)) (r (l16 Itl16)))
               )
               (>= (r (l16 boundL)) (r (l16 (s Itl16))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-r-l16
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-r-l16 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (r (l16 boundL)) (r (l16 boundR)))
         )
      )
   )
)

; Definition: Dense for i-l16
(assert
   (=
      Dense-i-l16
      (forall ((Itl16 Nat))
         (=>
            (Sub Itl16 nl16)
            (or
               (= (i (l16 (s Itl16))) (i (l16 Itl16)))
               (= (i (l16 (s Itl16))) (+ (i (l16 Itl16)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l16
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l16 xInt)
         (and
            (<= (i (l16 zero)) xInt)
            (< xInt (i (l16 nl16)))
            Dense-i-l16
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l16
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l16 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl16)
               (= (i (l16 it)) xInt)
               (= (i (l16 (s it))) (+ (i (l16 it)) 1))
            )
         )
      )
   )
)

; Definition: Dense for r-l16
(assert
   (=
      Dense-r-l16
      (forall ((Itl16 Nat))
         (=>
            (Sub Itl16 nl16)
            (or
               (= (r (l16 (s Itl16))) (r (l16 Itl16)))
               (= (r (l16 (s Itl16))) (+ (r (l16 Itl16)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-r-l16
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-r-l16 xInt)
         (and
            (<= (r (l16 zero)) xInt)
            (< xInt (r (l16 nl16)))
            Dense-r-l16
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-r-l16
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-r-l16 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl16)
               (= (r (l16 it)) xInt)
               (= (r (l16 (s it))) (+ (r (l16 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l16
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l16
            (= (i (l16 (s it1))) (+ (i (l16 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl16))
         )
         (not
            (= (i (l16 it1)) (i (l16 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-r-l16
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-r-l16
            (= (r (l16 (s it1))) (+ (r (l16 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl16))
         )
         (not
            (= (r (l16 it1)) (r (l16 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l16
(assert
   (=>
      (< (i (l16 zero)) length)
      (exists ((Itl16 Nat))
         (= (s Itl16) nl16)
      )
   )
)

; Conjecture: user-conjecture-1
(assert-not
   (forall ((k Int))
      (=>
         (and
            (<= 0 k)
            (< k length)
            (<= 0 length)
            (not
               (= (r main_end) 1)
            )
         )
         (= (a k) (b k))
      )
   )
)

(check-sat)

