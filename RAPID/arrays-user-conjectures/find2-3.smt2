; main()
; {
;    i = 0 @l14
;    while ((i < alength) && (!(a[i] == v))) @l15
;    {
;       i = (i) + (1) @l17
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Int) Int)
(declare-const alength Int)
(declare-const v Int)
(declare-fun i (Time) Int)
(declare-const l14 Time)
(declare-fun l15 (Nat) Time)
(declare-const nl15 Nat)
(declare-fun l17 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l15 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l15 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l15 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l15 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l15 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l15 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l15 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l15 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l15 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l15 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l15 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l15
      (and
         ;Define variable values at beginning of loop
         (= (i (l15 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl15 Nat))
            (=>
               (Sub Itl15 nl15)
               (and
                  (< (i (l15 Itl15)) alength)
                  (not
                     (= (a (i (l15 Itl15))) v)
                  )
               )
            )
         )
         ;Semantics of the body
         (forall ((Itl15 Nat))
            (=>
               (Sub Itl15 nl15)
               ;Define value of variable i at beginning of next iteration
               (= (i (l15 (s Itl15))) (+ (i (l15 Itl15)) 1))
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (and
               (< (i (l15 nl15)) alength)
               (not
                  (= (a (i (l15 nl15))) v)
               )
            )
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (= (i main_end) (i (l15 nl15)))
   )
)

; Definition: Premise for value-evolution-eq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l15 boundL boundR)
         (forall ((Itl15 Nat))
            (=>
               (and
                  (Sub boundL (s Itl15))
                  (Sub Itl15 boundR)
                  (= (i (l15 boundL)) (i (l15 Itl15)))
               )
               (= (i (l15 boundL)) (i (l15 (s Itl15))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l15 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l15 boundL)) (i (l15 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l15 boundL boundR)
         (forall ((Itl15 Nat))
            (=>
               (and
                  (Sub boundL (s Itl15))
                  (Sub Itl15 boundR)
                  (<= (i (l15 boundL)) (i (l15 Itl15)))
               )
               (<= (i (l15 boundL)) (i (l15 (s Itl15))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l15 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l15 boundL)) (i (l15 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l15 boundL boundR)
         (forall ((Itl15 Nat))
            (=>
               (and
                  (Sub boundL (s Itl15))
                  (Sub Itl15 boundR)
                  (>= (i (l15 boundL)) (i (l15 Itl15)))
               )
               (>= (i (l15 boundL)) (i (l15 (s Itl15))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l15
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l15 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l15 boundL)) (i (l15 boundR)))
         )
      )
   )
)

; Definition: Dense for i-l15
(assert
   (=
      Dense-i-l15
      (forall ((Itl15 Nat))
         (=>
            (Sub Itl15 nl15)
            (or
               (= (i (l15 (s Itl15))) (i (l15 Itl15)))
               (= (i (l15 (s Itl15))) (+ (i (l15 Itl15)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l15
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l15 xInt)
         (and
            (<= (i (l15 zero)) xInt)
            (< xInt (i (l15 nl15)))
            Dense-i-l15
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l15
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l15 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl15)
               (= (i (l15 it)) xInt)
               (= (i (l15 (s it))) (+ (i (l15 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l15
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l15
            (= (i (l15 (s it1))) (+ (i (l15 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl15))
         )
         (not
            (= (i (l15 it1)) (i (l15 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l15
(assert
   (=>
      (and
         (< (i (l15 zero)) alength)
         (not
            (= (a (i (l15 zero))) v)
         )
      )
      (exists ((Itl15 Nat))
         (= (s Itl15) nl15)
      )
   )
)

; Conjecture: user-conjecture-3
(assert-not
   (=>
      (and
         (<= 0 alength)
         (< (i main_end) alength)
      )
      (exists ((pos Int))
         (= (a pos) v)
      )
   )
)

(check-sat)

