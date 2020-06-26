; main()
; {
;    i = 0 @l4
;    while (!(a[i] == 0)) @l5
;    {
;       i = (i) + (1) @l7
;    }
; }
; 

(set-logic UFDTLIA)

(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)
(declare-fun a (Int) Int)
(declare-fun i (Time) Int)
(declare-const l4 Time)
(declare-fun l5 (Nat) Time)
(declare-const nl5 Nat)
(declare-fun l7 (Nat) Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-lemma-predicate BC-AxEvol-eq-i-l5 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-eq-i-l5 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-eq-i-l5 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-eq-i-l5 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-leq-i-l5 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-leq-i-l5 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-leq-i-l5 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-leq-i-l5 (Nat Nat) Bool)
(declare-lemma-predicate BC-AxEvol-geq-i-l5 (Nat) Bool)
(declare-lemma-predicate IC-AxEvol-geq-i-l5 (Nat Nat) Bool)
(declare-lemma-predicate Con-AxEvol-geq-i-l5 (Nat Nat) Bool)
(declare-lemma-predicate PremEvol-geq-i-l5 (Nat Nat) Bool)
(declare-lemma-predicate BC-Ax-Intermed-i-l5 (Nat Int) Bool)
(declare-lemma-predicate IC-Ax-Intermed-i-l5 (Nat Nat Int) Bool)
(declare-lemma-predicate Con-Ax-Intermed-i-l5 (Nat Nat Int) Bool)
(declare-lemma-predicate Dense-i-l5 () Bool)
(declare-lemma-predicate Prem-Intermed-i-l5 (Int) Bool)
(declare-lemma-predicate BC-Ax-Injec-i-l5 (Nat Nat) Bool)
(declare-lemma-predicate IC-Ax-Injec-i-l5 (Nat Nat Nat) Bool)
(declare-lemma-predicate Con-Ax-Injec-i-l5 (Nat Nat Nat) Bool)

; Axiom: Semantics of function main
(assert
   (and
      ;Loop at location l5
      (and
         ;Define variable values at beginning of loop
         (= (i (l5 zero)) 0)
         ;The loop-condition holds always before the last iteration
         (forall ((Itl5 Nat))
            (=>
               (Sub Itl5 nl5)
               (not
                  (= (a (i (l5 Itl5))) 0)
               )
            )
         )
         ;Semantics of the body
         (forall ((Itl5 Nat))
            (=>
               (Sub Itl5 nl5)
               ;Define value of variable i at beginning of next iteration
               (= (i (l5 (s Itl5))) (+ (i (l5 Itl5)) 1))
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (not
               (= (a (i (l5 nl5))) 0)
            )
         )
      )
      ;Define referenced terms denoting variable values at main_end
      (= (i main_end) (i (l5 nl5)))
   )
)

; Definition: Premise for value-evolution-eq-i-l5
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-eq-i-l5 boundL boundR)
         (forall ((Itl5 Nat))
            (=>
               (and
                  (Sub boundL (s Itl5))
                  (Sub Itl5 boundR)
                  (= (i (l5 boundL)) (i (l5 Itl5)))
               )
               (= (i (l5 boundL)) (i (l5 (s Itl5))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-eq-i-l5
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-eq-i-l5 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (= (i (l5 boundL)) (i (l5 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-leq-i-l5
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-leq-i-l5 boundL boundR)
         (forall ((Itl5 Nat))
            (=>
               (and
                  (Sub boundL (s Itl5))
                  (Sub Itl5 boundR)
                  (<= (i (l5 boundL)) (i (l5 Itl5)))
               )
               (<= (i (l5 boundL)) (i (l5 (s Itl5))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-leq-i-l5
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-leq-i-l5 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (<= (i (l5 boundL)) (i (l5 boundR)))
         )
      )
   )
)

; Definition: Premise for value-evolution-geq-i-l5
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=
         (PremEvol-geq-i-l5 boundL boundR)
         (forall ((Itl5 Nat))
            (=>
               (and
                  (Sub boundL (s Itl5))
                  (Sub Itl5 boundR)
                  (>= (i (l5 boundL)) (i (l5 Itl5)))
               )
               (>= (i (l5 boundL)) (i (l5 (s Itl5))))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma value-evolution-geq-i-l5
(assert
   (forall ((boundL Nat)(boundR Nat))
      (=>
         (PremEvol-geq-i-l5 boundL boundR)
         (=>
            (Sub boundL (s boundR))
            (>= (i (l5 boundL)) (i (l5 boundR)))
         )
      )
   )
)

; Definition: Dense for i-l5
(assert
   (=
      Dense-i-l5
      (forall ((Itl5 Nat))
         (=>
            (Sub Itl5 nl5)
            (or
               (= (i (l5 (s Itl5))) (i (l5 Itl5)))
               (= (i (l5 (s Itl5))) (+ (i (l5 Itl5)) 1))
            )
         )
      )
   )
)

; Definition: Premise for iterator-intermediateValue-i-l5
(assert
   (forall ((xInt Int))
      (=
         (Prem-Intermed-i-l5 xInt)
         (and
            (<= (i (l5 zero)) xInt)
            (< xInt (i (l5 nl5)))
            Dense-i-l5
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-intermediateValue-i-l5
(assert
   (forall ((xInt Int))
      (=>
         (Prem-Intermed-i-l5 xInt)
         (exists ((it Nat))
            (and
               (Sub it nl5)
               (= (i (l5 it)) xInt)
               (= (i (l5 (s it))) (+ (i (l5 it)) 1))
            )
         )
      )
   )
)

; Axiom: already-proven-lemma iterator-injectivity-i-l5
(assert
   (forall ((it1 Nat)(it2 Nat))
      (=>
         (and
            Dense-i-l5
            (= (i (l5 (s it1))) (+ (i (l5 it1)) 1))
            (Sub it1 it2)
            (Sub it2 (s nl5))
         )
         (not
            (= (i (l5 it1)) (i (l5 it2)))
         )
      )
   )
)

; Axiom: already-proven-lemma atLeastOneIteration-l5
(assert
   (=>
      (not
         (= (a (i (l5 zero))) 0)
      )
      (exists ((Itl5 Nat))
         (= (s Itl5) nl5)
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (=>
      (exists ((pos Int))
         (and
            (<= 0 pos)
            (= (a pos) 0)
         )
      )
      (forall ((j Int))
         (=>
            (and
               (<= 0 j)
               (< j (i main_end))
            )
            (not
               (= (a j) 0)
            )
         )
      )
   )
)

(check-sat)

