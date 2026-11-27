{-# OPTIONS --safe --without-K #-}
module Coding.Symplectic where

open import Coding.Binary
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Bool.Properties using (xor-same)
open import Relation.Binary.PropositionalEquality as E using (_≡_)
import Algebra.FiniteSums R as S
import Algebra.Properties.CommutativeSemigroup as CS
module Add = CS Law.+-commutativeSemigroup

-- Representatives X^x Z^z act on signed computational basis labels.
record Pauli (n : ℕ) : Set where
  constructor pauli
  field x z : Word n
open Pauli public
State = λ n → Word n × Bool
run : ∀ {n} → Pauli n → State n → State n
run p (v , s) = (v ⊞ x p) , (s xor dot (z p) v)
form : ∀ {n} → Pauli n → Pauli n → Bool
form p q = dot (z p) (x q) xor dot (z q) (x p)

-- Elementary group rearrangement for five bits. First factor out the
-- common input-dependent phase using associativity and commutativity.
phase-law : ∀ s a b c d → (s xor a) xor (b xor c) ≡ (c xor d) xor ((s xor b) xor (a xor d))
phase-law s a b c d = E.trans (E.sym (Law.+-assoc (s xor a) b c))
  (E.trans (E.cong (_xor c) swap) (E.trans (cancel u c d) (E.cong ((c xor d) xor_) (Law.+-assoc (s xor b) a d))))
  where
  u = (s xor b) xor a
  swap : (s xor a) xor b ≡ u
  swap = E.trans (Law.+-assoc s a b) (E.trans (E.cong (s xor_) (Law.+-comm a b)) (E.sym (Law.+-assoc s b a)))
  cancel : ∀ u c d → u xor c ≡ (c xor d) xor (u xor d)
  cancel u c d = E.trans (Law.+-comm u c) (E.trans (E.sym (Law.+-identityʳ (c xor u)))
    (E.trans (E.cong ((c xor u) xor_) (E.sym (xor-same d))) (Add.interchange c u d d)))

open import Data.Product.Base using (proj₁; proj₂)
swap-label : ∀ {n} (p q : Pauli n) t →
  proj₁ (run p (run q t)) ≐ proj₁ (run q (run p t))
swap-label p q (v , s) i = E.trans (Law.+-assoc (v i) (x q i) (x p i))
  (E.trans (E.cong (v i xor_) (Law.+-comm (x q i) (x p i))) (E.sym (Law.+-assoc (v i) (x p i) (x q i))))

swap-sign : ∀ {n} (p q : Pauli n) t →
  proj₂ (run p (run q t)) ≡ form p q xor proj₂ (run q (run p t))
swap-sign p q (v , s) rewrite dot-add (z p) v (x q) | dot-add (z q) v (x p) =
  phase-law s (dot (z q) v) (dot (z p) v) (dot (z p) (x q)) (dot (z q) (x p))

pure-check : ∀ {n} (a b : Word n) → form (pauli a zero) (pauli zero b) ≡ dot a b
pure-check {n} a b = E.trans (E.cong (_xor dot b a) (S.sum-zero n)) (dot-comm b a)

css-sign : ∀ {m k n} (X : Matrix m n) (Z : Matrix k n) → Orthogonal X Z →
  ∀ i j t → proj₂ (run (pauli (X i) zero) (run (pauli zero (Z j)) t)) ≡
             proj₂ (run (pauli zero (Z j)) (run (pauli (X i) zero) t))
css-sign X Z orth i j t = E.trans (swap-sign (pauli (X i) zero) (pauli zero (Z j)) t)
  (E.cong (_xor proj₂ (run (pauli zero (Z j)) (run (pauli (X i) zero) t)))
    (E.trans (pure-check (X i) (Z j)) (orth i j)))

-- The classical check bits are precisely the sign changes on opposite-type errors.
x-syndrome : ∀ {m n} (X : Matrix m n) (p : Pauli n) i →
  form (pauli (X i) zero) p ≡ apply X (z p) i
x-syndrome {n = n} X p i = E.trans (E.cong (_xor dot (z p) (X i)) (S.sum-zero n)) (dot-comm (z p) (X i))
z-syndrome : ∀ {k n} (Z : Matrix k n) (p : Pauli n) i →
  form (pauli zero (Z i)) p ≡ apply Z (x p) i
z-syndrome {n = n} Z p i = E.trans (E.cong (apply Z (x p) i xor_)
  (E.trans (dot-comm (z p) zero) (S.sum-zero n))) (Law.+-identityʳ _)
