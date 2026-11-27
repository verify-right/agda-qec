{-# OPTIONS --safe --without-K #-}
module Coding.Binary where

open import Data.Bool.Base public using (Bool; true; false; _xor_; _∧_)
open import Data.Bool.Properties using (xor-∧-commutativeRing; xor-same)
open import Data.Fin.Base as F using (Fin)
open import Data.Nat.Base as N using (ℕ)
open import Relation.Binary.PropositionalEquality as E using (_≡_; cong; cong₂)
import Algebra.Bundles as Bundles
R = xor-∧-commutativeRing
module Law = Bundles.CommutativeRing R
open import Fourier.Sums R public using (sum; delta)
import Fourier.Sums R as S

Word : ℕ → Set
Word n = Fin n → Bool
Matrix : ℕ → ℕ → Set
Matrix m n = Fin m → Word n
infix 4 _≐_
_≐_ : ∀ {n} → Word n → Word n → Set
a ≐ b = ∀ i → a i ≡ b i
zero : ∀ {n} → Word n
zero _ = false
_⊞_ : ∀ {n} → Word n → Word n → Word n
(a ⊞ b) i = a i xor b i

dot : ∀ {n} → Word n → Word n → Bool
dot {n} a b = sum n (λ i → a i ∧ b i)
apply : ∀ {m n} → Matrix m n → Word n → Word m
apply H e i = dot (H i) e
tr : ∀ {m n} → Matrix m n → Matrix n m
tr H j i = H i j

Kernel : ∀ {m n} → Matrix m n → Word n → Set
Kernel H x = apply H x ≐ zero
Orthogonal : ∀ {m k n} → Matrix m n → Matrix k n → Set
Orthogonal X Z = ∀ i j → dot (X i) (Z j) ≡ false

dot-comm : ∀ {n} (a b : Word n) → dot a b ≡ dot b a
dot-comm {n} a b = S.sum-cong n _ _ (λ i → Law.*-comm (a i) (b i))
dot-add : ∀ {n} (a b c : Word n) → dot a (b ⊞ c) ≡ dot a b xor dot a c
dot-add {n} a b c = E.trans (S.sum-cong n _ _ (λ i → Law.distribˡ (a i) (b i) (c i))) (S.sum-add n _ _)
dot-unit : ∀ {n} (a : Word n) j → dot a (delta j) ≡ a j
dot-unit {n} a j = E.trans (dot-comm a (delta j)) (S.select n j a)
syndrome-add : ∀ {m n} (H : Matrix m n) e f → apply H (e ⊞ f) ≐ (apply H e ⊞ apply H f)
syndrome-add H e f i = dot-add (H i) e f
syndrome-coset : ∀ {m n} (H : Matrix m n) e c → Kernel H c → apply H (e ⊞ c) ≐ apply H e
syndrome-coset H e c ker i = E.trans (syndrome-add H e c i)
  (E.trans (cong (apply H e i xor_) (ker i)) (Law.+-identityʳ _))

-- Moving a matrix across the dot product transposes it.
adjoint : ∀ {m n} (H : Matrix m n) (a : Word m) (b : Word n) →
  dot a (apply H b) ≡ dot (apply (tr H) a) b
adjoint {m} {n} H a b = E.trans (S.sum-cong m _ _ (λ i → E.sym (S.sum-mulˡ n (a i) _)))
  (E.trans (S.sum-swap m n (λ i j → a i ∧ (H i j ∧ b j))) (S.sum-cong n _ _ (λ j →
    E.trans (S.sum-cong m _ _ (λ i → E.trans (E.sym (Law.*-assoc (a i) (H i j) (b j)))
      (cong (_∧ b j) (Law.*-comm (a i) (H i j))))) (S.sum-mulʳ m (b j) _))))

boundary-cycle : ∀ {m k n} (X : Matrix m n) (Z : Matrix k n) →
  Orthogonal X Z → ∀ s → Kernel X (apply (tr Z) s)
boundary-cycle {k = k} X Z orth s i = E.trans (adjoint (tr Z) (X i) s)
  (E.trans (S.sum-cong k _ _ (λ j → cong (_∧ s j) (E.trans (dot-comm (Z j) (X i)) (orth i j))))
    (S.sum-zero k))

cycle-rows : ∀ {m k n} (X : Matrix m n) (Z : Matrix k n) →
  (∀ s → Kernel X (apply (tr Z) s)) → Orthogonal X Z
cycle-rows {n = n} X Z chain i j = E.trans (S.sum-cong n _ _ (λ t → cong (X i t ∧_)
  (E.sym (dot-unit (tr Z t) j)))) (chain (delta j) i)

cat : ∀ {m n} → Word m → Word n → Word (m N.+ n)
cat {N.zero} a b i = b i
cat {N.suc m} a b F.zero = a F.zero
cat {N.suc m} a b (F.suc i) = cat {m} (λ t → a (F.suc t)) b i

dot-cat : ∀ {m n} (a c : Word m) (b d : Word n) →
  dot (cat a b) (cat c d) ≡ dot a c xor dot b d
dot-cat {N.zero} a c b d = E.refl
dot-cat {N.suc m} a c b d = E.trans (cong ((a F.zero ∧ c F.zero) xor_)
  (dot-cat {m} (λ t → a (F.suc t)) (λ t → c (F.suc t)) b d)) (E.sym (Law.+-assoc (a F.zero ∧ c F.zero) (dot (λ t → a (F.suc t)) (λ t → c (F.suc t))) (dot b d)))

-- Little-endian coordinate of a natural-number bit mask.
open import Data.Nat.DivMod using (_%_; _/_)
bit : ℕ → ℕ → Bool
bit mask N.zero = (mask % 2) N.≡ᵇ 1
bit mask (N.suc j) = bit (mask / 2) j
