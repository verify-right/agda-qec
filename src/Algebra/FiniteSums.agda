{-# OPTIONS --safe --without-K #-}

open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)

module Algebra.FiniteSums (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as N
open import Data.Fin.Base using (Fin)
import Data.Fin.Base as F
import Algebra.Properties.Semiring.Sum semiring as S

sum : (n : ℕ) → (Fin n → Carrier) → Carrier
sum = S.sum-syntax

sum-cong : ∀ n (f g : Fin n → Carrier) →
  (∀ i → f i ≈ g i) → sum n f ≈ sum n g
sum-cong n f g p = S.sum-cong-≋ p

sum-zero : ∀ n → sum n (λ _ → 0#) ≈ 0#
sum-zero = S.sum-replicate-zero

sum-add : ∀ n (f g : Fin n → Carrier) →
  sum n (λ i → f i + g i) ≈ sum n f + sum n g
sum-add n = S.∑-distrib-+

sum-mulˡ : ∀ n c (f : Fin n → Carrier) →
  sum n (λ i → c * f i) ≈ c * sum n f
sum-mulˡ n c f = sym (S.*-distribˡ-sum c f)

sum-mulʳ : ∀ n c (f : Fin n → Carrier) →
  sum n (λ i → f i * c) ≈ sum n f * c
sum-mulʳ n c f = sym (S.*-distribʳ-sum c f)

sum-swap : ∀ m n (f : Fin m → Fin n → Carrier) →
  sum m (λ i → sum n (f i)) ≈
  sum n (λ j → sum m (λ i → f i j))
sum-swap m n = S.∑-comm

delta : ∀ {n} → Fin n → Fin n → Carrier
delta F.zero F.zero = 1#
delta F.zero (F.suc j) = 0#
delta (F.suc i) F.zero = 0#
delta (F.suc i) (F.suc j) = delta i j

select : ∀ n (i : Fin n) (f : Fin n → Carrier) →
  sum n (λ j → delta i j * f j) ≈ f i
select (N.suc n) F.zero f = trans (+-cong (*-identityˡ (f F.zero))
  (trans (sum-cong n _ _ (λ j → zeroˡ (f (F.suc j)))) (sum-zero n))) (+-identityʳ (f F.zero))
select (N.suc n) (F.suc i) f = trans (+-cong (zeroˡ (f F.zero)) (select n i (λ j → f (F.suc j)))) (+-identityˡ (f (F.suc i)))

delta-sym : ∀ {n} (i j : Fin n) → delta i j ≈ delta j i
delta-sym F.zero F.zero = refl
delta-sym F.zero (F.suc j) = refl
delta-sym (F.suc i) F.zero = refl
delta-sym (F.suc i) (F.suc j) = delta-sym i j
