{-# OPTIONS --safe --without-K #-}
module Coding.Decoder where

open import Coding.Binary
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (all?; any?)
open import Data.Bool.Properties using (_≟_; xor-same)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as E

module Single {m n} (H : Matrix m n) where
  Column = λ j → tr H j
  search : (s : Word m) → Dec (Σ (Fin n) (λ j → Column j ≐ s))
  search s = any? (λ j → all? (λ i → H i j ≟ s i))
  correct : Word n → Word n
  correct r with search (apply H r)
  ... | yes (j , _) = r ⊞ delta j
  ... | no _ = r

  clean : (∀ j → Column j ≐ zero → ⊥) → ∀ c → Kernel H c → correct c ≐ c
  clean nz c valid with search (apply H c)
  ... | yes (j , eq) = ⊥-elim (nz j (λ i → E.trans (eq i) (valid i)))
  ... | no _ = λ _ → E.refl

  flip-syndrome : ∀ c → Kernel H c → ∀ j → apply H (c ⊞ delta j) ≐ Column j
  flip-syndrome c valid j i = E.trans (syndrome-add H c (delta j) i)
    (E.cong₂ _xor_ (valid i) (dot-unit (H i) j))

  one-error : (∀ j k → Column j ≐ Column k → j E.≡ k) →
    ∀ c → Kernel H c → ∀ j → correct (c ⊞ delta j) ≐ c
  one-error inj c valid j with search (apply H (c ⊞ delta j))
  ... | no miss = ⊥-elim (miss (j , λ i → E.sym (flip-syndrome c valid j i)))
  ... | yes (k , eq) with inj k j (λ i → E.trans (eq i) (flip-syndrome c valid j i))
  ...   | E.refl = λ i → E.trans (Law.+-assoc (c i) (delta j i) (delta j i))
    (E.trans (E.cong (c i xor_) (xor-same (delta j i))) (Law.+-identityʳ (c i)))
