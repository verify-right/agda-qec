{-# OPTIONS --safe --without-K #-}
module Coding.Hamming where

open import Coding.Binary
import Data.Empty
open import Coding.Decoder
import Data.Fin.Base as F
import Data.Fin.Properties as FP
import Data.Nat.Base as N
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as E
open import Relation.Nullary.Decidable using (from-yes)

-- The columns are the seven nonzero three-bit words, least significant bit first.
H : Matrix 3 7
H i j = bit (N.suc (F.toℕ j)) (F.toℕ i)
module D = Single H
asNat : Bool → N.ℕ
asNat false = 0
asNat true = 1
number : Word 3 → N.ℕ
number v = asNat (v F.zero) N.+ 2 N.* asNat (v (F.suc F.zero)) N.+ 4 N.* asNat (v (F.suc (F.suc F.zero)))
number-cong : ∀ (a b : Word 3) → a ≐ b → number a E.≡ number b
number-cong a b eq rewrite eq F.zero | eq (F.suc F.zero) | eq (F.suc (F.suc F.zero)) = E.refl
column-value : ∀ j → number (D.Column j) E.≡ N.suc (F.toℕ j)
column-value = from-yes (FP.all? (λ j → number (D.Column j) NP.≟ N.suc (F.toℕ j)))

distinct : ∀ j k → D.Column j ≐ D.Column k → j E.≡ k
distinct j k eq = FP.toℕ-injective (NP.suc-injective (E.trans (E.sym (column-value j))
  (E.trans (number-cong _ _ eq) (column-value k))))
nonzero : ∀ j → D.Column j ≐ zero → Data.Empty.⊥
nonzero j eq with E.trans (E.sym (column-value j)) (number-cong (D.Column j) zero eq)
... | ()


recover-one = D.one-error distinct
recover-clean = D.clean nonzero
