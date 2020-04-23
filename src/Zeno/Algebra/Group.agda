{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Structures
open import Relation.Binary

module Zeno.Algebra.Group
  {ℓ} { A : Set ℓ} { _≈_ : Rel A ℓ } { _∙_ 0# -_ }
  (SG : IsGroup _≈_ _∙_ 0# -_)
  where

open IsGroup SG
open import Relation.Binary.Reasoning.Setoid setoid

x+y-y≈x : (x y : A) → (x ∙ y - y) ≈ x
x+y-y≈x x y = begin
  x ∙ y - y   ≈⟨ assoc x y (- y) ⟩
  x ∙ (y - y) ≈⟨ ∙-congˡ (inverseʳ y) ⟩
  x ∙ 0#      ≈⟨ identityʳ x ⟩
  x           ∎
