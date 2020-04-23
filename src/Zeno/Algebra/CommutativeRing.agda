{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Structures
open import Relation.Binary

module Zeno.Algebra.CommutativeRing
  {ℓ} { A : Set ℓ} { _≈_ : Rel A ℓ } { _+_ mul -_ 0# 1# }
  (CR : IsCommutativeRing _≈_ _+_ mul -_ 0# 1#)
  where

infixl 7 _*_
_*_ = mul

open IsCommutativeRing CR
open import Zeno.Algebra.Group +-isGroup
open import Relation.Binary.Reasoning.Setoid setoid

x*y*z≈x*z*y : (x y z : A) → (x * y * z) ≈ (x * z * y)
x*y*z≈x*z*y x y z = begin
  x * y * z   ≈⟨ *-assoc x y z ⟩
  x * (y * z) ≈⟨ *-cong refl (*-comm y z) ⟩
  x * (z * y) ≈⟨ sym (*-assoc x z y) ⟩
  x * z * y   ∎
