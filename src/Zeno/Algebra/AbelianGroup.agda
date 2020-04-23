{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Structures
open import Relation.Binary

module Zeno.Algebra.AbelianGroup
  {ℓ} { A : Set ℓ} { _≈_ : Rel A ℓ } { _∙_ 0# -_ }
  (AG : IsAbelianGroup _≈_ _∙_ 0# -_)
  where

open IsAbelianGroup AG
open import Zeno.Algebra.Group isGroup
open import Relation.Binary.Reasoning.Setoid setoid

-‿∙-comm : (x y : A) → (- x - y) ≈ (- (x ∙ y))
-‿∙-comm x y =
  let lemma : ((x ∙ y) ∙ (- y - x)) ≈ 0#
      lemma = begin
        (x ∙ y) ∙ (- y - x) ≈⟨ assoc x y (- y - x)                 ⟩
        x ∙ (y ∙ (- y - x)) ≈⟨ ∙-congˡ (sym (assoc y (- y) (- x))) ⟩
        x ∙ (y - y - x)     ≈⟨ ∙-congˡ (∙-congʳ (inverseʳ y))      ⟩
        x ∙ (0# - x)        ≈⟨ ∙-congˡ (identityˡ (- x))           ⟩
        x - x               ≈⟨ inverseʳ x                          ⟩
        0#                  ∎
  in begin
    - x - y                                     ≈⟨ comm (- x) (- y)                    ⟩
    - y - x                                     ≈⟨ sym (identityˡ (- y - x))           ⟩
    0# ∙ (- y - x)                              ≈⟨ ∙-congʳ (sym (inverseˡ (x ∙ y)))    ⟩
    (((- (x ∙ y)) ∙ (x ∙ y)) ∙ (- y - x))       ≈⟨ assoc (- (x ∙ y)) (x ∙ y) (- y - x) ⟩
    ((- (x ∙ y)) ∙ ((x ∙ y) ∙ ((- y) ∙ (- x)))) ≈⟨ ∙-congˡ lemma                       ⟩
    (- (x ∙ y)) ∙ 0#                            ≈⟨ identityʳ (- (x ∙ y))               ⟩
    - (x ∙ y) ∎

y-x≈z∙y-z∙x : (x y z : A) → (y - x) ≈ ((z ∙ y) - (z ∙ x))
y-x≈z∙y-z∙x x y z = begin
  y - x                 ≈⟨ sym (identityˡ (y - x))             ⟩
  0# ∙ (y - x)          ≈⟨ ∙-congʳ (sym (inverseʳ z))          ⟩
  (z - z) ∙ (y - x)     ≈⟨ assoc z (- z) (y - x)               ⟩
  z ∙ ((- z) ∙ (y - x)) ≈⟨ ∙-congˡ (sym (assoc (- z) y (- x))) ⟩
  z ∙ ((- z) ∙ y - x)   ≈⟨ ∙-congˡ (∙-congʳ (comm (- z) y))    ⟩
  z ∙ (y - z - x)       ≈⟨ ∙-congˡ (assoc y (- z) (- x))       ⟩
  z ∙ (y ∙ (- z - x))   ≈⟨ sym (assoc z y (- z - x))           ⟩
  (z ∙ y) ∙ (- z - x)   ≈⟨ ∙-congˡ (-‿∙-comm z x)             ⟩
  (z ∙ y) - (z ∙ x)     ∎

y-x≈y∙z-x∙z : (x y z : A) → (y - x) ≈ ((y ∙ z) - (x ∙ z))
y-x≈y∙z-x∙z x y z = begin
  (y - x)             ≈⟨ sym (identityʳ (y - x))          ⟩
  (y - x) ∙ 0#        ≈⟨ ∙-congˡ (sym (inverseʳ z))       ⟩
  (y - x) ∙ (z - z)   ≈⟨ sym (assoc (y - x) z (- z))      ⟩
  (y - x) ∙ z - z     ≈⟨ ∙-congʳ (assoc y (- x) z)        ⟩
  y ∙ ((- x) ∙ z) - z ≈⟨ ∙-congʳ (∙-congˡ (comm (- x) z)) ⟩
  y ∙ (z - x) - z     ≈⟨ ∙-congʳ (sym (assoc y z (- x)))  ⟩
  y ∙ z - x - z       ≈⟨ assoc (y ∙ z) (- x) (- z)        ⟩
  (y ∙ z) ∙ (- x - z) ≈⟨ ∙-congˡ (-‿∙-comm x z)          ⟩
  (y ∙ z) - (x ∙ z)   ∎
