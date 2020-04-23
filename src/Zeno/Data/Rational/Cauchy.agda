{-# OPTIONS --without-K --safe #-}

open import Data.Fin using ( Fin ; toℕ )
open import Data.Integer as ℤ using (ℤ) renaming
  ( _≤_ to _≤ᶻ_ ; _<_ to _<ᶻ_ )
import Zeno.Data.Integer.Properties as ℤₚ
open import Data.Product
open import Data.Nat as ℕ using (ℕ) renaming
  ( _<_ to _<ⁿ_ ; _≤_ to _≤ⁿ_ )
open import Data.Vec
open import Zeno.Data.Rational.Base
open import Zeno.Data.Rational.Properties
open import Relation.Binary.PropositionalEquality hiding
  ([_])

module Zeno.Data.Rational.Cauchy where

ℚ⁺ : Set
ℚ⁺ = Σ[ q ∈ ℚ ] 0ℚ < q

record ∁-Seq {n} (f : Fin n → ℚ) : Set where
  field
    ε    : ℚ⁺
    k    : ℕ
    k<x  : Σ[ x ∈ Fin n ] k ≤ⁿ toℕ x
    k<y  : Σ[ y ∈ Fin n ] k ≤ⁿ toℕ y
    Conv : ∣ f (proj₁ k<x) - f (proj₁ k<y) ∣ < proj₁ ε

record ℝ {n} : Set where
  field
    seq  : Vec ℚ n
    conv : ∁-Seq (lookup seq)

ℚ-to-ℝ : ℚ → ℚ⁺ → ℝ
ℚ-to-ℝ x ε = record
  { seq  = [ x ]
  ; conv = record
    { ε    = ε
    ; k    = 0
    ; k<x  = Fin.zero , _≤ⁿ_.z≤n
    ; k<y  = Fin.zero , _≤ⁿ_.z≤n
    ; Conv = begin-strict
      ∣ x - x ∣ ≈⟨ abs-cong (+-inverseʳ x) ⟩
      ∣ 0ℚ ∣    <⟨ proj₂ ε ⟩
      proj₁ ε   ∎
    }
  } where open ≤-Reasoning
