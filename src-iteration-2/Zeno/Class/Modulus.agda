{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Product
open import Data.Integer as ℤ using
  ( ℤ ; 0ℤ ; 1ℤ
  ; _*_ ; _-_
  ) renaming
  ( _≤_ to _≤ᶻ_ )
import Data.Integer.Properties as ℤₚ
open import Data.Nat as ℕ using (ℕ)
open import Data.Rational.Unnormalised as ℚᵘ using
  ( ℚᵘ ; 0ℚᵘ
  ; _≤_ ; *≤* ; -_; ↥_; ↧_
  )
open import Data.Rational.Unnormalised.Properties
open import Data.Sum
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Preorder as ≤-Reasoning

open import Zeno.Data.Rational.Cauchy

module Zeno.Class.Modulus where

open IsTotalOrder ≤-isTotalOrder using (total)

∣_∣ : ℚᵘ → Σ[ p ∈ ℚᵘ ] 0ℚᵘ ≤ p
∣ p@(ℚᵘ.mkℚᵘ n d-1) ∣ with total 0ℚᵘ p
... | inj₁ 0≤x       =   p , 0≤x
... | inj₂ (*≤* x≤0) = - p , *≤* (begin
  0ℤ             ≡⟨ sym (ℤₚ.+-inverseʳ n) ⟩
  n - n          ≡⟨ cong (_- n) (sym (ℤₚ.*-identityʳ n)) ⟩
  (n * 1ℤ) ℤ.- n ≤⟨ ℤₚ.+-monoˡ-≤ (ℤ.- n) x≤0 ⟩
  0ℤ ℤ.- n       ≡⟨ ℤₚ.+-identityˡ (ℤ.- n) ⟩
  ℤ.- n          ≡⟨ sym (ℤₚ.*-identityʳ (ℤ.- n)) ⟩
  ℤ.- n * 1ℤ     ∎)
  where open ℤₚ.≤-Reasoning

∣_∣' : Op₁ ℚᵘ
∣ x ∣' = proj₁ ∣ x ∣
