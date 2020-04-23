{-# OPTIONS --without-K --safe #-}

open import Algebra
import Data.Nat as ℕ
import Data.Integer.Properties as ℤₚ
open import Data.Integer as ℤ using
  ( ℤ ; 0ℤ ; 1ℤ
  ; _*_ ; _-_
  ; +[1+_] ; -[1+_] ; +_
  ) renaming
  ( _≤_ to _≤ᶻ_ )

open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Zeno.Data.Rational.Base where

open import Data.Rational.Unnormalised.Properties
open import Data.Rational.Unnormalised public renaming
  ( ℚᵘ to ℚ ; 0ℚᵘ to 0ℚ )

open IsTotalOrder ≤-isTotalOrder using
  (total)
{-
∣_∣ : ℚ → Σ[ p ∈ ℚ ] 0ℚ ≤ p
∣ p@(mkℚᵘ n d-1) ∣ with total 0ℚ p
... | inj₁ 0≤x       =   p , 0≤x
... | inj₂ (*≤* x≤0) = - p , *≤* (begin
  0ℤ               ≡⟨ sym (ℤₚ.+-inverseʳ n) ⟩
  n ℤ.- n          ≡⟨ cong (ℤ._- n) (sym (ℤₚ.*-identityʳ n)) ⟩
  (n ℤ.* 1ℤ) ℤ.- n ≤⟨ ℤₚ.+-monoˡ-≤ (ℤ.- n) x≤0 ⟩
  0ℤ ℤ.-   n       ≡⟨ ℤₚ.+-identityˡ (ℤ.- n) ⟩
  ℤ.- n            ≡⟨ sym (ℤₚ.*-identityʳ (ℤ.- n)) ⟩
  ℤ.- n ℤ.* 1ℤ    ∎)
  where open ℤₚ.≤-Reasoning
-}
∣_∣ : Op₁ ℚ
∣ mkℚᵘ (+ n)    d ∣ = mkℚᵘ (+ n)    d
∣ mkℚᵘ -[1+ n ] d ∣ = mkℚᵘ +[1+ n ] d
