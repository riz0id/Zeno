{-# OPTIONS --without-K --safe #-}

open import Data.Fin as Fin using
  ( Fin ; toℕ ; fromℕ )
open import Data.Product
open import Data.Integer as ℤ using
  ( ℤ ; 0ℤ ; 1ℤ )
import Data.Integer.Properties as ℤₚ
open import Data.Rational.Unnormalised
open import Data.Rational.Unnormalised.Properties
open import Data.Unit using (tt)
open import Data.Vec
open import Relation.Nullary.Decidable

module Zeno.Class.Cauchy where

open import Data.Nat as ℕ using ( ℕ ) renaming
  ( _≤_ to _≤ₙ_
  ; _≟_ to _≟ₙ_
  )

open import Zeno.Data.Rational.Cauchy
open import Zeno.Class.Modulus

ℕ₀ : Set
ℕ₀ = Σ[ n ∈ ℕ ] False (n ≟ₙ 0)

1ℕ₀ : ℕ₀
1ℕ₀ = 1 , tt

ℚ⁺ : Set
ℚ⁺ = Σ[ q ∈ ℚᵘ ] 0ℚᵘ < q

data ∁-Seq {n} (f : Fin n → ℚᵘ) : Set where
  Converges : ∀ (ε : ℚ⁺) k x y
            → k ≤ₙ toℕ x
            → k ≤ₙ toℕ y
            → ∣ f x - f y ∣' < proj₁ ε
            → ∁-Seq f

record ℝ {n} : Set where
  field
    seq  : Vec ℚᵘ n
    conv : ∁-Seq (lookup seq)

ℚ-to-ℝ : ℚᵘ → ℚ⁺ → ℝ
ℚ-to-ℝ x ε =
  let seq   = [ x ]
      ix    = fromℕ 0
  in record
  { seq  = seq
  ; conv = Converges ε 0 Fin.zero Fin.zero ℕ.z≤n ℕ.z≤n
    {!!}
  } where open ℤₚ.≤-Reasoning
