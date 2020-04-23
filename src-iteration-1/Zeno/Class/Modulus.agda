
open import Algebra
open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.Core
import Relation.Binary.Reasoning.Preorder as ≤-Reasoning

module Zeno.Class.Modulus
  {ℓ} { A : Set ℓ} { _+_ -_ 0# }
  { _≤_ _≈_ : Rel A ℓ }
  ( +-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_ )
  ( isTotal  : IsTotalOrder _≈_ _≤_  )
  ( isGroup  : IsGroup _≈_ _+_ 0# -_ )
  where

open IsGroup isGroup
open IsTotalOrder isTotal renaming
  ( refl       to ≤-refl
  ; isPreorder to ≤-isPreorder )

∣_∣ : A → Σ[ x ∈ A ] 0# ≤ x
∣ x ∣ with total 0# x
... | inj₁ 0≤x =   x , 0≤x
... | inj₂ x≤0 = - x , (begin -- this is just subst₂ over _≈_
  0#     ≈˘⟨ inverseʳ x ⟩
  x - x  ∼⟨ +-mono-≤ x≤0 ≤-refl ⟩
  0# - x ≈⟨ identityˡ (- x) ⟩
  - x    ∎)
  where ≤-preorder : Preorder ℓ ℓ ℓ
        ≤-preorder = record { isPreorder = ≤-isPreorder }

        open ≤-Reasoning ≤-preorder

∣_∣' : Op₁ A
∣ x ∣' = proj₁ ∣ x ∣
