{-# OPTIONS --without-K --safe #-}

module Zeno.Data.Rational.Cauchy where

import Data.Integer.Properties as ℤₚ
open import Data.Integer as ℤ using
  ( ℤ ; 0ℤ ) renaming
  ( _≤_ to _≤ᶻ_ )

open import Data.Nat as ℕ using ( ℕ ; zero ; suc )
open import Data.Rational.Unnormalised
open import Data.Rational.Unnormalised.Properties
open import Level renaming ( suc to lsuc )
open import Relation.Binary.Bundles
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Preorder as ≤-Reasoning

open import Zeno.Class.AbelianGroup ℤₚ.*-1-isAbelianGroup using () renaming
  ( x*y*z≈x*z*y to m*n*o≈m*o*n )

open import Zeno.Class.AbelianGroup +-0-isAbelianGroup
open import Zeno.Data.Integer.Lemmas

≤-preorder : Preorder 0ℓ 0ℓ 0ℓ
≤-preorder = record { isPreorder = ≤-isPreorder }

x≤y⇒0≤y-x : {x y : ℚᵘ} → x ≤ y → 0ℚᵘ ≤ y - x
x≤y⇒0≤y-x {x} {y} (*≤* ad≤cb) =
  let 0≤cb-ad = ℤₚ.m≤n⇒0≤n-m ad≤cb
  in *≤* (subst (_≤ᶻ_ 0ℤ) (sym (lemma-2 (↥ x) (↧ x) (↥ y) (↧ y))) 0≤cb-ad)

0≤y-x⇒x≤y : {x y : ℚᵘ} → 0ℚᵘ ≤ y - x → x ≤ y
0≤y-x⇒x≤y {x} {y} (*≤* ad≤cd) =
  *≤* (ℤₚ.0≤n-m⇒m≤n (subst (_≤ᶻ_ 0ℤ) (lemma-2 (↥ x) (↧ x) (↥ y) (↧ y)) ad≤cd))

+-monoˡ-≤ : {x y : ℚᵘ} → x ≤ y → (z : ℚᵘ) → z + x ≤ z + y
+-monoˡ-≤ {x} {y} x≤y z =
  let 0≤y-x     = x≤y⇒0≤y-x x≤y
      0≤z+y-z+x = ≤-trans 0≤y-x (≤-reflexive (y-x≈z+y-z+x x y z))
  in 0≤y-x⇒x≤y 0≤z+y-z+x

+-monoʳ-≤ : {x y : ℚᵘ} → x ≤ y → (z : ℚᵘ) → x + z ≤ y + z
+-monoʳ-≤ {x} {y} x≤y z =
  let 0≤y-x     = x≤y⇒0≤y-x x≤y
      0≤y+z-x+z = ≤-trans 0≤y-x (≤-reflexive (y-x≈y+z-x+z x y z))
  in 0≤y-x⇒x≤y 0≤y+z-x+z

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {x} {y} {u} {v} x≤y u≤v = begin
  x + u ∼⟨ +-monoʳ-≤ x≤y u ⟩
  y + u ∼⟨ +-monoˡ-≤ u≤v y ⟩
  y + v ∎
  where open ≤-Reasoning ≤-preorder

x<y≤z⇒x<z : {x y z : ℚᵘ} → x < y → y ≤ z → x < z
x<y≤z⇒x<z {x} {y} {z} (*<* ad<cb) (*≤* cf≤ed) =
  let a = ↥ x; b = ↧ x; b-1 = ↧ₙ x
      c = ↥ y; d = ↧ y; d-1 = ↧ₙ y
      e = ↥ z; f = ↧ z; f-1 = ↧ₙ z

      afd<ebd : a ℤ.* f ℤ.* d ℤ.< e ℤ.* b ℤ.* d
      afd<ebd = begin-strict
        a ℤ.* f ℤ.* d   ≡⟨ ℤₚ.*-assoc a f d ⟩
        a ℤ.* (f ℤ.* d) ≡⟨ cong (λ x₁ → {!a!} ℤ.* x₁) (ℤₚ.*-comm f d) ⟩
        a ℤ.* d ℤ.* f <⟨ {!!} ⟩
        c ℤ.* b ℤ.* f ≡⟨ {!!} ⟩
        c ℤ.* f ℤ.* b ≤⟨ {!!} ⟩
        e ℤ.* d ℤ.* b ≡⟨ {!!} ⟩
        e ℤ.* b ℤ.* d ∎
  in  *<* (ℤₚ.*-cancelʳ-<-non-neg {a ℤ.* f} d-1 afd<ebd)
    where open ℤₚ.≤-Reasoning


<-trans : Transitive  _<_
<-trans p<q q<r = {!≤-trans!}
