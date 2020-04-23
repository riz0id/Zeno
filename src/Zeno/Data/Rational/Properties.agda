{-# OPTIONS --without-K --safe #-}

import Data.Nat.Properties as ℕₚ
open import Data.Nat as ℕ using
  ( ℕ ; zero ; suc )

import Zeno.Data.Integer.Properties as ℤₚ
open import Data.Integer as ℤ using
  ( ℤ ; +[1+_] ; -[1+_] ; +_ ) renaming
  ( _≤_ to _≤ᶻ_ ; _<_ to _<ᶻ_ )

open import Data.Product
import Data.Sign as Sign
open import Function
open import Level using (0ℓ)
open import Zeno.Data.Rational.Base

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Zeno.Data.Rational.Properties where

open import Data.Rational.Unnormalised.Properties public

≤-preorder : Preorder 0ℓ 0ℓ 0ℓ
≤-preorder = record { isPreorder = ≤-isPreorder }

≤-poset : Poset 0ℓ 0ℓ 0ℓ
≤-poset = record { isPartialOrder = ≤-isPartialOrder }

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (*<* p<q) = *≤* (ℤₚ.<⇒≤ p<q)

drop‿*<* : {x y : ℚ} → x < y → ↥ x ℤ.* ↧ y <ᶻ ↥ y ℤ.* ↧ x
drop‿*<* (*<* ad<cb) = ad<cb

x<y⇒x≤y : _<_ ⇒ _≤_
x<y⇒x≤y {x} {y} = *≤* ∘ ℤₚ.<⇒≤ {↥ x ℤ.* ↧ y} ∘ drop‿*<*

x≤y<z⇒x<z : {x y z : ℚ} → x ≤ y → y < z → x < z
x≤y<z⇒x<z {x} {y} {z} (*≤* ad≤cb) (*<* cf<ed) =
  let a = ↥ x; b = ↧ x; b-1 = ↧ₙ x
      c = ↥ y; d = ↧ y; d-1 = ↧ₙ y
      e = ↥ z; f = ↧ z; f-1 = ↧ₙ z

      afd≤cfb : a ℤ.* f ℤ.* d ≤ᶻ c ℤ.* f ℤ.* b
      afd≤cfb = begin
        a ℤ.* f ℤ.* d ≡⟨ ℤₚ.x*y*z≈x*z*y a f d ⟩
        a ℤ.* d ℤ.* f ≤⟨ ℤₚ.*-monoʳ-≤-pos (ℚ.denominator-1 z)  ad≤cb ⟩
        c ℤ.* b ℤ.* f ≡⟨ ℤₚ.x*y*z≈x*z*y c b f ⟩
        c ℤ.* f ℤ.* b ∎

      cfb<ebd : c ℤ.* f ℤ.* b <ᶻ e ℤ.* b ℤ.* d
      cfb<ebd = begin-strict
        c ℤ.* f ℤ.* b <⟨ ℤₚ.*-monoʳ-<-pos (ℚ.denominator-1 x) cf<ed ⟩
        e ℤ.* d ℤ.* b ≡⟨ ℤₚ.x*y*z≈x*z*y e d b ⟩
        e ℤ.* b ℤ.* d ∎

      afd<ebd = ℤₚ.≤-<-trans afd≤cfb cfb<ebd

  in  *<* (ℤₚ.*-cancelʳ-<-non-neg (suc (ℚ.denominator-1 y)) afd<ebd)
    where open ℤₚ.≤-Reasoning

x<y≤z⇒x<z : {x y z : ℚ} → x < y → y ≤ z → x < z
x<y≤z⇒x<z {x} {y} {z} (*<* ad<cb) (*≤* cf≤ed) =
  let a = ↥ x; b = ↧ x; b-1 = ↧ₙ x
      c = ↥ y; d = ↧ y; d-1 = ↧ₙ y
      e = ↥ z; f = ↧ z; f-1 = ↧ₙ z

      afd<ebd : a ℤ.* f ℤ.* d <ᶻ e ℤ.* b ℤ.* d
      afd<ebd = begin-strict
        a ℤ.* f ℤ.* d ≡⟨ ℤₚ.x*y*z≈x*z*y a f d ⟩
        a ℤ.* d ℤ.* f <⟨ ℤₚ.*-monoʳ-<-pos (ℚ.denominator-1 z) ad<cb ⟩
        c ℤ.* b ℤ.* f ≡⟨ ℤₚ.x*y*z≈x*z*y c b f ⟩
        c ℤ.* f ℤ.* b ≤⟨ ℤₚ.*-monoʳ-≤-pos (ℚ.denominator-1 x) cf≤ed ⟩
        e ℤ.* d ℤ.* b ≡⟨ ℤₚ.x*y*z≈x*z*y e d b ⟩
        e ℤ.* b ℤ.* d ∎

  in  *<* (ℤₚ.*-cancelʳ-<-non-neg (suc (ℚ.denominator-1 y)) afd<ebd)
    where open ℤₚ.≤-Reasoning

<-trans : Transitive _<_
<-trans x<y y<z = x≤y<z⇒x<z (x<y⇒x≤y x<y) y<z

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans = x<y≤z⇒x<z

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans x≤y y<z = x≤y<z⇒x<z x≤y y<z

compare : Trichotomous _≃_ _<_
compare x y = case ℤₚ.<-cmp (↥ x ℤ.* ↧ y) (↥ y ℤ.* ↧ x) of λ
  { (tri< a<b a≢b a≯b) → tri< (*<* a<b) (a≢b ∘ drop-*≡*) (a≯b ∘ drop‿*<*)
  ; (tri≈ a≮b a≡b a≯b) → tri≈ (a≮b ∘ drop‿*<*) (*≡* a≡b) (a≯b ∘ drop‿*<*)
  ; (tri> a≮b a≢b a>b) → tri> (a≮b ∘ drop‿*<*) (a≢b ∘ drop-*≡*) (*<* a>b)
  }

isStrictTotalOrder : IsStrictTotalOrder _≃_ _<_
isStrictTotalOrder = record
  { isEquivalence = ≃-isEquivalence
  ; trans         = <-trans
  ; compare       = compare
  }

strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
strictTotalOrder = record { isStrictTotalOrder = isStrictTotalOrder }

module <ℚ = StrictTotalOrder strictTotalOrder

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    <ℚ.<-resp-≈
    <⇒≤
    <-≤-trans
    ≤-<-trans
    public

↥∣x∣≡Z∣↥x∣ : ∀ x → ↥ ∣ x ∣ ≡ ℤ.pos ℤ.∣ ↥ x ∣
↥∣x∣≡Z∣↥x∣ (mkℚᵘ (+ n)    d) = refl
↥∣x∣≡Z∣↥x∣ (mkℚᵘ -[1+ n ] d) = refl
  where open ≡-Reasoning

s◃∣x∣≡+∣x∣ : ∀ x → ℤ.sign (↥ ∣ x ∣) ≡ Sign.+
s◃∣x∣≡+∣x∣ (mkℚᵘ (+ n)    d) = refl
s◃∣x∣≡+∣x∣ (mkℚᵘ -[1+ n ] d) = refl

abs-cong : ∀ {x y} → x ≃ y → ∣ x ∣ ≃ ∣ y ∣
abs-cong {mkℚᵘ (+ nx)   dx-1}    {mkℚᵘ (+ ny)    dy-1}       (*≡* x≃y) = *≡* x≃y
abs-cong {mkℚᵘ (+ 0)    _}       {mkℚᵘ -[1+ _ ]  0}          (*≡* ())
abs-cong {mkℚᵘ (+ 0)    _}       {mkℚᵘ -[1+ _ ]  (suc _)}    (*≡* ())
abs-cong {mkℚᵘ +[1+ _ ] _}       {mkℚᵘ -[1+ _ ]  _}          (*≡* ())
abs-cong {mkℚᵘ -[1+ _ ] 0}       {mkℚᵘ (+ 0)     0}          (*≡* ())
abs-cong {mkℚᵘ -[1+ _ ] 0}       {mkℚᵘ +[1+ ny ] 0}          (*≡* ())
abs-cong {mkℚᵘ -[1+ _ ] 0}       {mkℚᵘ (+ 0)     (suc dy-1)} (*≡* ())
abs-cong {mkℚᵘ -[1+ _ ] 0}       {mkℚᵘ +[1+ ny ] (suc dy-1)} (*≡* ())
abs-cong {mkℚᵘ -[1+ _ ] (suc _)} {mkℚᵘ (+ 0)     0}          (*≡* ())
abs-cong {mkℚᵘ -[1+ _ ] (suc _)} {mkℚᵘ +[1+ ny ] 0}          (*≡* ())
abs-cong {mkℚᵘ -[1+ _ ] (suc _)} {mkℚᵘ (+ 0)     (suc dy-1)} (*≡* ())
abs-cong {mkℚᵘ -[1+ _ ] (suc _)} {mkℚᵘ +[1+ ny ] (suc dy-1)} (*≡* ())
abs-cong {mkℚᵘ -[1+ nx ] 0}      {mkℚᵘ -[1+ ny ] 0}          (*≡* x≃y) =
  *≡* (cong +[1+_] (ℤₚ.-[1+-injective x≃y))

abs-cong {mkℚᵘ -[1+ nx ] 0}      {mkℚᵘ -[1+ ny ] (suc dy-1)} (*≡* x≃y) =
  *≡* (cong +[1+_] (ℤₚ.-[1+-injective x≃y))

abs-cong {mkℚᵘ -[1+ nx ] (suc dx-1)} {mkℚᵘ (-[1+_] ny) zero} (*≡* x≃y)
  = *≡* (cong +[1+_] (ℤₚ.-[1+-injective x≃y))

abs-cong {mkℚᵘ -[1+ nx ] (suc dx-1)} {mkℚᵘ -[1+ ny ] (suc dy-1)} (*≡* x≃y) =
  *≡* (cong +[1+_] (ℤₚ.-[1+-injective x≃y))
