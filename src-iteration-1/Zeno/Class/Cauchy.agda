
open import Algebra.Structures
open import Data.Product
open import Data.Vec
open import Relation.Binary
open import Relation.Nullary.Decidable
import Relation.Binary.Reasoning.Preorder as <-Reasoning

module Zeno.Class.Cauchy
  {ℓ} {A : Set ℓ} { _+_ -_ 0# }
  { _≤_ _≈_  : Rel A ℓ }
  ( +-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_ )
  ( isTotal  : IsTotalOrder _≈_ _≤_  )
  ( isGroup  : IsGroup _≈_ _+_ 0# -_ )
  where

open IsGroup isGroup

-- equational reasoning (_<_) --------------------------------------------------
open import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_
open IsTotalOrder isTotal using (isDecTotalOrder)
open IsStrictTotalOrder (<-isStrictTotalOrder₂ {!!})

<-preorder : Preorder ℓ ℓ ℓ
<-preorder = record { isPreorder = {!!} }

open <-Reasoning <-preorder
--------------------------------------------------------------------------------

open import Zeno.Class.Modulus +-mono-≤ isTotal isGroup

open import Data.Nat as ℕ using ( ℕ ) renaming
  ( _≤_ to _≤ₙ_
  ; _≟_ to _≟ₙ_
  )

open import Data.Fin as Fin using ( Fin ; toℕ )

ℕ₀ : Set
ℕ₀ = Σ[ n ∈ ℕ ] False (0 ≟ₙ n)

A₀ : Set ℓ
A₀ = Σ[ x ∈ A ] 0# < x

-- frequently used equivalence, might as well make it an independent structure.
data _≺_ {n} : ℕ₀ → Fin n → Set where
  *≺* : {x : ℕ₀} {y : Fin n}
      → proj₁ x ≤ₙ toℕ y → x ≺ y

-- metric for the space underlying the convergence, should at least satisfy mere
-- relation properties or something has gone terrible wrong.
data _~_ : A → A → A₀ → Set ℓ where
  Merely : ∀ {x y : A} {ε : A₀}
         → ∣ x - y ∣' < proj₁ ε → (x ~ y) ε

data ∁-Seq {n} (f : Fin n → A) (ε : A₀) : Set ℓ where
  mk∁-Seq : ∀ {k : ℕ₀} (p q : Fin n)
          → k ≺ p → k ≺ q → (f p ~ f q) ε → ∁-Seq f ε

data ∁ℝ : Set ℓ where
  mk∁ℝ : ∀ {n : ℕ₀}
       → (ε : A₀)
       → (seq : Vec A (proj₁ n))
       → ∁-Seq (lookup seq) ε
       → ∁ℝ

∁-singleton : A → A₀ → ∁ℝ
∁-singleton x ε =
  let ix   = Fin.fromℕ 0
      mere = Merely
           ( (begin
             ∣ x - x ∣' ≈⟨ {!!} ⟩
             0# ∼⟨ {!proj₂ ε!} ⟩
             proj₁ ε ∎)
           , {!!}
           )
      conv = mk∁-Seq ix ix {!!} {!!} mere
  in mk∁ℝ ε [ x ] conv

{-
open import Data.Nat as ℕ using (ℕ) renaming
  ( suc to sucₙ )

open import Data.Fin as Fin using
  ( Fin ; zero ) renaming
  ( _<_  to _<ₙ_ )

data ∁-Seq {n : Σ[ n ∈ ℕ ] n} (f : Fin n → A) (ε : A) : Set ℓ where
  mk∁-Seq : (k : Σ[ m ∈ Fin (sucₙ n) ] zero <ₙ m)
          → ∁-Seq f ε

data ∁-ℝ : Set ℓ where
  mk∁-ℝ : (ε : A)
        → (seq : List A)
        → ∁-Seq (lookup seq) ε
        → ∁-ℝ

∁-singleton : A → ∁-ℝ
∁-singleton x = {!!}
-}
