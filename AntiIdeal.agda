{-# OPTIONS --allow-unsolved-metas #-}

module AntiIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
import Cubical.Data.Int as ℤ
open import Cubical.Data.Int.Divisibility
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.Instances.Int

private variable
  ℓ ℓ' ℓ'' : Level

module AntiIdeal (R' : CommRing ℓ) where
  private R = fst R'
  open CommRingStr (snd R')
  open CommRingTheory R'

  record isAntiIdeal (I : R → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor makeIsAntiIdeal
    field
      is-prop-valued : ∀ x → isProp (I x)
      +Coclosed : ∀ x y → I (x + y) → ∥ I x ⊎ I y ∥₁
      apart0 : ¬ I 0r
      ·RepelsL : ∀ x y → I (x · y) → I x

    ·RepelsR : ∀ x y → I (x · y) → I y
    ·RepelsR x y Ixy = ·RepelsL y x (subst I (·Comm x y) Ixy)

  AntiIdeal : ∀ ℓ' → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  AntiIdeal ℓ' = Σ[ I ∈ (R → Type ℓ') ] isAntiIdeal I

  open CommIdeal R'

  NegationIdeal : AntiIdeal ℓ → CommIdeal
  NegationIdeal (I , p) = (λ x → (¬ I x) , isProp¬ _) ,
    makeIsCommIdeal (λ ¬Ix ¬Iy Ix+y → 
        PT.rec isProp⊥ (λ where
          (inl Ix) → ¬Ix Ix
          (inr Iy) → ¬Iy Iy
        ) (+Coclosed _ _ Ix+y)
      ) apart0 λ r ¬Ix Irx → ¬Ix (·RepelsR _ _ Irx)
    where open isAntiIdeal p

open AntiIdeal
open CommIdeal

Order : Type₁
Order = CommIdeal ℤCommRing

AntiOrder : ∀ ℓ → Type (ℓ-suc ℓ)
AntiOrder = AntiIdeal ℤCommRing

open isAntiIdeal
open ℤ

FGAntiOrder : ℤ → AntiOrder ℓ
FGAntiOrder n .fst x = n ∣ x → ⊥*
FGAntiOrder n .snd .is-prop-valued x = isPropΠ λ _ → isProp⊥*
FGAntiOrder n .snd .+Coclosed x y p with dec∣ n x | dec∣ n y
... | yes p₁ | yes p₂ = ⊥.elim* (p (∣-+ p₁ p₂))
... | yes _ | no ¬p = ∣ inr (lift ∘ ¬p) ∣₁
... | no ¬p | _ = ∣ inl (lift ∘ ¬p) ∣₁
FGAntiOrder n .snd .apart0 p = lower (p ∣-zeroʳ)
FGAntiOrder n .snd .·RepelsL x y p n∣x = p (∣-left· n∣x)