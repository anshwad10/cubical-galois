-- The goal is to be able to turn this into --safe
{-# OPTIONS --allow-unsolved-metas #-}

module FundamentalTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Subgroup

open import HeytingField

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level

module _ (F : HeytingField ℓ ℓ') (E : GaloisExtension F (ℓ-max ℓ ℓ'') ℓ'') where
  private
    G : Group (ℓ-max ℓ ℓ'')
    G = GaloisGroup F E

    theMap : Subgroup G → Subextension F (GaloisExtension→Extension E) (ℓ-max ℓ ℓ'')
    theMap = {!OfSubgroup.FixedSubextension {F = F} {E = E .fst} {F→E = E .snd .fst}!}

    goalType : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') (ℓ-suc ℓ''))
    goalType = isEquiv theMap

  theTheorem : goalType
  theTheorem = {!   !}
