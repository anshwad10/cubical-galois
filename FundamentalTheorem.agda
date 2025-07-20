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
    G : Group ?
    G = GaloisGroup F E

    theMap : Subgroup G → Subextension F (GaloisExtension→Extension E) ?
    theMap = OfSubgroup.FixedSubextension

    goalType : Type ?
    goalType = isEquiv theMap

  theTheorem : goalType
  theTheorem = {!   !}
