-- The goal is to turn this into --safe
{-# OPTIONS --allow-unsolved-metas #-}

module FundamentalTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Subgroup

open import HeytingField

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level

module _ (F : HeytingField ℓ ℓ') (E : GaloisExtension F ℓ'' ℓ''') where
  private
    G : Group (ℓ-max (ℓ-max ℓ ℓ'') ℓ''')
    G = GaloisGroup F E

    theMap : Subgroup G → Subextension F (GaloisExtension→Extension E) ℓ'''
    theMap = {!   !}

    goalType : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
    goalType = isEquiv theMap

  -- theTheorem : goalType
  -- theTheorem = {!   !}
