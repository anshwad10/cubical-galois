{-# OPTIONS --allow-unsolved-metas #-}

module HeytingField.Extension.Galois where

open import Cubical.Foundations.Prelude

open import HeytingField.Base
open import HeytingField.Properties

open import HeytingField.Extension.Base

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  F : HeytingField ℓ ℓ'

module _ {F : HeytingField ℓ ℓ'} (E : FieldExtension F ℓ'' ℓ''') where
  IsSeparableExtension : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
  IsSeparableExtension = {!   !}

  IsAlgebraicExtension : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
  IsAlgebraicExtension = {!   !}

  IsGaloisExtension : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
  IsGaloisExtension = {!   !}

SeparableExtension : ∀ (F : HeytingField ℓ ℓ') ℓ'' ℓ''' → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
SeparableExtension F ℓ'' ℓ''' = Σ[ E ∈ HeytingField ℓ'' ℓ''' ]
                                Σ[ F→E ∈ HeytingFieldHom F E ]
                                IsSeparableExtension (E , F→E)

AlgebraicExtension : ∀ (F : HeytingField ℓ ℓ') ℓ'' ℓ''' → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
AlgebraicExtension F ℓ'' ℓ''' = Σ[ E ∈ HeytingField ℓ'' ℓ''' ]
                                Σ[ F→E ∈ HeytingFieldHom F E ]
                                IsAlgebraicExtension (E , F→E)

GaloisExtension : ∀ (F : HeytingField ℓ ℓ') ℓ'' ℓ''' → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
GaloisExtension F ℓ'' ℓ''' = Σ[ E ∈ HeytingField ℓ'' ℓ''' ]
                                Σ[ F→E ∈ HeytingFieldHom F E ]
                                IsGaloisExtension (E , F→E)

GaloisExtension→Extension : GaloisExtension F ℓ'' ℓ''' → FieldExtension F ℓ'' ℓ'''
GaloisExtension→Extension (E , F→E , _) = (E , F→E)