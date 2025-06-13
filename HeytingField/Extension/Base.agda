{-# OPTIONS --allow-unsolved-metas #-}

module HeytingField.Extension.Base where

open import Cubical.Foundations.Prelude

open import HeytingField.Base

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level

FieldExtension : ∀ (F : HeytingField ℓ ℓ') ℓ'' ℓ''' → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) (ℓ-suc ℓ'''))
FieldExtension F ℓ'' ℓ''' = Σ[ E ∈ HeytingField ℓ'' ℓ''' ] HeytingFieldHom F E