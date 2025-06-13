{-# OPTIONS --allow-unsolved-metas #-}

module HeytingField.Extension.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Group

open import HeytingField.Base

open import HeytingField.Extension.Base
open import HeytingField.Extension.Galois

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ''''' : Level
  F G H : HeytingField ℓ ℓ'
  E E' E'' : FieldExtension F ℓ'' ℓ'''

module _ (F : HeytingField ℓ ℓ') ((E , F→E , _) : FieldExtension F ℓ'' ℓ''') ((E' , F→E' , _) : FieldExtension F ℓ'''' ℓ''''') where
  record IsExtensionHom (f : ⟨ E ⟩ → ⟨ E' ⟩): Type (ℓ-max ℓ ℓ'''') where
    field
      presInc : ∀ x → f (F→E x) ≡ F→E' x

  ExtensionHom : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ'') ℓ''') ℓ'''') ℓ''''')
  ExtensionHom = Σ[ f ∈ HeytingFieldHom E E' ] IsExtensionHom (f .fst)

  ExtensionEquiv : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ'') ℓ''') ℓ'''') ℓ''''')
  ExtensionEquiv = Σ[ f ∈ HeytingFieldEquiv E E' ] IsExtensionHom (f .fst .fst)

Subextension : ∀ (F : HeytingField ℓ ℓ') (E : FieldExtension F ℓ'' ℓ''') ℓ'''' → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) ℓ''') (ℓ-suc ℓ''''))
Subextension {ℓ'' = ℓ''} F E ℓ'''' = Σ[ L ∈ FieldExtension F ℓ'' ℓ'''' ] ExtensionHom F L E

idExtensionEquiv : ExtensionEquiv F E E
idExtensionEquiv = {!   !}

compExtensionEquiv : ExtensionEquiv F E E' → ExtensionEquiv F E' E'' → ExtensionEquiv F E E''
compExtensionEquiv f g = {!   !}

invExtensionEquiv : ExtensionEquiv F E E' → ExtensionEquiv F E' E
invExtensionEquiv f = {!   !}

ExtensionSym : (F : HeytingField ℓ ℓ') (E : FieldExtension F ℓ'' ℓ''')
             → Type (ℓ-max (ℓ-max ℓ ℓ'') ℓ''')
ExtensionSym F E = ExtensionEquiv F E E

ExtensionSymGroupStr : (F : HeytingField ℓ ℓ') (E : FieldExtension F ℓ'' ℓ''')
                     → GroupStr (ExtensionSym F E)
ExtensionSymGroupStr F E = groupstr idExtensionEquiv compExtensionEquiv invExtensionEquiv {!   !}

ExtensionSymGroup : (F : HeytingField ℓ ℓ') (E : FieldExtension F ℓ'' ℓ''')
                  → Group (ℓ-max (ℓ-max ℓ ℓ'') ℓ''')
ExtensionSymGroup F E = _ , ExtensionSymGroupStr F E

GaloisGroup : (F : HeytingField ℓ ℓ') (E : GaloisExtension F ℓ'' ℓ''')
            → Group (ℓ-max (ℓ-max ℓ ℓ'') ℓ''')
GaloisGroup F E = ExtensionSymGroup F (GaloisExtension→Extension E)

