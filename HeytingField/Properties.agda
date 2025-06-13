{-# OPTIONS --safe #-}

module HeytingField.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset using (ℙ; _∈_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary

open import Cubical.Data.Sigma

open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing

open import HeytingField.Base

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  F G H : HeytingField ℓ ℓ'

module FieldTheory ((R , F) : HeytingField ℓ ℓ') where
  open HeytingFieldStr F public
  FCRing = HeytingField→CommRing (R , F)

  private variable
    x y : R

  FieldIsSeparated : Separated R
  FieldIsSeparated x y ¬¬x≡y = isTight x y λ x#y → ¬¬x≡y λ x≡y → is-irrefl y $ subst (_# y) x≡y x#y

  contrapos#→≡ : ∀ x y z w → (x # y → z # w) → z ≡ w → x ≡ y
  contrapos#→≡ x y z w x#y→z#w z≡w = isTight x y λ x#y → is-irrefl w $ subst (_# w) z≡w (x#y→z#w x#y)

  +Respect#ₗ : ∀ x y z → x # y → (z + x) # (z + y)
  +Respect#ₗ x y z x#y = subst2 _#_ (+Comm _ _) (+Comm _ _) (+Respect#ᵣ x y z x#y)

  -- x # y is the same as invertibility of x - y
  -- However, in the definition I chose to let the user give a custom implementation of # for two reasons:
  -- It's sometimes more convenient, for example in an ordered field where we can define x # y to be x < y or y < x
  -- I also allow it to have a smaller universe level, which is useful when implementing e.g. the Dedekind reals predicatively
  #→DiffIsInv : ∀ x y → x # y → (x - y) ∈ FCRing ˣ
  #→DiffIsInv x y x#y = #0→IsInv (x - y) (subst (_ #_) (+InvR y) (+Respect#ᵣ x y (- y) x#y))

  DiffIsInv→# : ∀ x y → (x - y) ∈ FCRing ˣ → x # y
  DiffIsInv→# x y (x-y⁻¹ , p) = subst2 _#_ (solve! FCRing) (+IdL y) (+Respect#ᵣ _ _ y (IsInv→#0 _ x-y⁻¹ p))

  ·Respect#ᵣ : ∀ x y z → z # 0r → x # y → (x · z) # (y · z)
  ·Respect#ᵣ x y z z#0 x#y = DiffIsInv→# _ _ $ subst (_∈ (FCRing ˣ)) (solve! FCRing) $
    Units.RˣMultClosed FCRing _ _ ⦃ #→DiffIsInv _ _ x#y ⦄ ⦃ #0→IsInv _ z#0 ⦄

  ·Respect#ₗ : ∀ x y z → z # 0r → x # y → (z · x) # (z · y)
  ·Respect#ₗ x y z z#0 x#y = subst2 _#_ (·Comm _ _) (·Comm _ _) (·Respect#ᵣ x y z z#0 x#y)

  +Cancel#ᵣ : ∀ x y z → (x + z) # (y + z) → x # y
  +Cancel#ᵣ x y z x+z#y+z = subst2 _#_ (solve! FCRing) (solve! FCRing) (+Respect#ᵣ _ _ (- z) x+z#y+z)

  +Cancel#ₗ : ∀ x y z → (z + x) # (z + y) → x # y
  +Cancel#ₗ x y z z+x#z+y = +Cancel#ᵣ x y z (subst2 _#_ (+Comm _ _) (+Comm _ _) z+x#z+y)

  recipRespect# : ∀ z (z#0 : z # 0r) → recip z z#0 # 0r
  recipRespect# z z#0 = IsInv→#0 _ z (isLInvRecip z z#0)

  ·Cancel#ᵣ : ∀ x y z → z # 0r → (x · z) # (y · z) → x # y
  ·Cancel#ᵣ x y z z#0 xz#yz = subst2 _#_ (lem x) (lem y) (·Respect#ᵣ _ _ (recip z z#0) (recipRespect# z z#0) xz#yz)
    where lem = λ (a : R) → sym (·Assoc a z (recip z z#0)) ∙∙ congR _·_ (isRInvRecip z z#0) ∙∙ ·IdR a
  
  ·Cancel#ₗ : ∀ x y z → z # 0r → (z · x) # (z · y) → x # y
  ·Cancel#ₗ x y z z#0 zx#zy = ·Cancel#ᵣ x y z z#0 (subst2 _#_ (·Comm _ _) (·Comm _ _) zx#zy)

  ·Cancelᵣ : ∀ x y z → z # 0r → x · z ≡ y · z → x ≡ y
  ·Cancelᵣ x y z z#0 = contrapos#→≡ _ _ _ _ (·Respect#ᵣ x y z z#0)

  ·Cancelₗ : ∀ x y z → z # 0r → z · x ≡ z · y → x ≡ y
  ·Cancelₗ x y z z#0 = contrapos#→≡ _ _ _ _ (·Respect#ₗ x y z z#0)

-- Any homomorphism of rings automatically preserves the apartness
module _ ((A , F) : HeytingField ℓ ℓ'') ((B , G) : HeytingField ℓ' ℓ''')
         (f : A → B) (fIsRingHom : IsRingHom (HeytingFieldStr→RingStr F) f (HeytingFieldStr→RingStr G)) where
  private
    module F = FieldTheory (A , F)
    module G = FieldTheory (B , G)

  FieldHomPres# : ∀ x y → x F.# y → f x G.# f y
  FieldHomPres# x y x#y = let (x-y⁻¹ , p) = F.#→DiffIsInv _ _ x#y in G.DiffIsInv→# _ _ $ 
    f x-y⁻¹ , sym (pres· _ _ ∙∙ congL G._·_ (pres+ _ _) ∙∙ congL G._·_ (congR G._+_ (pres- _))) ∙∙ cong f p ∙∙ pres1
    where open IsRingHom fIsRingHom

  FieldHomIsInj : ∀ x y → f x ≡ f y → x ≡ y
  FieldHomIsInj x y fx≡fy = F.isTight _ _ λ x#y → G.is-irrefl (f y) (subst (G._# (f y)) fx≡fy (FieldHomPres# x y x#y))

  module _ (strongExt : ∀ x y → f x G.# f y → x F.# y) where

    open IsHeytingFieldHom
    open IsRingHom

    strongExtRingHomIsFieldHom : IsHeytingFieldHom F f G
    strongExtRingHomIsFieldHom = λ where
      .pres0 → fIsRingHom .pres0
      .pres1 → fIsRingHom .pres1
      .pres+ → fIsRingHom .pres+
      .pres· → fIsRingHom .pres·
      .pres- → fIsRingHom .pres-
      .pres# x y → propBiimpl→Equiv (F.is-prop-valued _ _) (G.is-prop-valued _ _) (FieldHomPres# x y) (strongExt x y)

-- We can make a smart constructor for field homomorphisms, as they are just strongly extensional ring homomorphisms
module _ {A : Type ℓ} {B : Type ℓ'} {F : HeytingFieldStr ℓ'' A} {G : HeytingFieldStr ℓ''' B} {f : A → B} where
  private
    module F = FieldTheory (A , F)
    module G = FieldTheory (B , G)
  
  module _ (pres+ : ∀ x y → f (x F.+ y) ≡ f x G.+ f y) (pres1 : f F.1r ≡ G.1r)
           (pres· : ∀ x y → f (x F.· y) ≡ f x G.· f y) (strongExt : ∀ x y → f x G.# f y → x F.# y) where
    
    makeIsFieldHom : IsHeytingFieldHom F f G
    makeIsFieldHom = strongExtRingHomIsFieldHom _ _ f (makeIsRingHom pres1 pres+ pres·) strongExt

module _ {F : HeytingField ℓ ℓ''} {G : HeytingField ℓ' ℓ'''} (f : ⟨ F ⟩ → ⟨ G ⟩) where
  private
    module F = FieldTheory F
    module G = FieldTheory G
  
  module _ (pres+ : ∀ x y → f (x F.+ y) ≡ f x G.+ f y) (pres1 : f F.1r ≡ G.1r)
           (pres· : ∀ x y → f (x F.· y) ≡ f x G.· f y) (strongExt : ∀ x y → f x G.# f y → x F.# y) where
    
    makeFieldHom : HeytingFieldHom F G
    makeFieldHom = f , makeIsFieldHom pres+ pres1 pres· strongExt

-- Although not every ring homomorphism is a field homomorphism, every ring equivalence is an equivalence of fields:
module _ {A : Type ℓ} {B : Type ℓ'} {F : HeytingFieldStr ℓ'' A} (e : A ≃ B) {G : HeytingFieldStr ℓ''' B}
         (eIsRingEquiv : IsRingEquiv (HeytingFieldStr→RingStr F) e (HeytingFieldStr→RingStr G)) where
  private
    module F = FieldTheory (A , F)
    module G = FieldTheory (B , G)

  ringEquivIsStrongExt : ∀ x y → e .fst x G.# e .fst y → x F.# y
  ringEquivIsStrongExt x y ex#ey = subst2 F._#_ (retEq e x) (retEq e y) $
    FieldHomPres# (B , G) (A , F) (invEq e) (isRingHomInv (e , eIsRingEquiv)) _ _ ex#ey
    where open RingEquivs
  
  ringEquivIsFieldEquiv : IsHeytingFieldEquiv F e G
  ringEquivIsFieldEquiv = strongExtRingHomIsFieldHom _ _ _ eIsRingEquiv ringEquivIsStrongExt

module _ {F : HeytingField ℓ ℓ''} {G : HeytingField ℓ' ℓ'''} where
  RingEquiv→FieldEquiv : RingEquiv (HeytingField→Ring F) (HeytingField→Ring G) → HeytingFieldEquiv F G
  RingEquiv→FieldEquiv (e , eIsHom) = e , ringEquivIsFieldEquiv e eIsHom

  FieldEquiv≃RingEquiv : HeytingFieldEquiv F G ≃ RingEquiv (HeytingField→Ring F) (HeytingField→Ring G)
  FieldEquiv≃RingEquiv = Σ-cong-equiv-snd λ e → 
    propBiimpl→Equiv (isPropIsHeytingFieldHom _ _ _) (isPropIsRingHom _ _ _)
                     (isHeytingFieldHom→isRingHom _ _ _) (ringEquivIsFieldEquiv e)

  isEquivHeytingFieldEquiv→RingEquiv : isEquiv (HeytingFieldEquiv→RingEquiv F G)
  isEquivHeytingFieldEquiv→RingEquiv = FieldEquiv≃RingEquiv .snd

open RingHoms
open IsHeytingFieldHom

idFieldHom : HeytingFieldHom F F
idFieldHom = _ , strongExtRingHomIsFieldHom _ _ _ (idRingHom _ .snd) λ _ _ → idfun _

compFieldHom : HeytingFieldHom F G → HeytingFieldHom G H → HeytingFieldHom F H
compFieldHom f g = _ , strongExtRingHomIsFieldHom _ _ _ 
  (compIsRingHom (HeytingFieldHom→RingHom _ _ g .snd) (HeytingFieldHom→RingHom _ _ f .snd)) λ x y x#y →
    invEq (f .snd .pres# _ _) (invEq (g .snd .pres# _ _) x#y)

Subfield : ∀ (F : HeytingField ℓ ℓ'') ℓ' → Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓ'')) (ℓ-suc ℓ'))
Subfield {ℓ'' = ℓ''} F ℓ' = Σ[ H ∈ HeytingField ℓ' ℓ'' ] HeytingFieldHom H F