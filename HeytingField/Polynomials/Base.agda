-- Basic properties of polynomials over Heyting fields

module HeytingField.Polynomials.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; separatedℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties
open import Cubical.Algebra.Polynomials.UnivariateList.UniversalProperty
open import Cubical.Algebra.OrderedCommMonoid
open import Cubical.Algebra.OrderedCommMonoid.Instances
open import Cubical.Algebra.OrderedCommMonoid.PropCompletion
open import Cubical.Relation.Nullary
open import Cubical.Tactics.CommRingSolver

open import HeytingField.Base
open import HeytingField.Properties

private variable
  ℓ ℓ' : Level

-- The type of degrees are the bounded upper naturals; classically equivalent to the natural numbers
-- The definitions in the library are currently insufficiently polymorphic,
-- so we have to reduce the generality a bit for now
Deg≤+ : OrderedCommMonoid (ℓ-suc ℓ-zero) ℓ-zero
Deg≤+ = BoundedPropCompletion ℕ≤+

Deg = ⟨ Deg≤+ ⟩
module Deg where open OrderedCommMonoidStr (str Deg≤+) renaming (_·_ to _+_) public

ℕ→Deg : ℕ → Deg
ℕ→Deg n = n ^↑ , isBounded^ n where open PropCompletion _ ℕ≤+

-- Later this will be generalized
module FieldPoly (F : HeytingField ℓ-zero ℓ-zero) where
  open FieldTheory F
  open PolyModTheory FCRing
  open PolyMod FCRing using (Poly→Prf; ElimProp) renaming (Poly→Fun to coefficent) 
  private
    FAlgebra = initialCAlg FCRing
    PAlgebra = ListPolyCommAlgebra FCRing
  
  private variable
    P Q R : Poly FCRing
    m : ℕ

  -- We define this using 
  evaluateAlgebraHom : ⟨ F ⟩ → CommAlgebraHom PAlgebra FAlgebra
  evaluateAlgebraHom = inducedHom FCRing _

  evaluate _$p_ : Poly FCRing → ⟨ F ⟩ → ⟨ F ⟩
  evaluate P x = evaluateAlgebraHom x .fst P
  _$p_ = evaluate

  evaluate+ : ∀ P Q x → (P Poly+ Q) $p x ≡ (P $p x) + (Q $p x)
  evaluate+ P Q x = evaluateAlgebraHom x .snd .IsAlgebraHom.pres+ P Q

  evaluate1 : ∀ x → 1P $p x ≡ 1r
  evaluate1 x = evaluateAlgebraHom x .snd .IsAlgebraHom.pres1

  evaluate· : ∀ P Q x → (P Poly* Q) $p x ≡ (P $p x) · (Q $p x)
  evaluate· P Q x = evaluateAlgebraHom x .snd .IsAlgebraHom.pres· P Q

  isRoot : ∀ P x → Type
  isRoot P x = P $p x ≡ 0r

  coefficentRespConst* : ∀ r P n → coefficent (r PolyConst* P) n ≡ r · coefficent P n
  coefficentRespConst* r = ElimProp _ (λ _ → solve! FCRing) (λ where
      a P rec zero → refl
      a P rec (suc n) → rec n
    ) (isPropΠ λ _ → is-set _ _)

  -- These definitions are from 'A Course in Constructive Algebra'
  _hasDeg≤_ : Poly FCRing → ℕ → Type
  P hasDeg≤ n = ∀ m → n < m → coefficent P m ≡ 0r

  isPropHasDeg≤ : ∀ P n → isProp (P hasDeg≤ n)
  isPropHasDeg≤ _ _ = isPropΠ2 λ _ _ → is-set _ _

  hasDeg≤trans : ∀ P n m → n ≤ m → P hasDeg≤ n → P hasDeg≤ m
  hasDeg≤trans P n m n≤m degP≤n k m<k = degP≤n k (≤<-trans n≤m m<k)

  hasSomeDeg≤ : ∀ P → ∃[ n ∈ ℕ ] P hasDeg≤ n
  hasSomeDeg≤ P = PT.map (λ where  
      (zero , p) → zero , λ m _ → p m zero-≤
      (suc n , p) → n , p
    ) (Poly→Prf P)

  -- The above is exactly the data we need to define:
  deg : Poly FCRing → Deg
  deg P .fst .fst n .fst = P hasDeg≤ n
  deg P .fst .fst n .snd = isPropHasDeg≤ P n
  deg P .fst .snd = hasDeg≤trans P
  deg P .snd = hasSomeDeg≤ P

  PolyConst*PresDeg : ∀ r P n → P hasDeg≤ n → (r PolyConst* P) hasDeg≤ n
  PolyConst*PresDeg r P n p m n<m = coefficentRespConst* r P m ∙∙ congR _·_ (p m n<m) ∙∙ solve! FCRing

  -- Note that this is stronger than ℕ→Deg n Deg.≤ deg P because this requires the leading coefficient to
  -- be apart from zero, while the other definition only requires it to not equal zero.
  _hasDeg≥_ : Poly FCRing → ℕ → Type
  P hasDeg≥ n = coefficent P n # 0r

  -- This is also stronger than ℕ→Deg n ≡ deg P for similar reasons
  _hasDeg≡_ : Poly FCRing → ℕ → Type
  P hasDeg≡ n = P hasDeg≤ n × P hasDeg≥ n

  isPropHasDeg≡ : ∀ P n → isProp (P hasDeg≡ n)
  isPropHasDeg≡ P n = isProp× (isPropHasDeg≤ P n) (is-prop-valued _ _)

  hasDeg : Poly FCRing → Type
  hasDeg P = Σ[ n ∈ ℕ ] P hasDeg≡ n

  -- Every polynomial has at most one degree
  -- in other words, the degree can be considered a partial function from polynomials to naturals
  isPropHasDeg : ∀ P → isProp (hasDeg P)
  isPropHasDeg P (n , p) (m , q) = Σ≡Prop (isPropHasDeg≡ P) $ separatedℕ n m (lemma (n ≟ m))
    where
      lemma : Trichotomy n m → ¬ ¬ n ≡ m
      lemma (lt n<m) _ = #→≢ _ _ (q .snd) (p .fst m n<m)
      lemma (eq n≡m) n≢m = n≢m n≡m
      lemma (gt n>m) _ = #→≢ _ _ (p .snd) (q .fst n n>m)
  
  []hasNoDeg : ¬ hasDeg []
  []hasNoDeg (_ , _ , p) = is-irrefl 0r p
  
  leadingCoeff : ∀ P → hasDeg P → ⟨ F ⟩
  leadingCoeff P (n , p) = coefficent P n

  leadingCoeff#0 : ∀ P p → leadingCoeff P p # 0r
  leadingCoeff#0 P (n , p) = p .snd

  -- A polymonial is monic if it has a leading coefficent that is 1
  _isMonicWithDeg≡_ : Poly FCRing → ℕ → Type
  P isMonicWithDeg≡ n = P hasDeg≤ n × (coefficent P n ≡ 1r)

  isPropIsMonicWithDeg : ∀ P n → isProp (P isMonicWithDeg≡ n)
  isPropIsMonicWithDeg P n = isProp× (isPropHasDeg≤ P n) (is-set _ _)

  isMonic : Poly FCRing → Type
  isMonic P = Σ[ n ∈ ℕ ] P isMonicWithDeg≡ n

  isMonicWithDeg→hasDeg : ∀ P n → P isMonicWithDeg≡ n → P hasDeg≡ n
  isMonicWithDeg→hasDeg P n = map-snd λ c≡1 → subst (_# 0r) (sym c≡1) FieldIsNonTrivial

  isMonic→hasDeg : ∀ P → isMonic P → hasDeg P
  isMonic→hasDeg P = map-snd λ {a = n} → isMonicWithDeg→hasDeg P n

  isPropIsMonic : ∀ P → isProp (isMonic P)
  isPropIsMonic P p q = Σ≡Prop (isPropIsMonicWithDeg P) $
    cong fst $ isPropHasDeg P (isMonic→hasDeg P p) (isMonic→hasDeg P q)

  hasDeg→factorMonic : ∀ P → hasDeg P → Σ[ a ∈ ⟨ F ⟩ ] isMonic (a PolyConst* P)
  hasDeg→factorMonic P (n , p) =
    recip _ (p .snd) , n , PolyConst*PresDeg _ P n (p .fst) , coefficentRespConst* _ P n ∙ isLInvRecip _ (p .snd)

  module Division (f g : Poly FCRing) where