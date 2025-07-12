{-# OPTIONS --safe #-}
-- Basic properties of polynomials over Heyting fields

module HeytingField.Polynomials.Degree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; separatedℕ; predℕ)
open import Cubical.Data.Nat.Order as ℕOrd hiding (_≤_; _<_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.Ring
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
open import Cubical.Reflection.RecordEquiv

open import HeytingField.Base
open import HeytingField.Properties

private variable
  ℓ ℓ' : Level

-- The type of degrees are the bounded upper naturals; classically equivalent to the natural numbers
-- https://www.davidjaz.com/Talks/MHOTT-myers-slides-II.pdf
-- The definitions in the library are currently insufficiently polymorphic,
-- so we have to reduce the generality a bit for now
Deg≤+ : OrderedCommMonoid (ℓ-suc ℓ-zero) ℓ-zero
Deg≤+ = BoundedPropCompletion ℕ≤+

Deg≤· : OrderedCommMonoid (ℓ-suc ℓ-zero) ℓ-zero
Deg≤· = BoundedPropCompletion ℕ≤·

Deg = ⟨ Deg≤+ ⟩

ℕ→Deg : ℕ → Deg
ℕ→Deg n = n ^↑ , isBounded^ n where open PropCompletion _ ℕ≤+

module Deg where
  open OrderedCommMonoidStr (str Deg≤+) renaming (ε to 0d; _·_ to _+_) public
  open OrderedCommMonoidStr (str Deg≤·) using (_·_) renaming (ε to 1d) public

  degsuc : Deg → Deg
  degsuc d .fst .fst zero = ⊥ , isProp⊥
  degsuc d .fst .fst (suc n) = d .fst .fst n
  degsuc d .fst .snd zero m n≤m ()
  degsuc d .fst .snd (suc n) zero n≤m _ = ¬-<-zero n≤m
  degsuc d .fst .snd (suc n) (suc m) n≤m = d .fst .snd n m (pred-≤-pred n≤m)
  degsuc d .snd = PT.map (λ (m , dm) → suc m , dm) (d .snd)

  _<_ : Deg → Deg → Type
  d₁ < d₂ = degsuc d₁ ≤ d₂

open ℕOrd

-- Later this will be generalized
module FieldPoly (F : HeytingField ℓ-zero ℓ-zero) where
  open FieldTheory F
  open PolyModTheory FCRing
  open PolyMod FCRing using (Poly→Prf; ElimProp; elimProp2; isSetPoly) renaming (Poly→Fun to coefficent)
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
  _hasDeg<_ : Poly FCRing → ℕ → Type
  P hasDeg< n = ∀ m → n ≤ m → coefficent P m ≡ 0r

  _hasDeg≤_ : Poly FCRing → ℕ → Type
  P hasDeg≤ n = P hasDeg< suc n

  isPropHasDeg< : ∀ P n → isProp (P hasDeg< n)
  isPropHasDeg< _ _ = isPropΠ2 λ _ _ → is-set _ _

  isPropHasDeg≤ : ∀ P n → isProp (P hasDeg≤ n)
  isPropHasDeg≤ _ _ = isPropΠ2 λ _ _ → is-set _ _

  hasDeg<≤trans : ∀ P n m → n ≤ m → P hasDeg< n → P hasDeg< m
  hasDeg<≤trans P n m n≤m degP≤n k m≤k = degP≤n k (≤-trans n≤m m≤k)

  hasDeg≤trans : ∀ P n m → n ≤ m → P hasDeg≤ n → P hasDeg≤ m
  hasDeg≤trans P n m n≤m = hasDeg<≤trans P (suc n) (suc m) (suc-≤-suc n≤m)

  hasSomeDeg< : ∀ P → ∃[ n ∈ ℕ ] P hasDeg< n
  hasSomeDeg< = Poly→Prf

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

  deg+ : Poly FCRing → Deg
  deg+ P .fst .fst n .fst = P hasDeg< n
  deg+ P .fst .fst n .snd = isPropHasDeg< P n
  deg+ P .fst .snd = hasDeg<≤trans P
  deg+ P .snd = hasSomeDeg< P

  PolyConst*PresDeg+ : ∀ r P n → P hasDeg< n → (r PolyConst* P) hasDeg< n
  PolyConst*PresDeg+ r P n p m n≤m = coefficentRespConst* r P m ∙∙ congR _·_ (p m n≤m) ∙∙ solve! FCRing

  PolyConst*PresDeg : ∀ r P n → P hasDeg≤ n → (r PolyConst* P) hasDeg≤ n
  PolyConst*PresDeg r P n = PolyConst*PresDeg+ r P (suc n)

  -- Note that this is stronger than ℕ→Deg n ≡ deg P because this definition requires the leading coefficient to
  -- be apart from zero, while ℕ→Deg n ≡ deg P only requires it to not equal zero.
  _hasDeg≡_ : Poly FCRing → ℕ → Type
  P hasDeg≡ n = P hasDeg≤ n × coefficent P n # 0r

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

  ∷sucDeg< : ∀ r P n → P hasDeg< n → (r ∷ P) hasDeg< suc n
  ∷sucDeg< r = λ P n p m (k , k+sn≡m) → lemma P n p k m (sym (ℕ.+-suc k n) ∙ k+sn≡m) where

    lemma : ∀ P n (p : P hasDeg< n) k m → suc k ℕ.+ n ≡ m → coefficent (r ∷ P) m ≡ 0r
    lemma P n p k = J> p _ ≤SumRight

  ∷sucDeg≤ : ∀ r P n → P hasDeg≤ n → (r ∷ P) hasDeg≤ suc n
  ∷sucDeg≤ r P n = ∷sucDeg< r P (suc n)

  ∷sucDeg≡ : ∀ r P n → P hasDeg≡ n → (r ∷ P) hasDeg≡ suc n
  ∷sucDeg≡ r P n (p , q) = ∷sucDeg≤ r P n p , q

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
  
  -- Theorem 5.1 in ACICA
  -- Poly*HasDeg<+ : ∀ P Q → deg (P Poly* Q) ≡ deg P Deg.+ deg Q
  -- Poly*HasDeg<+ = elimProp2 _ {!   !} {!   !} {!   !} {!   !} {!   !}

  -- In a discrete field, every polynomial is either zero (has -1 degree) or has a degree
  module _ (FDisc : isDiscField F) where
    isDisc→≡0⊎hasDeg : ∀ P → (P ≡ 0P) ⊎ hasDeg P
    isDisc→≡0⊎hasDeg = ElimProp _ (inl refl) lemma (goalIsProp _) where

      goalIsProp : ∀ P → isProp ((P ≡ 0P) ⊎ hasDeg P)
      goalIsProp P = isProp⊎ (isSetPoly _ _) (isPropHasDeg P) λ P≡0 → subst (λ P → ¬ hasDeg P) (sym P≡0) []hasNoDeg

      lemma : ∀ r P → (P ≡ 0P) ⊎ hasDeg P → (r ∷ P ≡ 0P) ⊎ hasDeg (r ∷ P)
      lemma r P (inl P≡0) with FDisc r 0r
      ... | yes r#0 = inr λ { .fst → 0; .snd .fst m (k , k+1≡m) →
        cong₂ (λ P m → coefficent (r ∷ P) m) P≡0 (sym k+1≡m ∙ ℕ.+-comm k 1); .snd .snd → r#0}

      ... | no ¬r#0 = inl (cong₂ _∷_ (isTight _ _ ¬r#0) P≡0 ∙ drop0)
      lemma r P (inr (n , p)) = inr (suc n , ∷sucDeg≡ r P n p)

    -- The library doesn't have disjunctive syllogism defined yet
    isDisc→≢0→hasDeg : ∀ P → ¬ P ≡ 0P → hasDeg P
    isDisc→≢0→hasDeg P P≢0 = ⊎-IdL-⊥-Iso .Iso.fun (⊎.map P≢0 (idfun _) (isDisc→≡0⊎hasDeg P))

  isConstant isMonomial isBinomial : Poly FCRing → Type
  isConstant P = P hasDeg≤ 0
  isMonomial P = P hasDeg≤ 1
  isBinomial P = P hasDeg≤ 2