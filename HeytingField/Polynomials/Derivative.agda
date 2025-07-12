{-# OPTIONS --safe #-}
module HeytingField.Polynomials.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; separatedℕ; predℕ)
open import Cubical.Data.Nat.Order as ℕOrd
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
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
open import HeytingField.Polynomials.Degree

private module Helpers (R : CommRing ℓ-zero) where
  open CommRingStr (str R)
  interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  interchange a b c d = solve! R

module FieldPolyDerivative (F : HeytingField ℓ-zero ℓ-zero) where
  open FieldTheory F
  open PolyModTheory FCRing
  open PolyMod FCRing using (Poly→Prf; ElimProp; elimProp2; module Elim; isSetPoly) renaming (Poly→Fun to coefficent)
  open Elim renaming (f to Elim)
  open Helpers (UnivariatePolyList FCRing)

  -- The symbolic derivative of a polynomial
  diff : Poly FCRing → Poly FCRing
  diff [] = 0P
  -- We know that a ∷ P is a + (X · P), and since a is a constant, its derivative is zero and can be ignored.
  -- so diff (a ∷ P) should be diff (X · P) 
  -- which should be diff X · P + X · diff P by the product rule for differentiation
  -- which reduces to P + 0r ∷ diff P
  diff (a ∷ P) = P Poly+ (0r ∷ diff P)
  diff (drop0 i) = drop0 i

  diff+ : ∀ P Q → diff (P Poly+ Q) ≡ diff P Poly+ diff Q
  diff+ = elimProp2 _ refl (λ r P p → refl) (λ r P p → sym $ Poly+Lid _) (λ r s P Q p →
      {!   !}
    ) (isSetPoly _ _)

