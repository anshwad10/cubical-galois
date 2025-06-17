{-# OPTIONS --allow-unsolved-metas #-}

module IntInitial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Int
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc) hiding (module ℕ)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int

private variable
  ℓ ℓ' : Level

ℤRing : Ring ℓ-zero
ℤRing = CommRing→Ring ℤCommRing

module Initiality (R : Ring ℓ) where
  private module R = RingStr (str R)

  opaque

    ℤ→R : ℤ → ⟨ R ⟩
    ℤ→R (pos zero) = R.0r
    ℤ→R (pos (suc n)) = {!   !}
    ℤ→R (negsuc n) = {!   !}

    ℤ→RIsHom : IsRingHom (str ℤRing) ℤ→R (str R)
    ℤ→RIsHom = {!   !}

    ℤInitialHom : RingHom ℤRing R
    ℤInitialHom = ℤ→R , ℤ→RIsHom