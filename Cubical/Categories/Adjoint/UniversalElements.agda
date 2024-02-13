{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.Adjoint.UniversalElements where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.FunctorComprehension
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Yoneda

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category

-- A right adjoint to F : C → D
-- is specified by a functor RAdj F : D → 𝓟 C
--   RAdj F d c := D [ F c , d ]
module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (F : Functor C D)
         where
  RightAdjointProf : Functor D (PresheafCategory C ℓD')
  RightAdjointProf = precomposeF (SET _) (F ^opF) ∘F YO


  RightAdjointAt : (d : D .ob) → Type _
  RightAdjointAt d = UniversalElement C (RightAdjointProf ⟅ d ⟆)

  RightAdjoint : Type _
  RightAdjoint = UniversalElements RightAdjointProf


module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (F : Functor C D)
         where
  LeftAdjoint : Type _
  LeftAdjoint = RightAdjoint (F ^opF)

  LeftAdjointAt : (d : D .ob) → Type _
  LeftAdjointAt = RightAdjointAt (F ^opF)

-- Uh Oh
RightAdjointAt' : (C : Category ℓC ℓC')
                  (D : Category ℓD ℓD')
                  (F : Functor C D) (d : D .ob)
                → Type _
RightAdjointAt' C D F d  =
  UniversalElement C ((D [-, d ]) ∘F (F ^opF))

RightAdjointAt→Prime : (C : Category ℓC ℓC')
                 (D : Category ℓD ℓD')
                 (F : Functor C D)
                 (d : D .ob)
                 → RightAdjointAt F d → RightAdjointAt' C D F d
RightAdjointAt→Prime C D F d x .UniversalElement.vertex =
  UniversalElement.vertex x
RightAdjointAt→Prime C D F d x .UniversalElement.element =
  UniversalElement.element x
RightAdjointAt→Prime C D F d x .UniversalElement.universal =
  UniversalElement.universal x

RightAdjoint' : (C : Category ℓC ℓC')
                (D : Category ℓD ℓD')
                (F : Functor C D)
              → Type _
RightAdjoint' C D F = ∀ d → RightAdjointAt' C D F d

IdRightAdj' : (C : Category ℓC ℓC')
      → RightAdjoint' C C Id
IdRightAdj' C c .UniversalElement.vertex = c
IdRightAdj' C c .UniversalElement.element = id C
IdRightAdj' C c .UniversalElement.universal c' =
  isoToIsEquiv (iso _ (λ z → z) (C .⋆IdR) (C .⋆IdR))

