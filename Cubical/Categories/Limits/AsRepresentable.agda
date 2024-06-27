{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.AsRepresentable where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Bifunctor as Bif
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Morphism
open import Cubical.Categories.Adjoint.UniversalElements

open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Tactics.FunctorSolver.Reflection

private
  variable
    ℓj ℓj' ℓc ℓc' ℓd ℓd' : Level

ΔF : {C : Category ℓc ℓc'}{J : Category ℓj ℓj'}
   → Functor C (FUNCTOR J C)
ΔF = λFR Bif.Fst

CONE : (C : Category ℓc ℓc')(J : Category ℓj ℓj')
     → Profunctor (FUNCTOR J C) C (ℓ-max (ℓ-max ℓc' ℓj) ℓj')
CONE C J = RightAdjointProf (ΔF {C = C} {J = J})

limit : {C : Category ℓc ℓc'}{J : Category ℓj ℓj'}
        (D : Functor J C)
      → Type _
limit {C = C}{J = J} = RightAdjointAt ΔF

limitsOfShape : (C : Category ℓc ℓc') (J : Category ℓj ℓj')
              → Type _
limitsOfShape C J = RightAdjoint {C = C} {D = (FUNCTOR J C)} ΔF

-- Limit preservation
module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
         (F : Functor C D)
       where
  -- the simplest one is to preserve a *particular* limit, meaning the
  -- limit cone is mapped to a limiting cone.
  module _ {J : Category ℓj ℓj'} where
    open Functor
    open NatTrans
    open UniversalElement
    pushCone : ∀ (cⱼ : Functor J C)
      → PshHom F (CONE C J ⟅ cⱼ ⟆) (CONE D J ⟅ F ∘F cⱼ ⟆)
    pushCone cⱼ .N-ob c' (lift α) .lower .N-ob = (F ∘ʳ α) .N-ob
    pushCone cⱼ .N-ob c' (lift α) .lower .N-hom f =
      cong₂ (seq' D) (sym (F .F-id)) refl
      ∙ (F ∘ʳ α) .N-hom f
    pushCone cⱼ .N-hom f = funExt (λ (lift α) →
      cong lift (makeNatTransPath (funExt (λ j → F .F-seq _ _))))

    preservesLimit : ∀ {cⱼ : Functor J C}
      → (lim : UniversalElement C (CONE C J ⟅ cⱼ ⟆))
      → Type _
    preservesLimit {cⱼ} =
      preservesRepresentation F (CONE C J ⟅ cⱼ ⟆) (CONE D J ⟅ F ∘F cⱼ ⟆)
        (pushCone cⱼ)

    -- todo: preservesLimitsOfShape, preservesLimits

-- TODO: All functors preserve cones
--       Functors with left adjoints preserve limiting cones
