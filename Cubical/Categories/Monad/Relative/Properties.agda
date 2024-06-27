-- Monad relative to a Relator
{-
   Monads as extension systems, i.e., in terms of unit and bind,
   deriving the rest of the structure
   https://ncatlab.org/nlab/show/extension+system
-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Monad.Relative.Properties where

open import Cubical.Foundations.Prelude hiding (J)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Limits.AsRepresentable
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.FunctorComprehension
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.HLevels.More
open import Cubical.Categories.Displayed.Limits.Limits
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Constructions.TotalCategory.More as TotalCat
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Constructions.StructureOver
open import Cubical.Categories.Monad.Relative

open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Foundations.Isomorphism.More

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         (P : Profunctor D C ℓS)
         (E : ExtensionSystem (Profunctor→Relatoro* P))
         where
  private
    J = Profunctor→Relatoro* P
    Algᴰ = AlgebraOver J E
    ALGᴰ = ALGEBRAᴰ J E

  -- ALGEBRAS lift any limit that the profunctor P preserves
  ALGEBRA-liftsLimits : ∀ {ℓS ℓS'}{S : Category ℓS ℓS'}
    {ds : Functor S D}
    → {lim⟨ds⟩ : limit ds}
    → preservesLimit P lim⟨ds⟩
    → liftsLimit ALGᴰ lim⟨ds⟩
  ALGEBRA-liftsLimits P⟨lim⟨ds⟩⟩≡lim⟨P⟅ds⟆⟩ alg⟨ds⟩ = record
    { vertexᴰ = {!!}
    ; elementᴰ = {!!}
    ; universalᴰ = {!!}
    }
  -- ALGEBRA-liftsLimits : ∀ ℓS ℓS' → liftsLimits (ALGEBRAᴰ J E) ℓS ℓS'
  -- ALGEBRA-liftsLimits _ _ S limitOfS {D = F} Fᴰ = record
  --   { vertexᴰ    = LimAlg
  --   ; elementᴰ   = {!!}
  --   ; universalᴰ = {!!}
  --   } where
  --   module J = Bifunctor J
  --   module D = Category D
  --   module E = ExtensionSystem E
  --   module Lim = UniversalElementNotation (limitOfS F)
  --   open AlgebraOver
  --   open Functorᴰ
  --   open NatTrans
  --   LimAlg : Algᴰ Lim.vertex
  --   LimAlg .bindA j = Lim.intro (natTrans
  --     (((λ s → Fᴰ .F-obᴰ {x = s} _ .bindA ((J ⟪ Lim.element ⟦ s ⟧ ⟫r) j))) )
  --     λ f →
  --             D.⋆IdL _
  --             ∙ cong (Fᴰ .F-obᴰ _ .bindA)
  --               ( cong₂ (J.Bif-homR _)
  --                       (sym (D.⋆IdL _) ∙ Lim.element .N-hom f)
  --                       refl
  --               ∙ funExt⁻ (J.Bif-R-seq _ _) _)
  --             ∙ sym (Fᴰ .F-homᴰ {f = f} _ _)
  --     )
  --   -- Whoops! Need that J preserves limits in the rhs
  --   -- ⟨ (π_s ∘ r)^t ⟩_s o η
  --   -- = ⟨ (π_s o r)^t o η ⟩_s
  --   -- = ⟨ π_s o r ⟩_s
  --   -- = r

  --   LimAlg .bindA-l = {!!}
  --   LimAlg .bindA-comp = {!!}
