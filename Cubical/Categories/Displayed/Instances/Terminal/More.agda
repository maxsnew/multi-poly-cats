{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Terminal.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Terminal
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.PropertyOver as PO

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ
open Section
open Functorᴰ

module _ {C : Category ℓC ℓC'} where
  hasContrHomsUnitᴰ : hasContrHoms (Unitᴰ C)
  hasContrHomsUnitᴰ = hasContrHomsPropertyOver C _

  ttS : GlobalSection (Unitᴰ C)
  ttS .F-obᴰ  = λ _ → tt
  ttS .F-homᴰ = λ _ → tt
  ttS .F-idᴰ  = refl
  ttS .F-seqᴰ _ _ = refl

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         {F : Functor C D}
         where
  recᴰ : (s : Section F Dᴰ) → Functorᴰ F (Unitᴰ C) Dᴰ
  recᴰ s .F-obᴰ {x} _      = s .F-obᴰ x
  recᴰ s .F-homᴰ {f = f} _ = s .F-homᴰ f
  recᴰ s .F-idᴰ      = s .F-idᴰ
  recᴰ s .F-seqᴰ _ _ = s .F-seqᴰ _ _

