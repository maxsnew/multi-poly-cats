{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.TotalCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
-- open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Constructions.TotalCategory
  as TotalCat
  hiding (intro)

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

-- Projection out of the displayed total category
module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
  where

  open Functor
  open Functorᴰ
  open Section
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
    ∫∫Cᴰ = ∫C {C = C} (∫Cᴰ Cᴰ Dᴰ)
    -- module R = HomᴰReasoning (∫Cᴰ Cᴰ Dᴰ)

  Assocᴰ : Functor ∫∫Cᴰ (∫C Dᴰ)
  Assocᴰ .F-ob  x   = (x .fst , x .snd .fst) , x .snd .snd
  Assocᴰ .F-hom f   = (f .fst , f .snd .fst) , f .snd .snd
  Assocᴰ .F-id      = refl
  Assocᴰ .F-seq _ _ = refl

  Assocᴰ⁻ : Functor (∫C Dᴰ) ∫∫Cᴰ
  Assocᴰ⁻ .F-ob  x   = x .fst .fst , x .fst .snd , x .snd
  Assocᴰ⁻ .F-hom f   = f .fst .fst , f .fst .snd , f .snd
  Assocᴰ⁻ .F-id      = refl
  Assocᴰ⁻ .F-seq _ _ = refl

  Fstᴰ : Functorᴰ Id (∫Cᴰ Cᴰ Dᴰ) Cᴰ
  Fstᴰ .F-obᴰ = fst
  Fstᴰ .F-homᴰ = fst
  Fstᴰ .F-idᴰ = refl
  Fstᴰ .F-seqᴰ _ _ = refl

  -- Functor into the displayed total category
  module _ {E : Category ℓE ℓE'} (F : Functor E C)
           (Fᴰ : Section F Cᴰ)
           (Gᴰ : Section (TotalCat.intro F Fᴰ) Dᴰ)
           where
    intro : Section F (∫Cᴰ Cᴰ Dᴰ)
    intro .F-obᴰ  d   = Fᴰ .F-obᴰ d , Gᴰ .F-obᴰ d
    intro .F-homᴰ f   = Fᴰ .F-homᴰ f , Gᴰ .F-homᴰ f
    intro .F-idᴰ      = ΣPathP (Fᴰ .F-idᴰ , Gᴰ .F-idᴰ)
    intro .F-seqᴰ f g = ΣPathP (Fᴰ .F-seqᴰ f g , Gᴰ .F-seqᴰ f g)
