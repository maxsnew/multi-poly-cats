-- | Full subcategories (not necessarily prop) viewed as displayed categories.
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.FullSubcategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding

open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Preorder
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Base.HLevel1Homs
open import Cubical.Categories.Yoneda

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓS ℓR : Level

open Category
open Functor
open Categoryᴰ
open Functorᴰ

module _ (C : Category ℓC ℓC') (P : Category.ob C → Type ℓP) where
  private
    module C = Category C
  open Category
  open Functor

  FullSubcategoryᴰ : Categoryᴰ C ℓP ℓ-zero
  FullSubcategoryᴰ = Preorderᴰ→Catᴰ FSP where
    open Preorderᴰ
    FSP : Preorderᴰ C ℓP ℓ-zero
    FSP .ob[_] = P
    FSP .Hom[_][_,_] _ _ _ = Unit
    FSP .idᴰ = tt
    FSP ._⋆ᴰ_ = λ _ _ → tt
    FSP .isPropHomᴰ = isPropUnit

  hasContrHomsFullSubcategory : hasContrHoms FullSubcategoryᴰ
  hasContrHomsFullSubcategory _ _ _ = isContrUnit

  hasPropHomsFullSubcategory : hasPropHoms FullSubcategoryᴰ
  hasPropHomsFullSubcategory _ _ _ = isPropUnit

  module _ {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
           (F : Functor D C)
           (F-obᴰ : {x : D .ob} →
             Dᴰ .ob[_] x → ob[ FullSubcategoryᴰ ] (F .F-ob x))
           where
    mkFullSubcategoryᴰFunctorᴰ : Functorᴰ F Dᴰ FullSubcategoryᴰ
    mkFullSubcategoryᴰFunctorᴰ =
      mkFunctorᴰContrHoms hasContrHomsFullSubcategory F-obᴰ
