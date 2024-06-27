{-

  The category of elements of a presheaf is naturally formulated as a
  total category of a displayed category.

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Sets.Elements where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.StructureOver

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓP : Level

module _ (ℓ : Level) where
  Element : Categoryᴰ (SET ℓ) ℓ ℓ
  Element = StructureOver→Catᴰ S where
    open StructureOver
    S : StructureOver _ _ _
    S .ob[_] X = ⟨ X ⟩
    S .Hom[_][_,_] f x y = f x ≡ y
    S .idᴰ = refl
    S ._⋆ᴰ_ {g = g} fx≡y gy≡z = cong g fx≡y ∙ gy≡z
    S .isPropHomᴰ {y = Y} = Y .snd _ _
