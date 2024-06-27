{-

  The category of elements of a presheaf is naturally formulated as a
  total category of a displayed category.

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.PresheafElements where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Presheaf hiding (Elements)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Instances.Sets.Elements
  renaming (Element to SetElement)

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓP : Level

module _ {C : Category ℓC ℓC'}
         (P : Presheaf C ℓP) where
  Elemento : Categoryᴰ C ℓP ℓP
  Elemento = reindex (SetElement _) P ^opᴰ

module _ {C : Category ℓC ℓC'}
         (P : Functor C (SET ℓP)) where
  Element* : Categoryᴰ C ℓP ℓP
  Element* = reindex (SetElement _) P
