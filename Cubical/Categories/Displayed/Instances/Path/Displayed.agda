{-
  Paths between objects as a category displayed over C × C.

  If C is univalent, this is equivalent to the IsoComma category.

  Universal property: a section of the Path bundle is a path between
  functors

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Path.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.Relator as Relator hiding (Hom)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Base.HLevel1Homs
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.Graph
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Preorder hiding (Section; reindex)
open import Cubical.Categories.Displayed.Properties

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

module _  {C : Category ℓC ℓC'}
          (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
          where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    open Preorderᴰ
    PathCᴰ' : Preorderᴰ (∫C {C = C} (Cᴰ ×ᴰ Cᴰ)) _ _
    PathCᴰ' .ob[_] (c , cᴰ , cᴰ') = cᴰ ≡ cᴰ'
    PathCᴰ' .Hom[_][_,_] (f , fᴰ , fᴰ') p q =
      PathP (λ i → Cᴰ.Hom[ f ][ p i , q i ]) fᴰ fᴰ'
    PathCᴰ' .idᴰ i = Cᴰ.idᴰ
    PathCᴰ' ._⋆ᴰ_ fᴰ≡fᴰ' gᴰ≡gᴰ' i = fᴰ≡fᴰ' i Cᴰ.⋆ᴰ gᴰ≡gᴰ' i
    PathCᴰ' .isPropHomᴰ = isOfHLevelPathP' 1 Cᴰ.isSetHomᴰ _ _
  open Categoryᴰ
  PathCᴰ : Categoryᴰ (∫C {C = C} (Cᴰ ×ᴰ Cᴰ)) _ _
  PathCᴰ = Preorderᴰ→Catᴰ PathCᴰ'

  hashPropHomsPathCᴰ : hasPropHoms PathCᴰ
  hashPropHomsPathCᴰ = hasPropHomsPreorderᴰ PathCᴰ'

  open Section
  Refl : Section (∫F {C = C} (Δᴰ Cᴰ)) PathCᴰ
  Refl .F-obᴰ (c , cᴰ) = refl
  Refl .F-homᴰ (f , fᴰ) = refl
  Refl .F-idᴰ = refl
  Refl .F-seqᴰ _ _ = refl

-- TODO: "Path Reflection Rule" that constructs a Path between
-- sections from a section of PathCᴰ

