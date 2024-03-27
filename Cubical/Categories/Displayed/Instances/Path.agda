{-
  Paths between objects as a category displayed over C × C.

  If C is univalent, this is equivalent to the IsoComma category.

  Universal property: a section of the Path bundle is a path between
  functors

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Path where

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
open import Cubical.Categories.Displayed.Base.HLevel1Homs
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.Graph
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Preorder hiding (Section; reindex)
open import Cubical.Categories.Displayed.Properties

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

module _  (C : Category ℓC ℓC') where
  private
    module C = Category C
    PathC' : Preorderᴰ (C ×C C) _ _
    PathC' .Preorderᴰ.ob[_] (c , d) = c ≡ d
    PathC' .Preorderᴰ.Hom[_][_,_] (f , g) c≡c' d≡d' =
      PathP (λ i → C.Hom[ c≡c' i , d≡d' i ]) f g
    PathC' .Preorderᴰ.idᴰ = λ i → C.id
    PathC' .Preorderᴰ._⋆ᴰ_ f≡f' g≡g' = λ i → f≡f' i ⋆⟨ C ⟩ g≡g' i
    PathC' .Preorderᴰ.isPropHomᴰ = isOfHLevelPathP' 1 C.isSetHom _ _

  PathC : Categoryᴰ (C ×C C) ℓC ℓC'
  PathC = Preorderᴰ→Catᴰ PathC'

  hasPropHomsPathC : hasPropHoms PathC
  hasPropHomsPathC = hasPropHomsPreorderᴰ PathC'

  open Section
  -- The universal functor into PathC
  Refl : Section (Δ C) PathC
  Refl = mkSectionPropHoms hasPropHomsPathC (λ _ → refl) λ _ → refl

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F1 F2 : Functor D C}
         where
  -- "Equality/Path Reflection Rule"
  SectionPathC→Path :
    ∀ (Fᴰ : Section (F1 ,F F2) (PathC C)) → F1 ≡ F2
  SectionPathC→Path Fᴰ = Functor≡ Fᴰ.F-obᴰ Fᴰ.F-homᴰ
    where module Fᴰ = Section Fᴰ

-- TODO: there should also be a "J"-style elimination principle.
