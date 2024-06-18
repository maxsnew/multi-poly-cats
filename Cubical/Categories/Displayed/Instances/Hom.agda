{-
  The Hom profunctor viewed as a 2-sided discrete fibration.

  This is just an instance of Constructions.Graph but it's common
  enough to be given its own module.

  https://ncatlab.org/nlab/show/two-sided+fibration#twosided_discrete_fibrations
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Hom where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Profunctor.Relator as Relator
open import Cubical.Categories.Profunctor.Hom as Relator hiding (Hom)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.HLevels.More
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.Graph
open import Cubical.Categories.Displayed.Constructions.TotalCategory
  as TotalCatᴰ
open import Cubical.Categories.Displayed.Constructions.PropertyOver

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

module _ (C : Category ℓC ℓC') where
  Hom : Categoryᴰ (C ×C C) ℓC' ℓC'
  Hom = Graph {C = C}{D = C} (Relator.Hom C)

  hasPropHomsHom = hasPropHomsGraph (Relator.Hom C)

  Mono : Categoryᴰ (C ×C C) (ℓ-max ℓC' (ℓ-max ℓC ℓC')) (ℓ-max ℓC' ℓ-zero)
  Mono = ∫Cᴰ Hom (PropertyOver _ (λ (_ , f) → isMonic C f))

module _ {C : Category ℓC ℓC'} where
  private
    module C = Category C
  ID : Section (Δ C) (Hom C)
  ID = mkPropHomsSection (hasPropHomsHom C)
    (λ x → C.id)
    (λ f → C.⋆IdR _ ∙ sym (C.⋆IdL _))

  module _ {D : Category ℓD ℓD'}
           {F1 F2 : Functor D C}
         where
    open Section
    open NatTrans
    SectionHom→NatTrans :
      ∀ (Fᴰ : Section (F1 ,F F2) (Hom C)) → NatTrans F1 F2
    SectionHom→NatTrans Fᴰ .N-ob  = Fᴰ .F-obᴰ
    SectionHom→NatTrans Fᴰ .N-hom = Fᴰ .F-homᴰ

-- TODO: A J-style elimination rule?
