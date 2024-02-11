{-
  The graph category of a profunctor viewed as a displayed category over the product.
-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Graph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Preorder

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level

open Category
open Preorderᴰ
open Functor

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
         (R : Bifunctor (C ^op) D (SET ℓS))
         where
  open Bifunctor

  private
    Graph' : Preorderᴰ (C ×C D) ℓS ℓS
    Graph' .ob[_] (c , d) = ⟨ R ⟅ c , d ⟆b ⟩
    Graph' .Hom[_][_,_] (f , g) r s = (R ⟪ f ⟫l) s ≡ (R ⟪ g ⟫r) r
    Graph' .idᴰ =
      funExt⁻ (R .Bif-L-id) _
      ∙ sym (funExt⁻ (R .Bif-R-id) _)
    Graph' ._⋆ᴰ_ {f = f , g}{g = f' , g'} r s =
      funExt⁻ (R .Bif-L-seq _ _) _
      ∙ cong (R ⟪ f ⟫l) s
      ∙ funExt⁻ ((Bif-RL-commute R _ _)) _
      ∙ cong (R ⟪ g' ⟫r) r
      ∙ sym ( funExt⁻ (R .Bif-R-seq _ _) _)
    Graph' .isPropHomᴰ {x = c , d}{y = c' , d'} = str (R ⟅ c , d' ⟆b) _ _

  Graph : Categoryᴰ (C ×C D) ℓS ℓS
  Graph = Preorderᴰ→Catᴰ Graph'

  hasPropHomsGraph : hasPropHoms Graph
  hasPropHomsGraph = hasPropHomsPreorderᴰ Graph'

  -- TODO: show Graph is a two-sided discrete fibration
  -- https://ncatlab.org/nlab/show/profunctor#in_terms_of_twosided_discrete_fibrations