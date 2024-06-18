{-# OPTIONS --safe #-}
{-

  Given a displayed category Cᴰ over C, and any object x in C, we can
  construct the fiber category over x whose objects are the Cᴰ.ob[ x ]
  and whose morphisms are those that are over the identity.

-}

module Cubical.Categories.Constructions.Fiber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv hiding (fiber)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.Hom
open import Cubical.Categories.Profunctor.Homomorphism.Unary
open import Cubical.Categories.Profunctor.Homomorphism.Bilinear
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning


private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ
  fiber : C .ob → Category ℓCᴰ ℓCᴰ'
  fiber x .ob = Cᴰ.ob[ x ]
  fiber x .Hom[_,_] xᴰ xᴰ' = Cᴰ.Hom[ C .id ][ xᴰ , xᴰ' ]
  fiber x .id = Cᴰ.idᴰ
  fiber x ._⋆_ fᴰ gᴰ = R.reind (C .⋆IdL _) (fᴰ Cᴰ.⋆ᴰ gᴰ)
  fiber x .⋆IdL f =
    R.≡[]-rectify (R.≡[]∙ _ _ (R.reind-filler-sym _ _) (Cᴰ.⋆IdLᴰ _))
  fiber x .⋆IdR f =
    R.≡[]-rectify (R.≡[]∙ _ _ (R.reind-filler-sym _ _) (Cᴰ.⋆IdRᴰ _))
  fiber x .⋆Assoc f g h =
    R.≡[]-rectify (R.≡[]∙ _ _
    (R.≡[]∙ _ _ (R.reind-filler-sym _ _)
     (R.≡[]∙ _ _ (R.≡[]⋆ _ refl (R.reind-filler-sym _ _) refl)
     (Cᴰ.⋆Assocᴰ _ _ _)))
    (R.≡[]∙ _ _ (R.≡[]⋆ refl _ refl (R.reind-filler _ _)) (R.reind-filler _ _)))
  fiber x .isSetHom = Cᴰ.isSetHomᴰ

  Homᴰ : ∀ {x y} → (f : C [ x , y ]) → fiber x o-[ ℓCᴰ' ]-* fiber y
  Homᴰ f = mkBifunctorSep F where
    open BifunctorSep
    F : BifunctorSep _ _ _
    F .Bif-ob xᴰ yᴰ = Cᴰ.Hom[ f ][ xᴰ , yᴰ ] , Cᴰ.isSetHomᴰ
    F .Bif-homL v d = λ fᴰ → R.reind (C .⋆IdL f) (v Cᴰ.⋆ᴰ fᴰ)
    F .Bif-homR c v = λ fᴰ → R.reind (C .⋆IdR f) (fᴰ Cᴰ.⋆ᴰ v)
    F .Bif-L-id = funExt λ fᴰ → R.≡[]-rectify (
      R.≡[]∙ _ _ (R.reind-filler-sym _ _)
      (Cᴰ.⋆IdLᴰ fᴰ))
    F .Bif-R-id = funExt (λ fᴰ → R.≡[]-rectify
      (R.≡[]∙ _ _ (R.reind-filler-sym _ _)
      (Cᴰ.⋆IdRᴰ fᴰ)))
    F .Bif-L-seq v u = funExt λ fᴰ → R.≡[]-rectify
      (R.≡[]∙ _ _ (R.reind-filler-sym _ _)
      (R.≡[]∙ _ _ (R.≡[]⋆ _ refl (R.reind-filler-sym _ _) refl)
      (R.≡[]∙ _ _ (Cᴰ.⋆Assocᴰ _ _ _)
      (R.≡[]∙ _ _ (R.≡[]⋆ refl _ refl (R.reind-filler _ _))
      (R.reind-filler _ _)))))
    F .Bif-R-seq v u = funExt λ fᴰ → R.≡[]-rectify
      (R.≡[]∙ _ _ (R.reind-filler-sym _ _)
      (R.≡[]∙ _ _ (R.≡[]⋆ refl _ refl (R.reind-filler-sym _ _))
      (R.≡[]∙ _ _ (symP (Cᴰ.⋆Assocᴰ _ _ _))
      (R.≡[]∙ _ _ (R.≡[]⋆ _ refl (R.reind-filler _ _) refl)
      (R.reind-filler _ _)))))
    F .SepBif-RL-commute v u = funExt λ fᴰ → R.≡[]-rectify
      (R.≡[]∙ _ _ (R.reind-filler-sym _ _)
      (R.≡[]∙ _ _ (R.≡[]⋆ refl _ refl (R.reind-filler-sym _ _))
      (R.≡[]∙ _ _ (R.≡[]∙ _ _ (symP (Cᴰ.⋆Assocᴰ v fᴰ u))
      (R.≡[]⋆ _ refl (R.reind-filler _ _) refl))
      (R.reind-filler _ _))))
