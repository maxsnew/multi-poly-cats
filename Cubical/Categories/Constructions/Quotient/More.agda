-- Quotient category
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Quotient.More where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Initial
open import Cubical.Foundations.HLevels
import      Cubical.Data.Equality as Eq
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients as SetQuotients
  renaming ([_] to ⟦_⟧) hiding (elim)

open import Cubical.Categories.Constructions.Quotient
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.Reindex as Reindex

private
  variable
    ℓ ℓ' ℓq ℓD ℓD' : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  module _ (_~_ : {x y : ob} (f g : Hom[ x , y ] ) → Type ℓq)
           (~refl : {x y : ob} (f : Hom[ x , y ] ) → f ~ f)
           (~cong : {x y z : ob}
                    (f f' : Hom[ x , y ]) → f ~ f'
                  → (g g' : Hom[ y , z ]) → g ~ g'
                  → (f ⋆ g) ~ (f' ⋆ g')) where
    private
      C/~ = QuotientCategory C _~_ ~refl ~cong
      QF = QuoFunctor C _~_ ~refl ~cong

    open Categoryᴰ
    open Section
    module _ (Dᴰ : Categoryᴰ C/~ ℓD ℓD') where
      private
        module Dᴰ = Categoryᴰ Dᴰ

      module ReindexQuo = EqReindex Dᴰ QF Eq.refl (λ _ _ → Eq.refl)

      open Section
      -- TODO: should elim construct a global section or a local section?
      elim : (F : GlobalSection ReindexQuo.reindex')
           → (∀ {x y} → (f g : Hom[ x , y ]) → (p : f ~ g) →
             PathP (λ i → Dᴰ.Hom[ eq/ f g p i ][ F .F-obᴰ x , F .F-obᴰ y ])
                   (F .F-homᴰ f)
                   (F .F-homᴰ g))
           → GlobalSection Dᴰ
      elim F F-resp-∼ .F-obᴰ = F .F-obᴰ
      elim F F-resp-∼ .F-homᴰ = SetQuotients.elim (λ _ → Dᴰ.isSetHomᴰ)
        (F .F-homᴰ)
        F-resp-∼
      elim F F-resp-∼ .F-idᴰ = F .F-idᴰ
      elim F F-resp-∼ .F-seqᴰ =
        elimProp2 (λ [f] [g] → Dᴰ.isSetHomᴰ _ _) (F .F-seqᴰ)

    -- TODO: elim' that constructs a local section
    -- module _ {D : Category ℓD ℓD'}
    --          (F : Functor C/~ D)
    --          (Dᴰ : Categoryᴰ D ℓD ℓD')
    --          where
    --   elim' : (Fᴰ : Section (F ∘F QF) Dᴰ)
    --         → Section F Dᴰ
    --   elim' Fᴰ = GlobalSection→Section Dᴰ F (elim (reindex Dᴰ F) {!ReindexQuo.intro'!} {!!})      
