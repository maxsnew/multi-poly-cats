{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Base.HLevel1Homs where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  private
    module Cᴰ = Categoryᴰ Cᴰ

  hasContrHoms : Type _
  hasContrHoms =
    ∀ {c c' : C .ob}(f : C [ c , c' ])(cᴰ : Cᴰ.ob[ c ])(cᴰ' : Cᴰ.ob[ c' ])
      → isContr Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]

  hasPropHoms : Type _
  hasPropHoms =
    ∀ {c c' : C .ob}(f : C [ c , c' ])(cᴰ : Cᴰ.ob[ c ])(cᴰ' : Cᴰ.ob[ c' ])
      → isProp Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]

  hasContrHoms→hasPropHoms : hasContrHoms → hasPropHoms
  hasContrHoms→hasPropHoms contrHoms =
    λ f cᴰ cᴰ' → isContr→isProp (contrHoms f cᴰ cᴰ')

module _
       {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
       {F : Functor C D}
       {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Category
  open Functor
  private
    module Dᴰ = Categoryᴰ Dᴰ
  mkSectionPropHoms :
    (propHoms : hasPropHoms Dᴰ)
      → (F-obᴰ  : (x : C .ob) → Dᴰ.ob[ F .F-ob x ])
      → (F-homᴰ : {x y : C .ob}
        (f : C [ x , y ]) → Dᴰ [ F .F-hom f ][ F-obᴰ x , F-obᴰ y ])
      → Section F Dᴰ
  mkSectionPropHoms propHoms F-obᴰ F-homᴰ .Section.F-obᴰ = F-obᴰ
  mkSectionPropHoms propHoms F-obᴰ F-homᴰ .Section.F-homᴰ = F-homᴰ
  mkSectionPropHoms propHoms F-obᴰ F-homᴰ .Section.F-idᴰ =
    isProp→PathP (λ i → propHoms _ _ _) _ _
  mkSectionPropHoms propHoms F-obᴰ F-homᴰ .Section.F-seqᴰ _ _ =
    isProp→PathP (λ i → propHoms _ _ _) _ _

  mkSectionContrHoms :
    (contrHoms : hasContrHoms Dᴰ)
      → (F-obᴰ  : (x : C .ob) → Dᴰ.ob[ F .F-ob x ])
      → Section F Dᴰ
  mkSectionContrHoms contrHoms F-obᴰ = mkSectionPropHoms
    (hasContrHoms→hasPropHoms Dᴰ contrHoms)
    F-obᴰ
      λ {x}{y} f → contrHoms (F .F-hom f) (F-obᴰ x) (F-obᴰ y) .fst

module _
       {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
       {F : Functor C D}
       {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
       {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Category
  open Functor
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  mkFunctorᴰPropHoms :
    (propHoms : hasPropHoms Dᴰ)
      → (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
      → (F-homᴰ : {x y : C .ob}
        {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
        → Cᴰ [ f ][ xᴰ , yᴰ ] → Dᴰ [ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ])
      → Functorᴰ F Cᴰ Dᴰ
  mkFunctorᴰPropHoms propHoms F-obᴰ F-homᴰ .Functorᴰ.F-obᴰ = F-obᴰ
  mkFunctorᴰPropHoms propHoms F-obᴰ F-homᴰ .Functorᴰ.F-homᴰ = F-homᴰ
  mkFunctorᴰPropHoms propHoms F-obᴰ F-homᴰ .Functorᴰ.F-idᴰ =
    isProp→PathP (λ i → propHoms _ _ _) _ _
  mkFunctorᴰPropHoms propHoms F-obᴰ F-homᴰ .Functorᴰ.F-seqᴰ _ _ =
    isProp→PathP (λ i → propHoms _ _ _) _ _

  mkFunctorᴰContrHoms : (contrHoms : hasContrHoms Dᴰ)
                      → (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
                      → Functorᴰ F Cᴰ Dᴰ
  mkFunctorᴰContrHoms contrHoms F-obᴰ =
    mkFunctorᴰPropHoms (hasContrHoms→hasPropHoms Dᴰ contrHoms) F-obᴰ
    λ _ → contrHoms _ _ _ .fst

  -- Alternate version: maybe Dᴰ.Hom[_][_,_] isn't always
  -- contractible, but it is in the image of F-obᴰ
  mkFunctorᴰContrHoms'
    : (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
    → (F-homᴰ : {x y : C .ob}
      {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
    → Cᴰ [ f ][ xᴰ , yᴰ ]
    → isContr (Dᴰ [ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]))
    → Functorᴰ F Cᴰ Dᴰ
  mkFunctorᴰContrHoms' F-obᴰ F-homᴰ .Functorᴰ.F-obᴰ = F-obᴰ
  mkFunctorᴰContrHoms' F-obᴰ F-homᴰ .Functorᴰ.F-homᴰ fᴰ = F-homᴰ fᴰ .fst
  mkFunctorᴰContrHoms' F-obᴰ F-homᴰ .Functorᴰ.F-idᴰ =
    symP (toPathP (isProp→PathP (λ i → isContr→isProp (F-homᴰ Cᴰ.idᴰ)) _ _))
  mkFunctorᴰContrHoms' F-obᴰ F-homᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ =
    symP (toPathP (isProp→PathP
      (λ i → isContr→isProp (F-homᴰ (fᴰ Cᴰ.⋆ᴰ gᴰ))) _ _))
