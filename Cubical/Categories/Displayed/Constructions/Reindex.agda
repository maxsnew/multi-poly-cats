{-

-}
{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Constructions.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq
import      Cubical.Data.Equality.Conversion as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Magmoid

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  private
    module C = Category C
    module D = Category D

  open Categoryᴰ Dᴰ
  open Functor F
  open Functorᴰ

  forgetReindex : Functorᴰ F (reindex Dᴰ F) Dᴰ
  forgetReindex .F-obᴰ = λ z → z
  forgetReindex .F-homᴰ = λ z → z
  forgetReindex .F-idᴰ = symP (transport-filler _ _)
  forgetReindex .F-seqᴰ fᴰ gᴰ = symP (transport-filler _ _)

  GlobalSectionReindex→Section : GlobalSection (reindex Dᴰ F) → Section F Dᴰ
  GlobalSectionReindex→Section Fᴰ = compFunctorᴰGlobalSection forgetReindex Fᴰ

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {B : Category ℓB ℓB'}
  (G : Functor B C)
  (FGᴰ : Section (F ∘F G) Dᴰ)
  where
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module F*Dᴰ = Categoryᴰ (reindex Dᴰ F)
    module R = HomᴰReasoning Dᴰ
  open Functor
  open Section

  intro : Section G (reindex Dᴰ F)
  intro .F-obᴰ = FGᴰ .F-obᴰ
  intro .F-homᴰ = FGᴰ .F-homᴰ
  intro .F-idᴰ = R.≡[]-rectify (R.≡[]∙ _ _ (FGᴰ .F-idᴰ) (R.reind-filler _ _))
  intro .F-seqᴰ fᴰ gᴰ =
    R.≡[]-rectify (R.≡[]∙ _ _ (FGᴰ .F-seqᴰ fᴰ gᴰ) (R.reind-filler _ _))

-- module _
--   {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
--   {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
--   {F : Functor C D}
--   {B : Category ℓB ℓB'} {Bᴰ : Categoryᴰ B ℓBᴰ ℓBᴰ'}
--   (G : Functor B C)
--   (FGᴰ : Functorᴰ (F ∘F G) Bᴰ Dᴰ)
--   where
--   private
--     module Dᴰ = Categoryᴰ Dᴰ
--     module F*Dᴰ = Categoryᴰ (reindex Dᴰ F)
--     module R = HomᴰReasoning Dᴰ
--   open Functor
--   open Functorᴰ
--   -- todo: shouldn't this construct a Section?
--   intro : Functorᴰ G Bᴰ (reindex Dᴰ F)
--   intro .F-obᴰ = FGᴰ .F-obᴰ
--   intro .F-homᴰ = FGᴰ .F-homᴰ
--   intro .F-idᴰ = R.≡[]-rectify (R.≡[]∙ _ _ (FGᴰ .F-idᴰ) (R.reind-filler _ _))
--   intro .F-seqᴰ fᴰ gᴰ =
--     R.≡[]-rectify (R.≡[]∙ _ _ (FGᴰ .F-seqᴰ fᴰ gᴰ) (R.reind-filler _ _))

-- module _
--   {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
--   where

--   private
--     module C = Category C
--     module R = HomᴰReasoning Cᴰ

--     -- todo: generalize upstream somewhere to Data.Equality?
--     isPropEqHom : ∀ {a b : C.ob} {f g : C [ a , b ]}
--                 → isProp (f Eq.≡ g)
--     isPropEqHom {f = f}{g} =
--       subst isProp (Eq.PathPathEq {x = f}{y = g}) (C.isSetHom f g)

--   open Categoryᴰ Cᴰ

--   reind' : {a b : C.ob} {f g : C [ a , b ]} (p : f Eq.≡ g)
--       {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
--     → Hom[ f ][ aᴰ , bᴰ ] → Hom[ g ][ aᴰ , bᴰ ]
--   reind' p = Eq.transport Hom[_][ _ , _ ] p

--   reind≡reind' : ∀ {a b : C.ob} {f g : C [ a , b ]}
--     {p : f ≡ g} {e : f Eq.≡ g}
--     {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
--     → (fᴰ : Hom[ f ][ aᴰ , bᴰ ])
--     → R.reind p fᴰ ≡ reind' e fᴰ
--   reind≡reind' {p = p}{e} fᴰ =
--     subst {x = Eq.pathToEq p}
--       (λ e → R.reind p fᴰ ≡ reind' e fᴰ)
--       (isPropEqHom _ _)
--       lem
--     where
--     lem : R.reind p fᴰ ≡ reind' (Eq.pathToEq p) fᴰ
--     lem = sym (Eq.eqToPath
--       ((Eq.transportPathToEq→transportPath Hom[_][ _ , _ ]) p fᴰ))

-- open Category
-- open Functor

-- module EqReindex
--   {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
--   (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
--   (F : Functor C D)
--   (F-id'  : {x : C .ob} → D .id {x = F .F-ob x} Eq.≡ F .F-hom (C .id))
--   (F-seq' : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
--           → (F .F-hom f) ⋆⟨ D ⟩ (F .F-hom g) Eq.≡ F .F-hom (f ⋆⟨ C ⟩ g))
--   where

--   private
--     module R = HomᴰReasoning Dᴰ
--     module C = Category C
--     module D = Category D
--     module Dᴰ = Categoryᴰ Dᴰ

--     singId : singl {A = {x : C .ob} {p : Dᴰ .Categoryᴰ.ob[_] (F .F-ob x)} →
--        Dᴰ .Categoryᴰ.Hom[_][_,_] {F .F-ob x} {F .F-ob x}
--        (F .F-hom {x} {x} (C .id {x})) p p}
--        (R.reind (λ i → F .F-id (~ i)) (Dᴰ.idᴰ))
--     singId = (reind' Dᴰ F-id' Dᴰ.idᴰ ,
--       implicitFunExt (λ {x} → implicitFunExt (λ {xᴰ} →
--       reind≡reind' Dᴰ Dᴰ.idᴰ)))


--     singSeq : singl
--       {A = ∀ {x y z} {f : C .Hom[_,_] x y} {g : C .Hom[_,_] y z}{xᴰ}{yᴰ}{zᴰ}
--        → Dᴰ.Hom[ F .F-hom f ][ xᴰ , yᴰ ]
--        → Dᴰ.Hom[ F .F-hom g ][ yᴰ , zᴰ ]
--        → Dᴰ.Hom[ F .F-hom (f C.⋆ g)][ xᴰ , zᴰ ]}
--       (λ {x}{y}{z}{f}{g} fᴰ gᴰ → R.reind (sym (F .F-seq f g)) (fᴰ Dᴰ.⋆ᴰ gᴰ))
--     singSeq = (λ fᴰ gᴰ → reind' Dᴰ (F-seq' _ _) (Dᴰ._⋆ᴰ_ fᴰ gᴰ)) ,
--       implicitFunExt (λ {x} → implicitFunExt (λ {y} → implicitFunExt (λ {z} →
--       implicitFunExt (λ {f} → implicitFunExt (λ {g} → implicitFunExt (λ {xᴰ} →
--       implicitFunExt (λ {yᴰ} → implicitFunExt (λ {zᴰ} →
--       funExt (λ fᴰ → funExt λ gᴰ → reind≡reind' Dᴰ (fᴰ Dᴰ.⋆ᴰ gᴰ))))))))))

--   -- This definition is preferable to reindex when F-id' and F-seq'
--   -- are given by Eq.refl.
--   reindex' : Categoryᴰ C ℓDᴰ ℓDᴰ'
--   reindex' = redefine-id⋆ (reindex Dᴰ F) singId singSeq


--    -- TODO: it would be really nice to have a macro reindexRefl! that
--    -- worked like the following: See
--    -- Cubical.Categories.Constructions.Quotient.More for an example
--    -- reindexRefl! Cᴰ F = reindex' Cᴰ F Eq.refl (λ _ _ → Eq.refl)

--   -- TODO: Reindex' needs to be a module to make this easier to use
--   module _ {B : Category ℓB ℓB'} {Bᴰ : Categoryᴰ B ℓBᴰ ℓBᴰ'}
--            (G : Functor B C)
--            (FGᴰ : Functorᴰ (F ∘F G) Bᴰ Dᴰ)
--          where
--     intro' : Functorᴰ G Bᴰ reindex'
--     intro' = redefine-id⋆F (reindex Dᴰ F) singId singSeq (intro G FGᴰ)

--   open Functorᴰ
--   -- There's probably an easier way if we use sing'
--   forgetReindex' : Functorᴰ F reindex' Dᴰ
--   forgetReindex' .F-obᴰ xᴰ = xᴰ
--   forgetReindex' .F-homᴰ fᴰ = fᴰ
--   forgetReindex' .F-idᴰ {x}{xᴰ} =
--     subst (λ F-id' → PathP (λ i → Dᴰ.Hom[ F .F-id i ][ xᴰ , xᴰ ])
--       F-id'
--       Dᴰ.idᴰ)
--       (λ i → singId .snd i)
--       (symP (R.reind-filler (sym (F .F-id)) _))
--   forgetReindex' .F-seqᴰ {x} {y} {z} {f} {g} {xᴰ} {yᴰ} {zᴰ} fᴰ gᴰ =
--     subst
--       {A = ∀ {x y z} {f : C .Hom[_,_] x y} {g : C .Hom[_,_] y z}{xᴰ}{yᴰ}{zᴰ}
--        → Dᴰ.Hom[ F .F-hom f ][ xᴰ , yᴰ ]
--        → Dᴰ.Hom[ F .F-hom g ][ yᴰ , zᴰ ]
--        → Dᴰ.Hom[ F .F-hom (f C.⋆ g)][ xᴰ , zᴰ ]}
--       (λ F-seq' →  PathP (λ i → Dᴰ.Hom[ F .F-seq f g i ][ xᴰ , zᴰ ])
--        (F-seq' fᴰ gᴰ) (fᴰ Dᴰ.⋆ᴰ gᴰ))
--       (λ i → singSeq .snd i)
--       (symP (R.reind-filler (sym (F .F-seq f g)) _))
