{-
   Local Sections of a displayed category.

          A
        ↗ |
       /  |
    M /   |
     /    |
    /     ↓
   Δ ---→ Γ
       γ

   Every Section can be implemented as a Functorᴰ out of Unitᴰ (see
   Displayed.Instances.Terminal):

       M
   Δ ----→ A
   |       |
   |       |
   |       |
   |       |
   |       ↓
   Δ ----→ Γ
       γ

   And vice-versa any Functorᴰ

       M
   B ----→ A
   |       |
   |       |
   |       |
   |       |
   ↓       ↓
   Δ ----→ Γ
       γ

   Can be implemented as a Section (see
   Displayed.Constructions.TotalCategory)

            A
          ↗ |
         /  |
      M /   |
       /    |
      /     ↓
   Δ.B ---→ Γ
         γ

   Both options are sometimes more ergonomic. One of the main
   cosmetic differences is

   1. When defining a Functorᴰ, the object of the base category is
      implicit
   2. When defining a Section, the object of the base category is
      explicit

   Definitionally, there is basically no difference as these are
   definitional isomorphisms.

   Style advice is to use Sections by default, and use Functorᴰ only
   for things like displayed adjoints where they make more sense
   intuitively.

   Elimination rules are naturally stated in terms of local sections
   (and often global sections, see below). Intro rules can be
   formulated as either constructing a Section or a Functorᴰ. Good
   style is to offer both intro for Section and intro' for Functorᴰ.

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Section.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq
import      Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Equality
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Categoryᴰ
open Functor

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (F : Functor D C)
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         where
  private
    module C = Category C
    module D = Category D
    module Cᴰ = Categoryᴰ Cᴰ
    module F = Functor F

  -- Section without a qualifier means *local* section.
  record Section : Type (ℓ-max (ℓ-max ℓC ℓC')
                        (ℓ-max (ℓ-max ℓD ℓD')
                        (ℓ-max ℓCᴰ ℓCᴰ')))
    where
    field
      F-obᴰ  : ∀ d → Cᴰ.ob[ F ⟅ d ⟆ ]
      F-homᴰ : ∀ {d d'} (f : D.Hom[ d , d' ])
        → Cᴰ.Hom[ F ⟪ f ⟫ ][ F-obᴰ d , F-obᴰ d' ]
      F-idᴰ : ∀ {d} → F-homᴰ (D.id {d}) Cᴰ.≡[ F .F-id ] Cᴰ.idᴰ
      F-seqᴰ : ∀ {d d' d''}
            → (f : D.Hom[ d , d' ])(g : D.Hom[ d' , d'' ])
            → F-homᴰ (f D.⋆ g) Cᴰ.≡[ F .F-seq f g ] F-homᴰ f Cᴰ.⋆ᴰ F-homᴰ g

{-
   A Global Section is a local section over the identity functor.

          A
        ↗ |
       /  |
    M /   |
     /    |
    /     ↓
   Γ ==== Γ


   So global sections are by definition local sections

   All local sections can be implemented as global sections into the
   reindexed displayed category. See Reindex.agda for details.

   But this isomorphism is not a definitional equality. Constructing a
   local section is preferable as they are more flexible, but often
   elimination principles are naturally proven first about global
   sections and then generalized to local sections using reindexing.

   Style is offer both: elim to construct a local section and elim' to
   construct a global section.
-}

module _ {C : Category ℓC ℓC'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         where
  GlobalSection : Type _
  GlobalSection = Section Id Cᴰ

-- Reindexing a section. Makes
module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         where
  open Section
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ
  reindS : ∀ {F G}(H : Path (Functor D C) F G) → Section F Cᴰ → Section G Cᴰ
  reindS H = subst (λ F → Section F Cᴰ) H

  reindS' : ∀ {F G : Functor D C} (H : FunctorEq F G)
          → Section F Cᴰ
          → Section G Cᴰ
  reindS' {F}{G} (H-ob , H-hom) Fᴰ = record
    { F-obᴰ = Gᴰ-obᴰ (F-singl .fst)
    ; F-homᴰ = Gᴰ-homᴰ F-singl
    ; F-idᴰ = Gᴰ-idᴰ F-singl (G .F-id)
    ; F-seqᴰ = Gᴰ-seqᴰ F-singl (G .F-seq)
    } where
      F-singl : FunctorSingl F
      F-singl = (_ , H-ob) , (_ , H-hom)

      Gᴰ-obᴰ : (G : Eq.singl (F .F-ob)) → (d : D .ob) → Cᴰ.ob[ G .fst d ]
      Gᴰ-obᴰ (_ , Eq.refl) = Fᴰ .F-obᴰ

      Gᴰ-homᴰ : (G : FunctorSingl F) → ∀ {d d'} (f : D [ d , d' ])
              → Cᴰ.Hom[ G .snd .fst f ][ Gᴰ-obᴰ (G .fst) d , Gᴰ-obᴰ (G .fst) d' ]
      Gᴰ-homᴰ ((_ , Eq.refl), (_ , Eq.refl)) = Fᴰ .F-homᴰ

      Gᴰ-idᴰ : (G : FunctorSingl F)
               (G-id : ∀ {x} → G .snd .fst (D .id {x}) ≡ C .id)
             →  ∀ {d} → Gᴰ-homᴰ G (D .id {d}) Cᴰ.≡[ G-id ] Cᴰ.idᴰ
      Gᴰ-idᴰ ((_ , Eq.refl), (_ , Eq.refl)) G-id = R.≡[]-rectify (Fᴰ .F-idᴰ)

      Gᴰ-seqᴰ : (G : FunctorSingl F)
                (G-seq : ∀ {d d' d''}(f : D [ d , d' ])(g : D [ d' , d'' ])
                       → G .snd .fst (f ⋆⟨ D ⟩ g)
                       ≡ G .snd .fst f ⋆⟨ C ⟩ G .snd .fst g)
              → ∀ {d d' d'' : D .ob} (f : D [ d , d' ]) (g : D [ d' , d'' ])
              → Gᴰ-homᴰ G (f ⋆⟨ D ⟩ g) Cᴰ.≡[ G-seq f g ] (Gᴰ-homᴰ G f Cᴰ.⋆ᴰ Gᴰ-homᴰ G g)
      Gᴰ-seqᴰ ((_ , Eq.refl), (_ , Eq.refl)) G-seq f g = R.≡[]-rectify (Fᴰ .F-seqᴰ f g)
{-

   Composition of a Section and a Functor

                 A
               ↗ |
              /  |
           M /   |
            /    |
           /     ↓
   Δ' ---→ Δ ---→ Γ
              γ

-}
module _ {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F : Functor C D}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Functor
  open Section
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module R = HomᴰReasoning Dᴰ
  compSectionFunctor : Section F Dᴰ → (G : Functor B C) → Section (F ∘F G) Dᴰ
  compSectionFunctor Fᴰ G .F-obᴰ d     = Fᴰ .F-obᴰ (G .F-ob d)
  compSectionFunctor Fᴰ G .F-homᴰ f    = Fᴰ .F-homᴰ (G .F-hom f)
  compSectionFunctor Fᴰ G .F-idᴰ       = R.≡[]-rectify (R.≡[]∙ _ _
    (cong (Fᴰ .F-homᴰ) (G .F-id))
    (Fᴰ .F-idᴰ))
  compSectionFunctor Fᴰ G .F-seqᴰ f g = R.≡[]-rectify (R.≡[]∙ _ _
    (cong (Fᴰ .F-homᴰ) (G .F-seq f g))
    (Fᴰ .F-seqᴰ (G .F-hom f) (G .F-hom g)))


{-

  Composition of a Section and a Functorᴰ

             Fᴰ
          A ---→ A'
        ↗ |      |
       /  |      |
    M /   |      |
     /    |      |
    /     ↓      ↓
   Δ ---→ Γ ---→ Γ'
       γ     F

-}
module _ {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F : Functor C D}
         {G : Functor B C}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Functor
  open Functorᴰ
  open Section
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Dᴰ
  compFunctorᴰSection : Functorᴰ F Cᴰ Dᴰ → Section G Cᴰ → Section (F ∘F G) Dᴰ
  compFunctorᴰSection Fᴰ Gᴰ .F-obᴰ d    = Fᴰ .F-obᴰ (Gᴰ .F-obᴰ d)
  compFunctorᴰSection Fᴰ Gᴰ .F-homᴰ f   = Fᴰ .F-homᴰ (Gᴰ .F-homᴰ f)
  compFunctorᴰSection Fᴰ Gᴰ .F-idᴰ      = R.≡[]-rectify (R.≡[]∙ _ _
    (λ i → Fᴰ .F-homᴰ (Gᴰ .F-idᴰ i))
    (Fᴰ .F-idᴰ))
  compFunctorᴰSection Fᴰ Gᴰ .F-seqᴰ f g = R.≡[]-rectify (R.≡[]∙ _ _
    (λ i → Fᴰ .F-homᴰ (Gᴰ .F-seqᴰ f g i))
    (Fᴰ .F-seqᴰ (Gᴰ .F-homᴰ f) (Gᴰ .F-homᴰ g)))

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F : Functor C D}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Functor
  open Functorᴰ
  open Section
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Dᴰ

  compFunctorᴰGlobalSection : Functorᴰ F Cᴰ Dᴰ → GlobalSection Cᴰ → Section F Dᴰ
  compFunctorᴰGlobalSection Fᴰ Gᴰ = reindS' (Eq.refl , Eq.refl)
    (compFunctorᴰSection Fᴰ Gᴰ)
