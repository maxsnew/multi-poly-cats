-- Free category quotiented by equations
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Presented where

open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base hiding (Id)
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients as SetQuotient
  renaming ([_] to [_]q) hiding (rec; elim)

open import Cubical.Categories.Constructions.Quotient as CatQuotient
open import Cubical.Categories.Constructions.Free.Category.Quiver as Free
  hiding (rec; elim)
open import Cubical.Categories.Constructions.Quotient.More as CatQuotient
  hiding (elim)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Section

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓj : Level

open Category
open Functor
open NatIso hiding (sqRL; sqLL)
open NatTrans

module _ (𝓒 : Category ℓc ℓc') where
  record Axioms ℓj : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-suc ℓj)) where
    field
      equation : Type ℓj
      dom cod : equation → 𝓒 .ob
      lhs rhs : ∀ eq → 𝓒 [ dom eq , cod eq ]

  open Axioms
  mkAx : (Equation : Type ℓj) →
         (Equation →
           Σ[ A ∈ 𝓒 .ob ] Σ[ B ∈ 𝓒 .ob ] 𝓒 [ A , B ] × 𝓒 [ A , B ]) →
         Axioms ℓj
  mkAx Eq funs .equation = Eq
  mkAx Eq funs .dom eq = funs eq .fst
  mkAx Eq funs .cod eq = funs eq .snd .fst
  mkAx Eq funs .lhs eq = funs eq .snd .snd .fst
  mkAx Eq funs .rhs eq = funs eq .snd .snd .snd

  -- TODO: make this a named module for a better API
  module QuoByAx (Ax : Axioms ℓj) where
    data _≈_ : ∀ {A B} → 𝓒 [ A , B ] → 𝓒 [ A , B ] →
               Type (ℓ-max (ℓ-max ℓc ℓc') ℓj) where
      ↑_ : ∀ eq → Ax .lhs eq ≈ Ax .rhs eq
      reflₑ : ∀ {A B} → (e : 𝓒 [ A , B ]) → e ≈ e
      ⋆ₑ-cong : ∀ {A B C}
           → (e e' : 𝓒 [ A , B ]) → (e ≈ e')
           → (f f' : 𝓒 [ B , C ]) → (f ≈ f')
           → (e ⋆⟨ 𝓒 ⟩ f) ≈ (e' ⋆⟨ 𝓒 ⟩ f')
      ⋆ₑIdL : ∀ {A B} (e : 𝓒 [ A , B ]) → (𝓒 .id ⋆⟨ 𝓒 ⟩ e) ≈ e
      ⋆ₑIdR : ∀ {A B} (e : 𝓒 [ A , B ]) → (e ⋆⟨ 𝓒 ⟩ 𝓒 .id) ≈ e
      ⋆ₑAssoc : ∀ {A B C D} (e : 𝓒 [ A , B ])
               (f : 𝓒 [ B , C ])(g : 𝓒 [ C , D ])
              → ((e ⋆⟨ 𝓒 ⟩ f) ⋆⟨ 𝓒 ⟩ g) ≈ (e ⋆⟨ 𝓒 ⟩ (f ⋆⟨ 𝓒 ⟩ g))

    PresentedCat : Category _ _
    PresentedCat = QuotientCategory 𝓒 _≈_ reflₑ ⋆ₑ-cong

    ToPresented = QuoFunctor 𝓒 _≈_ reflₑ ⋆ₑ-cong

    isFullToPresented : isFull ToPresented
    isFullToPresented A B = []surjective

    ηEq : ∀ eq → Path (PresentedCat [ Ax .dom eq , Ax .cod eq ])
                      [ Ax .lhs eq ]q
                      [ Ax .rhs eq ]q
    ηEq eq = eq/ _ _ (↑ eq)

    module _ (𝓓 : Categoryᴰ PresentedCat ℓd ℓd') where
      private
        𝓓' = reindexᴰQuo 𝓒 _≈_ reflₑ ⋆ₑ-cong 𝓓
        module 𝓓 = Categoryᴰ 𝓓
        module R = HomᴰReasoning 𝓓

      open Section
      elim : (F : Section 𝓓')
           → (∀ eq →
             PathP (λ i → 𝓓.Hom[ ηEq eq i ][
                                 F .F-ob (Ax .dom eq)
                               , F .F-ob (Ax .cod eq) ])
                   (F .F-hom (Ax .lhs eq))
                   (F .F-hom (Ax .rhs eq)))
           → Section 𝓓
      elim F F-respects-axioms =
        CatQuotient.elim 𝓒 _≈_ reflₑ ⋆ₑ-cong 𝓓 F
          (λ _ _ → F-respects-≈) where
        F-respects-≈ : {x y : 𝓒 .ob} {f g : Hom[ 𝓒 , x ] y}
          (p : f ≈ g) →
          PathP
          (λ i → 𝓓.Hom[ eq/ f g p i ][
            F .F-ob x
          , F .F-ob y ])
          (F .F-hom f)
          (F .F-hom g)
        F-respects-≈ (↑ eq) = F-respects-axioms eq
        F-respects-≈ {x}{y} (reflₑ f) = R.≡[]-rectify {p = refl} refl
        F-respects-≈ (⋆ₑ-cong e e' p f f' q) =
          R.≡[]-rectify
          (F .F-seq e f ◁
          (λ i → F-respects-≈ p i 𝓓.⋆ᴰ F-respects-≈ q i)
          ▷ (sym (F .F-seq e' f')))
        F-respects-≈ (⋆ₑIdL g) = R.≡[]-rectify
          ( F .F-seq _ _
          ∙ cong₂ 𝓓._⋆ᴰ_ (F .F-id) refl
          ◁ 𝓓.⋆IdLᴰ (F .F-hom g))
        F-respects-≈ {x}{y} (⋆ₑIdR g) = R.≡[]-rectify
          ( F .F-seq _ _
          ∙ cong₂ 𝓓._⋆ᴰ_ refl (F .F-id)
          ◁ 𝓓.⋆IdRᴰ (F .F-hom g))
        F-respects-≈ (⋆ₑAssoc e f g) = R.≡[]-rectify
          ( F .F-seq _ _ ∙ cong₂ 𝓓._⋆ᴰ_ (F .F-seq _ _) refl
          ◁ 𝓓.⋆Assocᴰ (F .F-hom e) (F .F-hom f) (F .F-hom g)
          ▷ sym (F .F-seq _ _ ∙ cong₂ 𝓓._⋆ᴰ_ refl (F .F-seq _ _)))

    module _ (𝓓 : Category ℓd ℓd') (F : Functor 𝓒 𝓓)
      (F-satisfies-axioms : ∀ eq →
        F ⟪ Ax .lhs eq ⟫ ≡ F ⟪ Ax .rhs eq ⟫) where
        rec : Functor PresentedCat 𝓓
        rec = Iso.fun (SectionToWkIsoFunctor _ _)
          (elim (weaken _ 𝓓) F' F-satisfies-axioms) where
          -- There's probably a general principle but η expansion is
          -- easier
          F' : Section _
          F' .Section.F-ob = F .F-ob
          F' .Section.F-hom = F .F-hom
          F' .Section.F-id = F .F-id
          F' .Section.F-seq = F .F-seq
