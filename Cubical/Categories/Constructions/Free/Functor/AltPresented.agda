-- This module defines the free category H equipped with a functor
-- from a given category 𝓒
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Constructions.Free.Functor.AltPresented where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum hiding (rec; elim)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Properties as DCat
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation

open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Constructions.Presented as Presented
open import Cubical.Categories.Constructions.Free.Category.Quiver as FreeCat
  hiding (rec; elim)
open import Cubical.Categories.Displayed.Preorder as PO

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ ℓcᴰ ℓcᴰ' ℓdᴰ ℓdᴰ' : Level

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open Cat.Section
open QuiverOver
open HetQG
open Axioms
-- open Interpᴰ


module _ (𝓒 : Category ℓc ℓc') where
  HQuiver : ∀ ℓh ℓh' → Type _
  HQuiver ℓh ℓh' = Σ[ Hgen ∈ Type ℓh ] QuiverOver (𝓒 .ob ⊎ Hgen) ℓh'

  module FreeFunctor (H : HQuiver ℓh ℓh') where
    private
      HOb = (𝓒 .ob ⊎ H .fst)

    HQ : Quiver (ℓ-max ℓc ℓh) (ℓ-max (ℓ-max ℓc ℓc') ℓh')
    HQ .fst = HOb
    HQ .snd .mor = Cat→Quiver 𝓒 .snd .mor ⊎ H .snd .mor
    HQ .snd .dom (inl (A , B , _)) = inl A
    HQ .snd .cod (inl (A , B , _)) = inl B
    HQ .snd .dom (inr g) = H .snd .dom g
    HQ .snd .cod (inr g) = H .snd .cod g

    PreHCat = FreeCat HQ
    ηPre = η HQ

    FunctorEquation =
    --   F⟪id⟫≡id
      𝓒 .ob
    --   F⟪⋆⟫≡⋆F⟪⟫
      ⊎ (Σ[ A ∈ 𝓒 .ob ] Σ[ B ∈ 𝓒 .ob ] Σ[ C ∈ 𝓒 .ob ]
        𝓒 [ A , B ] × 𝓒 [ B , C ])
    FunctorAxioms : Axioms PreHCat _
    FunctorAxioms = mkAx PreHCat FunctorEquation (Sum.rec
      (λ A → inl A , inl A
      , (↑ inl (_ , _ , 𝓒 .id)) -- F ⟪ G .id ⟫
      , PreHCat .id)                 -- H .id
      (λ (A , B , C , f , g) → inl A , inl C
      , (↑ (inl (_ , _ , f ⋆⟨ 𝓒 ⟩ g)))
      , ↑ (inl (_ , _ , f)) ⋆⟨ PreHCat ⟩ (↑ (inl (_ , _ , g)))))

    module PresentH = QuoByAx PreHCat FunctorAxioms
    HCat = PresentH.PresentedCat
    moduloAx = PresentH.ToPresented
    ηHEq  = PresentH.ηEq

    FreeFunctor : Functor 𝓒 HCat
    FreeFunctor .F-ob = inl
    FreeFunctor .F-hom e = moduloAx .F-hom (ηPre <$g> inl (_ , _ , e))
    FreeFunctor .F-id = ηHEq (inl _)
    FreeFunctor .F-seq f g = ηHEq (inr (_ , _ , _ , f , g))

    -- A version of elim that avoids reindex in the definition of
    -- s.
    module _ {𝓒ᴰ : Categoryᴰ 𝓒 ℓcᴰ ℓcᴰ'}
             {𝓓ᴰ : Categoryᴰ HCat ℓdᴰ ℓdᴰ'}
             (s : Cat.Section 𝓒ᴰ)
             (𝓕 : Functorᴰ FreeFunctor 𝓒ᴰ 𝓓ᴰ)
             (ıOb : ∀ (A : H .fst) → 𝓓ᴰ .ob[_] (inr A))
             where
      private
        ıOb' : ∀ (A : HOb) → 𝓓ᴰ .ob[_] A
        ıOb' = Sum.elim (λ A → 𝓕 .F-obᴰ (s .F-ob A)) ıOb
      module _ (ıHom : ∀ e
             → 𝓓ᴰ [ moduloAx .F-hom (ηPre <$g> inr e) ][
                    ıOb' (H .snd .dom e)
                  , ıOb' (H .snd .cod e) ]) where
        elim : Cat.Section 𝓓ᴰ
        elim = PresentH.elim 𝓓ᴰ (FreeCat.elim HQ ıHgen) satisfies-axioms where
          ıHgen : Interpᴰ HQ _
          ıHgen .Section.F-ob = ıOb'
          ıHgen .Section.F-hom (inl (_ , _ , e)) = 𝓕 .F-homᴰ (s .F-hom e)
          ıHgen .Section.F-hom (inr f) = ıHom f

          satisfies-axioms : ∀ (eq : FunctorAxioms .equation) → _
          -- F⟪ id A ⟫ ≡ id (F ⟅ A ⟆)
          satisfies-axioms (inl A) =
            cong (𝓕 .F-homᴰ) (s .F-id)
            ◁ 𝓕 .F-idᴰ
          -- F⟪ f ⋆ g ⟫ ≡ F⟪ f ⟫ ⋆ F⟪ g ⟫
          satisfies-axioms (inr (_ , _ , _ , f , g)) =
            cong (𝓕 .F-homᴰ) (s .F-seq _ _)
            ◁ 𝓕 .F-seqᴰ _ _

module CoUnit {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D)
  where

  DGenOb = C .ob ⊎ D .ob

  asDob : DGenOb → D .ob
  asDob = Sum.rec (F .F-ob) λ z → z

  DGen = Σ[ A ∈ DGenOb ] Σ[ B ∈ DGenOb ] (D [ asDob A , asDob B ])

  DQuiver : HQuiver C _ _
  DQuiver .fst = D .ob
  DQuiver .snd .mor = DGen
  DQuiver .snd .dom (A , B , f) = A
  DQuiver .snd .cod (A , B , f) = B

  open FreeFunctor (FreeCat (Cat→Quiver C)) DQuiver public
