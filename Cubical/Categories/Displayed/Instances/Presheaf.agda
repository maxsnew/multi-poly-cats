{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning

private
  variable ℓC ℓC' ℓSET : Level

module _ (C : Category ℓC ℓC') ℓSET ℓSETᴰ where
  open Category
  open Functor
  open Categoryᴰ
  module _ (P : Presheaf C ℓSET) where
    -- Displayed Sets
    Presheafᴰ-ob : Type _
    Presheafᴰ-ob = (Γ : C .ob) → ⟨ P ⟅ Γ ⟆ ⟩ → hSet ℓSETᴰ
    module _ (Pᴰ-ob : Presheafᴰ-ob) where
      Presheafᴰ-hom : Type _
      Presheafᴰ-hom = ∀{Γ Δ}(f : C [ Γ , Δ ]) →
        (ϕ : ⟨ P ⟅ Δ ⟆ ⟩) →
        ⟨ Pᴰ-ob Δ ϕ ⟩ →
        ⟨ Pᴰ-ob Γ (ϕ ∘ᴾ⟨ C , P ⟩ f) ⟩
    Presheafᴰ = Σ[ Pᴰ-ob ∈ Presheafᴰ-ob ] Presheafᴰ-hom Pᴰ-ob
    -- TODO: use implicit args instead of private modules
    -- This is so gross...
    module PresheafᴰNotation (Pᴰ : Presheafᴰ) where
      ⟅_,_⟆ : (Γ : C .ob) → ⟨ P ⟅ Γ ⟆ ⟩ → hSet ℓSETᴰ
      ⟅ Γ , ϕ ⟆ = Pᴰ .fst Γ ϕ
      actionᴰ : {Γ Δ : C .ob} (f : C [ Γ , Δ ]) →
        (ϕ : ⟨ P ⟅ Δ ⟆ ⟩) →
        ⟨ ⟅ Δ , ϕ ⟆ ⟩ →
        ⟨ ⟅ Γ , ϕ ∘ᴾ⟨ C , P ⟩ f ⟆ ⟩
      actionᴰ = Pᴰ .snd
      syntax actionᴰ f ϕ ϕᴰ = ϕᴰ ∘ᴾ⟨ ϕ ⟩ f
  -- Displayed Natural Transformation-- of presheaves specifically
  -- (left Categoryᴰ is trivial, compared to general NatTransᴰ)
  module _ {P Q : Presheaf C ℓSET}(α : NatTrans P Q)
    (Pᴰ : Presheafᴰ P)(Qᴰ : Presheafᴰ Q) where
    private
      module Pᴰ = PresheafᴰNotation P Pᴰ
      module Qᴰ = PresheafᴰNotation Q Qᴰ
    NatTransᴰ-ob : Type _
    NatTransᴰ-ob = (Γ : C .ob) →
      (ϕ : ⟨ P ⟅ Γ ⟆ ⟩) →
      ⟨ Pᴰ.⟅ Γ , ϕ ⟆ ⟩ →
       ⟨ Qᴰ.⟅ Γ , (α ⟦ Γ ⟧) ϕ ⟆ ⟩
    module _ (αᴰ-ob : NatTransᴰ-ob) where
      open NatTrans
      NatTransᴰ-hom : Type _
      NatTransᴰ-hom = ∀{Γ Δ}(f : C [ Γ , Δ ]) →
        (ϕ : ⟨ P ⟅ Δ ⟆ ⟩) →
        (ϕᴰ : ⟨ Pᴰ.⟅ Δ , ϕ ⟆ ⟩) →
        PathP (λ i → congS (λ x → ⟨ Qᴰ.⟅ Γ , x ϕ ⟆ ⟩) (α .N-hom f) i)
          (αᴰ-ob Γ (ϕ ∘ᴾ⟨ C , P ⟩ f) (ϕᴰ Pᴰ.∘ᴾ⟨ _ ⟩ f))
          ((αᴰ-ob Δ ϕ ϕᴰ) Qᴰ.∘ᴾ⟨ _ ⟩ f)
    NatTransᴰ = Σ[ αᴰ-ob ∈ NatTransᴰ-ob ] NatTransᴰ-hom αᴰ-ob
  PRESHEAFᴰ : Categoryᴰ (PresheafCategory C ℓSET) _ _
  PRESHEAFᴰ .ob[_] P = Presheafᴰ P
  PRESHEAFᴰ .Hom[_][_,_] α Pᴰ Qᴰ = NatTransᴰ α Pᴰ Qᴰ
  PRESHEAFᴰ .idᴰ {x = P} {p = Pᴰ} = (λ Γ ϕ ϕᴰ → ϕᴰ) ,
    λ {Γ = Γ} {Δ = Δ} f ϕ ϕᴰ →
      --(λ i →
      --   ⟨ Pᴰ.⟅ Γ , PresheafCategory C ℓSET .id .NatTrans.N-hom f i ϕ ⟆ ⟩)
      subst (λ x → PathP (λ i → ⟨ Pᴰ.⟅ Γ , x i ϕ ⟆ ⟩) (Pᴰ.actionᴰ f _ ϕᴰ) (Pᴰ.actionᴰ f _ ϕᴰ))
      (blll f) refl
      --subst (λ x → PathP (λ i → x i) (Pᴰ.actionᴰ f _ ϕᴰ) (Pᴰ.actionᴰ f _ ϕᴰ))
      --(test Γ Δ f ϕ ϕᴰ) refl {- toPathP (Pᴰ.⟅ Γ , _ ⟆ .snd ) -}
    where
      module Pᴰ = PresheafᴰNotation P Pᴰ
      --test : ∀ Γ Δ f ϕ ϕᴰ → {!⟨ Pᴰ.⟅ Γ , ? ⟆ ⟩!} ≡ {!!}
      --test F Δ f ϕ ϕᴰ = {!!}
      --arg : refl ∙ refl ≡ refl
      --arg = sym compPathRefl
      blll : ∀{Γ Δ} (f : C [ Γ , Δ ]) → refl ≡ PresheafCategory C ℓSET .id {x = P} .NatTrans.N-hom f
      blll f = compPathRefl ∙ congS (λ x → refl ∙ x) compPathRefl
      --subst (λ x → {!!})
      --((P ⟅ Γ ⟆) .snd (ϕ ∘ᴾ⟨ C , P ⟩ f) {! ⟦ Δ ⟧!} {!!} {!!})
      --refl
  PRESHEAFᴰ ._⋆ᴰ_ = {!!}
  PRESHEAFᴰ .⋆IdLᴰ = {!!}
  PRESHEAFᴰ .⋆IdRᴰ = {!!}
  PRESHEAFᴰ .⋆Assocᴰ = {!!}
  PRESHEAFᴰ .isSetHomᴰ = {!!}
