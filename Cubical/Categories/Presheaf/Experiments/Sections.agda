module Cubical.Categories.Presheaf.Experiments.Sections where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category

-- Type-valued presheaf
-- with dependent presheaves in terms of the Grothendieck construction
private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ₁ ℓ₂ : Level

open Category
module _ (C : Category ℓ ℓ') where
  record Presheaf ℓ'' : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-suc ℓ''))) where
    field
      ty : C .ob → Type ℓ''
      pull : ∀ {x y} (f : C [ x , y ]) → ty y → ty x
      pull-id : ∀ {x} → pull (C .id {x}) ≡ λ s → s
      pull-∘ : ∀ {x y z}{f : C [ x , y ]}{g : C [ y , z ]}
             → pull (f ⋆⟨ C ⟩ g) ≡ λ z → pull f (pull g z)

  open Presheaf
  isSetValued : Presheaf ℓ → Type _
  isSetValued P = ∀ c → isSet (P .ty c)

  _×ᴾ_ : Presheaf ℓ₁ → Presheaf ℓ₂ → Presheaf (ℓ-max ℓ₁ ℓ₂)
  (P ×ᴾ Q) .ty x = P .ty x × Q .ty x
  (P ×ᴾ Q) .pull f x = (P .pull f (x .fst)) , (Q .pull f (x .snd))
  (P ×ᴾ Q) .pull-id =
    funExt
      (λ pq → cong₂ _,_ (funExt⁻ (P .pull-id) (pq .fst))
                        ((funExt⁻ (Q .pull-id) (pq .snd))))
  (P ×ᴾ Q) .pull-∘ =
     funExt (λ pq → cong₂ _,_
       (funExt⁻ (P .pull-∘) (pq .fst))
       (funExt⁻ (Q .pull-∘) (pq .snd)))

  -- Dependent presheaf??
  module _ (P : Presheaf ℓ'') where
    Sectionᴾ : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    Sectionᴾ = Σ[ s ∈ (∀ x → P .ty x) ]
      (∀ x y (f : C [ x , y ]) (p : P .ty y) →
      P .pull f (s y) ≡ s x)

    -- "types"
    record Presheafᴰ ℓ''' : Type ((ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' (ℓ-suc ℓ'''))))) where
      field
        tyᴰ : ∀ {x} → P .ty x → Type ℓ'''
        pullᴰ : ∀ {x y} (f : C [ x , y ]) {p : P .ty y}
              → tyᴰ p → tyᴰ (P .pull f p)
        pullᴰ-id : ∀ {x} {p : P .ty x}
                 → PathP (λ i → tyᴰ p → tyᴰ (funExt⁻ (P .pull-id) p i))
                   (pullᴰ (C .id {x}))
                   λ x → x
        pullᴰ-∘ : ∀ {x y z}{f : C [ x , y ]}{g : C [ y , z ]}{p : P .ty z}
                → PathP (λ i → tyᴰ p → tyᴰ (funExt⁻ (P .pull-∘ {f = f}{g}) p i))
                  (pullᴰ (f ⋆⟨ C ⟩ g))
                  λ z → pullᴰ f (pullᴰ g z)

    open Presheafᴰ
    -- "terms"
    Sectionᴰ : Presheafᴰ ℓ''' → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ'') ℓ''')
    Sectionᴰ Pᴰ = Σ[ s ∈ (∀ x → (p : P .ty x) → Pᴰ .tyᴰ p) ]
      (∀ x y (f : C [ x , y ]) (p : P .ty y) →
      Pᴰ .pullᴰ f (s y p) ≡ s x (P .pull f p))

    -- context extension
    Σᴾ : Presheafᴰ ℓ''' → Presheaf (ℓ-max ℓ'' ℓ''')
    Σᴾ Pᴰ .ty x = Σ[ p ∈ P .ty x ] Pᴰ .tyᴰ p
    Σᴾ Pᴰ .pull f (p , pᴰ) = P .pull f p , Pᴰ .pullᴰ f pᴰ
    Σᴾ Pᴰ .pull-id =
      funExt (λ ppᴰ → cong₂ _,_ (funExt⁻ (P .pull-id) (ppᴰ .fst)) (funExt⁻ (Pᴰ .pullᴰ-id) (ppᴰ .snd)))
    Σᴾ Pᴰ .pull-∘ =
      funExt (λ (p , pᴰ) → cong₂ _,_
        (funExt⁻ (P .pull-∘) p)
        (funExt⁻ (Pᴰ .pullᴰ-∘) pᴰ))

  open Presheafᴰ
  module _ (P : Presheaf ℓ'') (Pᴰ : Presheafᴰ P ℓ''') (Qᴰ : Presheafᴰ (Σᴾ P Pᴰ) ℓ'''') where
    Σᴰ : Presheafᴰ P (ℓ-max ℓ''' ℓ'''')
    Σᴰ .tyᴰ p = Σ[ pᴰ ∈ Pᴰ .tyᴰ p ] Qᴰ .tyᴰ (p , pᴰ)
    Σᴰ .pullᴰ f (pᴰ , qᴰ) = (Pᴰ .pullᴰ f pᴰ) , (Qᴰ .pullᴰ f qᴰ)
    Σᴰ .pullᴰ-id = funExt (λ (pᴰ , qᴰ) → {!!}) -- todo
    Σᴰ .pullᴰ-∘ = {!!}

  -- Category internal to presheaves
  record PshCat ℓ'' ℓ''' : Type {!!} where
    field
      obᴾ : Presheaf ℓ''
      Homᴾ : Presheafᴰ (obᴾ ×ᴾ obᴾ) ℓ'''
      idᴾ : Sectionᴰ _ Homᴾ
