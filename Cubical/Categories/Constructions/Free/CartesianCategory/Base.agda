{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

module _ (Q : ×Quiver) where
  open ProductQuiver
  -- NOTE: I tried to make Ob opaque, but it doesn't make sense to since
  -- - You need to know the implementation to know when you can pair morphisms (equal dom)
  -- - Yes, this means Ob normalizes out when we don't always want it to, but opaque won't solve that issue
  open ×Quiver-Nice Q
  data Exp : Ob → Ob → Type (ℓ-suc ℓ-zero) where
    -- Category
    ↑ₑ_ : ∀ t → Exp (Dom t) (Cod t)
    idₑ : ∀{Γ} → Exp Γ Γ
    _⋆ₑ_ : ∀{Γ Γ' Γ''}(δ : Exp Γ Γ') → (δ' : Exp Γ' Γ'') →  Exp Γ Γ''
    ⋆ₑIdL : ∀{Γ Δ}(δ : Exp Γ Δ) → idₑ ⋆ₑ δ ≡ δ
    ⋆ₑIdR : ∀{Γ Δ}(δ : Exp Γ Δ) → δ ⋆ₑ idₑ ≡ δ
    ⋆ₑAssoc : ∀{Γ Γ' Γ'' Γ'''}(δ : Exp Γ Γ')(δ' : Exp Γ' Γ'')(δ'' : Exp Γ'' Γ''') → (δ ⋆ₑ δ') ⋆ₑ δ'' ≡ δ ⋆ₑ (δ' ⋆ₑ δ'')
    isSetExp : ∀{Γ Γ'} → isSet (Exp Γ Γ')
    -- CartesianCategory
    -- I'd like to directly stipulate `!ₑ : ∀ Γ → isContr (Exp Γ ⊤)`
    -- but this is the best we'll get
    -- NOTE: here, we choose ! instead of just saying it merely exists
    !ₑ : ∀{Γ} → Exp Γ ⊤
    ⊤η : ∀{Γ}(t : Exp Γ ⊤) → t ≡ !ₑ
    π₁ : ∀{Γ Δ} → Exp (Γ × Δ) Γ
    π₂ : ∀{Γ Δ} → Exp (Γ × Δ) Δ
    -- and similarily, I'd like to just `isBinProduct`
    ⟨_,_⟩ : ∀{Γ Δ Δ'} → Exp Γ Δ → Exp Γ Δ' → Exp Γ (Δ × Δ')
    ×β₁ : ∀{Γ Δ Δ'}{t : Exp Γ Δ}{t' : Exp Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₁ ≡ t
    ×β₂ : ∀{Γ Δ Δ'}{t : Exp Γ Δ}{t' : Exp Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₂ ≡ t'
    ×η : ∀{Γ Δ Δ'}{t : Exp Γ (Δ × Δ')} → ⟨ t ⋆ₑ π₁ , t ⋆ₑ π₂ ⟩ ≡ t

  open Category
  |FreeCartesianCategory| : Category _ _
  |FreeCartesianCategory| .ob = Ob
  |FreeCartesianCategory| .Hom[_,_] = Exp
  |FreeCartesianCategory| .id = idₑ
  |FreeCartesianCategory| ._⋆_ = _⋆ₑ_
  |FreeCartesianCategory| .⋆IdL = ⋆ₑIdL
  |FreeCartesianCategory| .⋆IdR = ⋆ₑIdR
  |FreeCartesianCategory| .⋆Assoc = ⋆ₑAssoc
  |FreeCartesianCategory| .isSetHom = isSetExp

  FreeCartesianCategory : CartesianCategory _ _
  FreeCartesianCategory .fst = |FreeCartesianCategory|
  FreeCartesianCategory .snd .fst = ⊤ , λ Γ → !ₑ , λ t → sym (⊤η t)
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.binProdOb = Γ × Δ
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.binProdPr₁ = π₁
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.binProdPr₂ = π₂
  -- this is a bit of a tedious proof I've c/p from the superceded PR draft
  -- I'm not sure anymore why we use isSet', but I'll take it
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.univProp f g = (⟨ f , g ⟩ , ×β₁ , ×β₂) ,
    λ (h , p , q) → λ i →
      sym (×η-lemma h p q) i ,
      isSet→isSet' isSetExp ×β₁ p (congS (λ x → x ⋆ₑ π₁) (sym (×η-lemma h p q))) refl i ,
      isSet→isSet' isSetExp ×β₂ q (congS (λ x → x ⋆ₑ π₂) (sym (×η-lemma h p q))) refl i
    where
    -- this direction has more `sym` s, but I like it more
    ×η-lemma : ∀{Γ Δ Δ'}{f g}(h : Exp Γ (Δ × Δ')) → h ⋆ₑ π₁ ≡ f → h ⋆ₑ π₂ ≡ g → h ≡ ⟨ f , g ⟩
    ×η-lemma h p q = (sym ×η) ∙ cong₂ (λ x y → ⟨ x , y ⟩) p q
