{-# OPTIONS --safe #-}
-- Note: Max wrote this at first
module Cubical.Categories.Displayed.Limits.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct
open import Agda.Builtin.Cubical.Equiv
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Foundations.Univalence

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

CartesianCategoryᴰ : CartesianCategory ℓC ℓC' → (ℓ ℓ' : Level) → Type _
CartesianCategoryᴰ CC ℓ ℓ' =
  Σ[ Cᴰ ∈ Categoryᴰ (CC .fst) ℓ ℓ' ]
  {!!} × BinProductsᴰ Cᴰ bps
  where
  bps : BinProducts' (CC .fst)
  bps d = record { vertex = foo .BinProduct.binProdOb

                 ; element = foo .BinProduct.binProdPr₁ , foo .BinProduct.binProdPr₂
                 ; universal = λ A → record { equiv-proof = λ y → ((foo .BinProduct.univProp (y .fst) (y .snd) .fst .fst) , ΣPathP ((foo .BinProduct.univProp (y .fst) (y .snd) .fst .snd .fst) , ((foo .BinProduct.univProp (y .fst) (y .snd) .fst .snd .snd)))) , λ y₁ → {!!} } }
    where
    foo = CC .snd .snd (d .fst) (d .snd)
  -- Terminalᴰ Cᴰ (CC .snd .fst) × BinProductsᴰ Cᴰ (CC .snd .snd)

l : (A B : Type _) → isSet A → isSet B → isSet (A × B)
l A B isSetA isSetB (a , b) (a' , b') p q = {!foobar!}
  where
  foo : a ≡ a'
  foo = λ i → p i .fst
  foo' : a ≡ a'
  foo' = λ i → q i .fst
  bar : b ≡ b'
  bar = λ i → p i .snd
  bar' : b ≡ b'
  bar' = λ i → q i .snd
  baz : foo ≡ foo'
  baz = isSetA a a' foo foo'
  baz' : bar ≡ bar'
  baz' = isSetB b b' bar bar'
  foobar : ((a , b) ≡ (a' , b')) ≡ (a ≡ a') × (b ≡ b')
  foobar = ua ((λ x → (λ i → x i .fst) , (λ i → x i .snd)) , record { equiv-proof = λ y → (p , {!!}) , {!!} })
module _ (C : Category ℓC ℓC') where
  module _ (Γ Δ θ : C .Category.ob) where
    le : (x y : C [ θ , Γ ] × C [ θ , Δ ]) → (p q : x ≡ y) → p ≡ q
    le x y p q = {!!}
  module _ (∃!prod : BinProducts C) where
    module _ (Γ Δ θ : C .Category.ob) where
      lema : (δ : C [ θ , Γ ]) → (δ' : C [ θ , Δ ]) →
        ∃![ f ∈ C [ θ , ∃!prod Γ Δ .BinProduct.binProdOb ] ]
        (f ⋆⟨ C ⟩ (∃!prod Γ Δ .BinProduct.binProdPr₁) ≡ δ) × (f ⋆⟨ C ⟩ (∃!prod Γ Δ .BinProduct.binProdPr₂) ≡ δ')
      lema δ δ' = ∃!prod Γ Δ .BinProduct.univProp δ δ'

      lemmaa : isEquiv (λ (f : C [ θ , ∃!prod Γ Δ .BinProduct.binProdOb ]) → (f ⋆⟨ C ⟩ ∃!prod Γ Δ .BinProduct.binProdPr₁ , f ⋆⟨ C ⟩ ∃!prod Γ Δ .BinProduct.binProdPr₂))
      equiv-proof lemmaa (δ , δ') = (lema δ δ' .fst .fst ,
        ΣPathP (lema δ δ' .fst .snd .fst , lema δ δ' .fst .snd .snd)) ,
        λ f → ΣPathP (congS (λ x → x .fst) (lema δ δ' .snd (f .fst , PathPΣ (f .snd))) , toPathP (isSet→isSet' (le Γ Δ θ) {!!} {!!} {!!} {!!}))

    lemma' : BinProducts' C
    lemma' (Γ , Δ) .UniversalElement.vertex = ∃!prod Γ Δ .BinProduct.binProdOb
    lemma' (Γ , Δ) .UniversalElement.element = ∃!prod Γ Δ .BinProduct.binProdPr₁ , ∃!prod Γ Δ .BinProduct.binProdPr₂
    lemma' (Γ , Δ) .UniversalElement.universal θ = lemmaa Γ Δ θ
