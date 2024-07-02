{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma hiding (_×_)
import Cubical.Data.Sigma as Σ

open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Constructions.Weaken as Wk

private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ (Q : ×Quiver ℓQ ℓQ') where
  open ProductQuiver
  private module Q = ×QuiverNotation Q
  data Exp : Q.Ob → Q.Ob → Type (ℓ-max ℓQ ℓQ') where
    ↑ₑ_ : ∀ t → Exp (Q.Dom t) (Q.Cod t)
    idₑ : ∀{Γ} → Exp Γ Γ
    _⋆ₑ_ : ∀{Γ Γ' Γ''}(δ : Exp Γ Γ') → (δ' : Exp Γ' Γ'') →  Exp Γ Γ''
    ⋆ₑIdL : ∀{Γ Δ}(δ : Exp Γ Δ) → idₑ ⋆ₑ δ ≡ δ
    ⋆ₑIdR : ∀{Γ Δ}(δ : Exp Γ Δ) → δ ⋆ₑ idₑ ≡ δ
    ⋆ₑAssoc : ∀{Γ Γ' Γ'' Γ'''}
      (δ : Exp Γ Γ')(δ' : Exp Γ' Γ'')(δ'' : Exp Γ'' Γ''')
      → (δ ⋆ₑ δ') ⋆ₑ δ'' ≡ δ ⋆ₑ (δ' ⋆ₑ δ'')
    isSetExp : ∀{Γ Γ'} → isSet (Exp Γ Γ')
    !ₑ : ∀{Γ} → Exp Γ ⊤
    ⊤η : ∀{Γ}(t : Exp Γ ⊤) → t ≡ !ₑ
    π₁ : ∀{Γ Δ} → Exp (Γ × Δ) Γ
    π₂ : ∀{Γ Δ} → Exp (Γ × Δ) Δ
    ⟨_,_⟩ : ∀{Γ Δ Δ'} → Exp Γ Δ → Exp Γ Δ' → Exp Γ (Δ × Δ')
    ×β₁ : ∀{Γ Δ Δ'}{t : Exp Γ Δ}{t' : Exp Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₁ ≡ t
    ×β₂ : ∀{Γ Δ Δ'}{t : Exp Γ Δ}{t' : Exp Γ Δ'} → ⟨ t , t' ⟩ ⋆ₑ π₂ ≡ t'
    ×η : ∀{Γ Δ Δ'}{t : Exp Γ (Δ × Δ')} → t ≡ ⟨ t ⋆ₑ π₁ , t ⋆ₑ π₂ ⟩

  open Category
  |FreeCartesianCategory| : Category _ _
  |FreeCartesianCategory| .ob = Q.Ob
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
  FreeCartesianCategory .snd .snd Γ Δ .BinProduct.univProp f g = uniqueExists
    ⟨ f , g ⟩
    (×β₁ , ×β₂)
    (λ _ → isProp× (isSetExp _ _) (isSetExp _ _))
    λ ⟨f,g⟩' (comm₁ , comm₂) → cong₂ ⟨_,_⟩ (sym comm₁) (sym comm₂) ∙ sym ×η

  module _
    (CCᴰ : CartesianCategoryᴰ FreeCartesianCategory ℓCᴰ ℓCᴰ')
    where
    private
      Cᴰ = CCᴰ .fst
      module Cᴰ = Categoryᴰ Cᴰ
      termᴰ = CCᴰ .snd .fst
      bpᴰ = CCᴰ .snd .snd
      open LiftedTerminalNotation _ termᴰ
      open LiftedBinProductsNotation bpᴰ
    open UniversalElementᴰ
    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elim-F-ob : ∀ c → Cᴰ.ob[ c ]
      elim-F-ob (↑ o)     = ı-ob o
      elim-F-ob ⊤         = 𝟙ᴰ
      elim-F-ob (c₁ × c₂) = elim-F-ob c₁ ×ᴰ elim-F-ob c₂

      module _ (ı-hom : ∀ e →
        Cᴰ.Hom[ ↑ₑ e ][ elim-F-ob (Q.Dom e) , elim-F-ob (Q.Cod e) ])
        where
        open Section
        private
          module R = HomᴰReasoning Cᴰ

        elim-F-hom : ∀ {c c'} (f : |FreeCartesianCategory| [ c , c' ]) →
          Cᴰ [ f ][ elim-F-ob c , elim-F-ob c' ]
        elim-F-hom (↑ₑ t) = ı-hom t
        elim-F-hom idₑ = Cᴰ.idᴰ
        elim-F-hom (f ⋆ₑ g) = elim-F-hom f Cᴰ.⋆ᴰ elim-F-hom g
        elim-F-hom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elim-F-hom f) i
        elim-F-hom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elim-F-hom f) i
        elim-F-hom (⋆ₑAssoc f g h i) =
          Cᴰ.⋆Assocᴰ (elim-F-hom f) (elim-F-hom g) (elim-F-hom h) i
        elim-F-hom (isSetExp f g p q i j) =
          isOfHLevel→isOfHLevelDep 2 (λ _ → Cᴰ.isSetHomᴰ)
          (elim-F-hom f) (elim-F-hom g)
          (cong elim-F-hom p) (cong elim-F-hom q)
          (isSetExp f g p q)
          i j
        elim-F-hom !ₑ = !tᴰ _
        -- TODO: Why does this need rectify?
        elim-F-hom (⊤η f i) =
          R.≡[]-rectify {p' = ⊤η f} (𝟙ηᴰ (elim-F-hom f)) i
        elim-F-hom π₁ = π₁ᴰ
        elim-F-hom π₂ = π₂ᴰ
        elim-F-hom ⟨ f₁ , f₂ ⟩ = elim-F-hom f₁ ,pᴰ elim-F-hom f₂
        elim-F-hom (×β₁ {t = f₁}{t' = f₂} i) =
          ×β₁ᴰ {f₁ᴰ = elim-F-hom f₁} {f₂ᴰ = elim-F-hom f₂} i
        elim-F-hom (×β₂ {t = f₁}{t' = f₂} i) =
          ×β₂ᴰ {f₁ᴰ = elim-F-hom f₁} {f₂ᴰ = elim-F-hom f₂} i
        -- TODO: Why do we need this rectify too?
        elim-F-hom (×η {t = f} i) =
          R.≡[]-rectify {p' = ×η {t = f}} (×ηᴰ {fᴰ = elim-F-hom f}) i

        elim : GlobalSection Cᴰ
        elim .F-obᴰ = elim-F-ob
        elim .F-homᴰ = elim-F-hom
        elim .F-idᴰ = refl
        elim .F-seqᴰ _ _ = refl

  module _
    {D : Category ℓD ℓD'}
    {F : Functor |FreeCartesianCategory| D}
    {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    where
    module _
      (lt : LiftedTerminal (reindex Dᴰ F)
        (terminalToUniversalElement (FreeCartesianCategory .snd .fst)))
      (lbp : LiftedBinProducts (reindex Dᴰ F)
        (BinProductsToBinProducts' _ (FreeCartesianCategory .snd .snd)))
      where
      private
        module Dᴰ = Categoryᴰ Dᴰ
        CCᴰ : CartesianCategoryᴰ _ ℓDᴰ ℓDᴰ'
        CCᴰ = reindex Dᴰ F , (lt , lbp)
      module _
        (ϕ : (o : Q .fst) → Dᴰ.ob[ F ⟅ ↑ o ⟆ ])
        (ψ : (e : Q .snd .mor) →
               Dᴰ.Hom[ F ⟪ ↑ₑ e ⟫ ][
               elim-F-ob CCᴰ ϕ (Q.Dom e) ,
               elim-F-ob CCᴰ ϕ (Q.Cod e)
               ])
        where
        elimLocal' : Section F Dᴰ
        elimLocal' = GlobalSectionReindex→Section Dᴰ F (elim CCᴰ ϕ ψ)

    module _
      (vt : VerticalTerminalAt Dᴰ (F ⟅ ⊤ ⟆))
      (lift-π₁₂ : {c c' : Q.Ob}
        (Fcᴰ : Categoryᴰ.ob[ Dᴰ ] (F ⟅ c ⟆))
        (Fc'ᴰ : Categoryᴰ.ob[ Dᴰ ] (F ⟅ c' ⟆)) →
        (CartesianOver Dᴰ Fcᴰ (F ⟪ π₁ ⟫) Σ.×
        CartesianOver Dᴰ Fc'ᴰ (F ⟪ π₂ ⟫)))
      (∧ : {c c' : Q.Ob}
        (Fcᴰ : Categoryᴰ.ob[ Dᴰ ] (F ⟅ c ⟆))
        (Fc'ᴰ : Categoryᴰ.ob[ Dᴰ ] (F ⟅ c' ⟆)) →
        VerticalBinProductsAt Dᴰ
          (lift-π₁₂ Fcᴰ Fc'ᴰ .fst .CartesianOver.f*cᴰ' ,
          lift-π₁₂ Fcᴰ Fc'ᴰ .snd .CartesianOver.f*cᴰ'))
      where
      private
        module Dᴰ = Categoryᴰ Dᴰ
        lt : LiftedTerminal (reindex Dᴰ F)
            (terminalToUniversalElement (FreeCartesianCategory .snd .fst))
        lt = LiftedTerminalReindex vt
        lbp : LiftedBinProducts (reindex Dᴰ F)
            (BinProductsToBinProducts' _ (FreeCartesianCategory .snd .snd))
        lbp = LiftedBinProdsReindex
          (BinProductsToBinProducts' _ (FreeCartesianCategory .snd .snd))
          lift-π₁₂ ∧
        CCᴰ : CartesianCategoryᴰ _ ℓDᴰ ℓDᴰ'
        CCᴰ = reindex Dᴰ F , (lt , lbp)
      module _
        (ϕ : (o : Q .fst) → Dᴰ.ob[ F ⟅ ↑ o ⟆ ])
        (ψ : (e : Q .snd .mor) →
          Dᴰ.Hom[ F ⟪ ↑ₑ e ⟫ ][
            elim-F-ob CCᴰ ϕ (Q.Dom e) ,
            elim-F-ob CCᴰ ϕ (Q.Cod e)
          ]) where
        elimLocal : Section F Dᴰ
        elimLocal = elimLocal' lt lbp ϕ ψ

  module _ (CC : CartesianCategory ℓC ℓC')
    (ϕ : (o : Q .fst) → CC .fst .ob)
    where
    ϕ* : Q.Ob → CC .fst .ob
    ϕ* = elim-F-ob
      (weaken |FreeCartesianCategory| (CC .fst) ,
      termWeaken (terminalToUniversalElement (FreeCartesianCategory .snd .fst))
        (terminalToUniversalElement (CC .snd .fst)) ,
      binprodWeaken
        (BinProductsToBinProducts' _ (FreeCartesianCategory .snd .snd))
        (BinProductsToBinProducts' _ (CC .snd .snd)))
      ϕ
    module _ (ψ : (e : Q .snd .mor) →
      CC .fst [
        ϕ* (Q.Dom e) ,
        ϕ* (Q.Cod e)
      ])
      where
      rec : Functor |FreeCartesianCategory| (CC .fst)
      rec = introS⁻ (elim
        ((weaken |FreeCartesianCategory| (CC .fst)) ,
          termWeaken _ (terminalToUniversalElement (CC .snd .fst)) ,
          binprodWeaken
            (BinProductsToBinProducts' _ (FreeCartesianCategory .snd .snd))
            (BinProductsToBinProducts' _ (CC .snd .snd)))
        ϕ ψ)
