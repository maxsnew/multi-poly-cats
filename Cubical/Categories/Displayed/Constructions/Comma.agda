{-

  The comma category of two functors viewed as a displayed category
  over one or both of the projections.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Comma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Displayed.Constructions.FullSubcategory
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Constructions.BinProduct as BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More as Displayed
open import Cubical.Categories.Displayed.Base.HLevel1Homs
open import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryR
open import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryL
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Preorder
open import Cubical.Categories.Displayed.Constructions.Graph
open import Cubical.Categories.Isomorphism.More

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' : Level

open Category
open Categoryᴰ
open Preorderᴰ
open Functor
open NatTrans

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
         (F : Functor C E) (G : Functor D E) where

  Commaᴰ : Categoryᴰ (C ×C D) ℓE' ℓE'
  Commaᴰ = Graph {C = C} (HomBif E ∘Fl (F ^opF) ∘Fr G)

  hasPropHomsCommaᴰ : hasPropHoms Commaᴰ
  hasPropHomsCommaᴰ = hasPropHomsGraph _

  -- Universal Property: a functor into the comma category is
  -- equivalent to a natural transformation
  Comma : Category _ _
  Comma = ∫C Commaᴰ

  π1 : Functor Comma C
  π1 = BinProduct.Fst C D ∘F Displayed.Fst {Cᴰ = Commaᴰ}

  π2 : Functor Comma D
  π2 = BinProduct.Snd C D ∘F Displayed.Fst {Cᴰ = Commaᴰ}

  π⇒ : NatTrans (F ∘F π1) (G ∘F π2)
  π⇒ .N-ob  = snd
  π⇒ .N-hom = snd

  Commaᴰ₁ : Categoryᴰ C (ℓ-max ℓD ℓE') (ℓ-max ℓD' ℓE')
  Commaᴰ₁ = ∫Cᴰsr Commaᴰ

  IsoCommaᴰ : Categoryᴰ (C ×C D) (ℓ-max ℓE' ℓE') ℓE'
  IsoCommaᴰ = ∫Cᴰ Commaᴰ (FullSubcategoryᴰ _ (λ (_ , f) → isIso E f))

  -- Not following from a gneral result about ∫Cᴰ but works
  hasPropHomsIsoCommaᴰ : hasPropHoms IsoCommaᴰ
  hasPropHomsIsoCommaᴰ {c , d}{c' , d'} f cᴰ cᴰ' =
  -- TODO generalize this as a reasoning principle for ∫Cᴰ
    isPropΣ
      (hasPropHomsCommaᴰ f (cᴰ .fst) (cᴰ' .fst))
      λ x → hasPropHomsFullSubcategory _ _ (f , x) (cᴰ .snd) (cᴰ' .snd)

  IsoComma : Category _ _
  IsoComma = ∫C IsoCommaᴰ

  IsoCommaᴰ₁ : Categoryᴰ C _ _
  IsoCommaᴰ₁ = ∫Cᴰsr IsoCommaᴰ

  IsoCommaᴰ₂ : Categoryᴰ D _ _
  IsoCommaᴰ₂ = ∫Cᴰsl IsoCommaᴰ

  open isIso
  -- Characterization of HLevel of Commaᴰ₁ homs
  private
    module IC₁ = Categoryᴰ IsoCommaᴰ₁
    module _ {c c'}(f : C [ c , c' ])
             (c≅d : IC₁.ob[ c ])
             (c'≅d' : IC₁.ob[ c' ]) where
      AltHom : Type _
      AltHom = fiber (G .F-hom)
        (c≅d .snd .snd .inv ⋆⟨ E ⟩ F .F-hom f ⋆⟨ E ⟩ c'≅d' .snd .fst)

      ICHom = IC₁.Hom[ f ][ c≅d , c'≅d' ]

      Hom→Alt : ICHom → AltHom
      Hom→Alt (g , sq , _) = g ,
        ⋆InvLMove (c≅d .snd) (sym sq) ∙ sym (E .⋆Assoc _ _ _)

      Alt→Hom : AltHom → ICHom
      Alt→Hom (g , sq) = g ,
        sym (⋆InvLMove⁻ (c≅d .snd) (sq ∙ E .⋆Assoc _ _ _)), tt

      AltHomRetr : (x : ICHom) → Alt→Hom (Hom→Alt x) ≡ x
      AltHomRetr _ = Σ≡Prop (λ g' → hasPropHomsIsoCommaᴰ _ _ _) refl

      AltHomProp : isFaithful G → isProp AltHom
      AltHomProp G-faithful = isEmbedding→hasPropFibers
        (injEmbedding (E .isSetHom) (λ {g} {g'} → G-faithful _ _ _ _))
        _

      AltHomContr : isFullyFaithful G → isContr AltHom
      AltHomContr G-ff = G-ff _ _ .equiv-proof _

      HomProp : isFaithful G → isProp ICHom
      HomProp G-faithful =
        isPropRetract Hom→Alt Alt→Hom AltHomRetr (AltHomProp G-faithful)

      HomContr : isFullyFaithful G → isContr ICHom
      HomContr G-ff =
        isContrRetract Hom→Alt Alt→Hom AltHomRetr (AltHomContr G-ff)

  hasPropHomsIsoCommaᴰ₁ : isFaithful G → hasPropHoms IsoCommaᴰ₁
  hasPropHomsIsoCommaᴰ₁ G-faithful f diso diso' =
    HomProp f diso diso' G-faithful

  hasContrHomsIsoCommaᴰ₁ : isFullyFaithful G → hasContrHoms IsoCommaᴰ₁
  hasContrHomsIsoCommaᴰ₁ G-ff f diso diso' = HomContr f diso diso' G-ff

  πⁱ1 : Functor IsoComma C
  πⁱ1 = BinProduct.Fst C D ∘F Displayed.Fst {Cᴰ = IsoCommaᴰ}

  πⁱ2 : Functor IsoComma D
  πⁱ2 = BinProduct.Snd C D ∘F Displayed.Fst {Cᴰ = IsoCommaᴰ}

  π≅ : NatIso (F ∘F πⁱ1) (G ∘F πⁱ2)
  π≅ .NatIso.trans .N-ob (_ , f , _) = f
  π≅ .NatIso.trans .N-hom (_ , sq , _) = sq
  π≅ .NatIso.nIso (_ , _ , isIso) = isIso

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
         (F : Functor C E) (G : Functor D E) where

  private
    module IC₂ = Categoryᴰ (IsoCommaᴰ₂ F G)
    module IC₁ = Categoryᴰ (IsoCommaᴰ₁ G F)
    module _ {d d'}(g : D [ d , d' ])
             (d≅c   : IC₂.ob[ d ])
             (d'≅c' : IC₂.ob[ d' ]) where
      c≅d : IC₁.ob[ d ]
      c≅d = (d≅c .fst) , (invIso (d≅c .snd))
      c'≅d' : IC₁.ob[ d' ]
      c'≅d' = (d'≅c' .fst) , (invIso (d'≅c' .snd))
      IC2Hom = IC₂.Hom[ g ][ d≅c , d'≅c' ]
      IC1Hom = IC₁.Hom[ g ][ c≅d , c'≅d' ]

      isOfHLevelIC2Hom : ∀ n → isOfHLevel n IC1Hom → isOfHLevel n IC2Hom
      isOfHLevelIC2Hom n =
        isOfHLevelRetract n
          -- this proof would be better if it was an iff directly
          (λ (f , sq2 , tt) → f ,
          sym (⋆InvRMove (d'≅c' .snd)
            (E .⋆Assoc _ _ _ ∙ sym (⋆InvLMove (d≅c .snd) (sym sq2))))
          , tt)
          (λ (f , sq1 , tt) → f ,
            sym (⋆InvRMove (c'≅d' .snd)
            (E .⋆Assoc _ _ _ ∙ sym (⋆InvLMove (c≅d .snd) (sym sq1))))
            , tt)
          λ sq2 → Σ≡Prop (λ _ → hasPropHomsIsoCommaᴰ F G _ _ _) refl

  hasPropHomsIsoCommaᴰ₂ : isFaithful F → hasPropHoms (IsoCommaᴰ₂ F G)
  hasPropHomsIsoCommaᴰ₂ F-faithful f diso diso' =
    isOfHLevelIC2Hom _ _ _ 1 (hasPropHomsIsoCommaᴰ₁ G F F-faithful _ _ _)

  hasContrHomsIsoCommaᴰ₂ : isFullyFaithful F → hasContrHoms (IsoCommaᴰ₂ F G)
  hasContrHomsIsoCommaᴰ₂ F-ff f diso diso' =
    isOfHLevelIC2Hom _ _ _ 0 (hasContrHomsIsoCommaᴰ₁ G F F-ff _ _ _)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
         {F : Functor C E} {G : Functor D E}
         {B : Category ℓB ℓB'}
         (H : Functor B C)
         (K : Functor B D)
         (α : NatTrans (F ∘F H) (G ∘F K))
         where
  open Functorᴰ
  mkCommaFunctor : Functor B (Comma F G)
  mkCommaFunctor = mk∫Functor (H ,F K) αF where
    αF : Functorᴰ (H ,F K) _ _
    αF = mkP→CᴰFunctorᴰ _ _ _
      (λ {b} _ → α ⟦ b ⟧ )
      λ {_}{_}{f} _ → α .N-hom f

  mkCommaFunctorβ₁ : (π1 _ _ ∘F mkCommaFunctor) ≡ H
  mkCommaFunctorβ₁ = Functor≡ (λ _ → refl) (λ _ → refl)

  mkCommaFunctorβ₂ : (π2 _ _ ∘F mkCommaFunctor) ≡ K
  mkCommaFunctorβ₂ = Functor≡ (λ _ → refl) (λ _ → refl)

  private
    β⇒-boundary₁ : (F ∘F π1 F G) ∘F mkCommaFunctor ≡ F ∘F H
    β⇒-boundary₁ =
      sym F-assoc
      ∙ cong (F ∘F_) mkCommaFunctorβ₁
    β⇒-boundary₂ : (G ∘F π2 F G) ∘F mkCommaFunctor ≡ G ∘F K
    β⇒-boundary₂ =
      sym F-assoc
      ∙ cong (G ∘F_) mkCommaFunctorβ₂

  -- Morally this hole is refl but it's a PathP so...
  -- mkCommaFunctorβ⇒ :
  --   PathP (λ i → NatTrans (β⇒-boundary₁ i) (β⇒-boundary₂ i))
  --         (π⇒ F G ∘ˡ mkCommaFunctor)
  --         α
  -- mkCommaFunctorβ⇒ = makeNatTransPathP _ _
  --   (funExt (λ x → {!λ i → α ⟦ x ⟧!}))

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
         {F : Functor C E} {G : Functor D E}
         {B : Category ℓB ℓB'}
         (H : Functor B C)
         (K : Functor B D)
         (α : NatIso (F ∘F H) (G ∘F K))
         where
  open NatIso

  mkIsoCommaFunctor : Functor B (IsoComma F G)
  mkIsoCommaFunctor = mk∫Functor (H ,F K)
    (mk∫ᴰFunctorᴰ _ _
      (mkP→CᴰFunctorᴰ _ _ _
       ((λ {b} _ → α .trans ⟦ b ⟧ ))
       λ {_}{_}{f} _ → α .trans .N-hom f)
      (mkP→CᴰFunctorᴰ _ _ _
       (λ x → α .nIso _)
       λ x → _))
