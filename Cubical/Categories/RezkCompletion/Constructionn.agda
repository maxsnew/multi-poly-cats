{-

The Constructionn (sic) of Rezk Completion

-}
{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.RezkCompletion.Constructionn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Constructions.EssentialImage
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Yoneda

open import Cubical.Categories.RezkCompletion.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

open isWeakEquivalence


-- There are two different ways to construct the Rezk completion,
-- one is using the essential image of the Yoneda embbeding,
-- another one is using a higher inductive type
-- (c.f. HoTT Book Chaper 9.9).

-- Yoneda embbeding can give a very simple and quick construction.
-- Unfortunately, this construction increases the universe level.

-- The HIT construction, on the other hand, keeps the universe level,
-- but its proof is a bit long and tedious, still easy though.


{- The Construction by Yoneda Embedding -}

module RezkByYoneda (C : Category ℓ ℓ) where

  YonedaImage : Category (ℓ-suc ℓ) ℓ
  YonedaImage = EssentialImage (YO {C = C})

  isUnivalentYonedaImage : isUnivalent YonedaImage
  isUnivalentYonedaImage = isUnivalentEssentialImage _ isUnivalentPresheafCategory

  ToYonedaImage : Functor C YonedaImage
  ToYonedaImage = ToEssentialImage _

  isWeakEquivalenceToYonedaImage : isWeakEquivalence ToYonedaImage
  isWeakEquivalenceToYonedaImage .fullfaith = isFullyFaithfulToEssentialImage _ isFullyFaithfulYO
  isWeakEquivalenceToYonedaImage .esssurj   = isEssentiallySurjToEssentialImage YO

  isRezkCompletionToYonedaImage : isRezkCompletion ToYonedaImage
  isRezkCompletionToYonedaImage = makeIsRezkCompletion isUnivalentYonedaImage isWeakEquivalenceToYonedaImage


{- The Construction by Higher Inductive Type -}

module RezkByHIT (C : Category ℓ ℓ') where
  module C = Category C
  -- TODO: Write the HIT construction of Rezk completion here.
  data Ĉ₀ : Type (ℓ-max ℓ ℓ') where -- TODO: is this the best we can do w/ the levels?
    [_] : (C.ob) → Ĉ₀
    iso// : {a b : C.ob}(e : CatIso C a b) → [ a ] ≡ [ b ]
    id// : {a : C.ob} → iso// {a} idCatIso ≡ refl
    -- | copied this from HITs.GroupoidQuotients
    -- | Equivalent to the original but stated in terms of PathP
    -- | instead of path composition
    comp// : ∀ {a b c} → (e : CatIso C a b) → (e' : CatIso C b c)
          → PathP (λ j → [ a ] ≡ iso// e' j)
                  (iso// e)
                  (iso// (⋆Iso e e'))
    -- comp// : {a b c : C .ob}(f : CatIso C a b)(g : CatIso C b c)
    --       → iso// (⋆Iso f g) ≡ iso// f ∙ iso// g
    squash// : isGroupoid Ĉ₀

  -- -- the paragraph directly following the HIT definition, below theorem 9.9.5 of the HOTT book
  -- _ : (a b : C .ob)(p : a ≡ b) → j (pathToIso p) ≡ congS i p
  -- _ = λ a b p → J (λ y → λ eq → j (pathToIso eq) ≡ congS i eq) (j (pathToIso refl) ≡⟨ congS j pathToIso-refl ⟩ j idCatIso ≡⟨ jid ⟩ congS i refl ∎) p -- TODO: I don't really get this proof and why we want this theorem

  open import Cubical.Foundations.Isomorphism
  open import Cubical.Categories.Category.Base
  open Cubical.Categories.Category.isIso
  open import Cubical.Foundations.Univalence
  open import Cubical.Foundations.Equiv

  elim : {P : Ĉ₀ → Type ℓ''}
       → (∀ ĉ → isGroupoid (P ĉ))
       → (f-[_] : ∀ c → P [ c ])
       → (f-iso// : ∀ {a b} (e : CatIso C a b)
                  → PathP (λ i → P (iso// e i)) (f-[ a ]) (f-[ b ]))
       → (f-id// : ∀ {a} →
                     SquareP (λ i j → P (id// {a} i j))
                       ((f-iso// {a} idCatIso))
                       refl
                       (λ j → f-[ a ])
                       (cong f-[_] refl))
       → (f-comp// : ∀ {a b c} (e : CatIso C a b)(e' : CatIso C b c)
                     → SquareP (λ i j → P (comp// e e' i j))
                               (f-iso// e)
                               (f-iso// (⋆Iso e e'))
                               (λ j → f-[ a ])
                               (f-iso// e'))
       → ∀ ĉ → P ĉ
  elim isGroupoidP f-[_] f-iso// f-id// f-comp// [ c ] = f-[ c ]
  elim isGroupoidP f-[_] f-iso// f-id// f-comp// (iso// e i) = f-iso// e i
  elim isGroupoidP f-[_] f-iso// f-id// f-comp// (id// i j) = f-id// i j
  elim isGroupoidP f-[_] f-iso// f-id// f-comp// (comp// f g i j) = f-comp// f g i j
  elim isGroupoidP f-[_] f-iso// f-id// f-comp// (squash// ĉ ĉ' p p' q q' i j k) =
    isOfHLevel→isOfHLevelDep 3 isGroupoidP
      _ _ _ _ (λ j k → elimm (q j k)) (λ j k → elimm (q' j k)) (squash// ĉ ĉ' p p' q q') i j k where
      elimm = elim isGroupoidP f-[_] f-iso// f-id// f-comp//

  ĈHom : Ĉ₀ → Ĉ₀ → hSet ℓ'
  ĈHom = elim isGrpdFam ĈHomc    
    {!!}
    {!!}
    {!!} where
    ĈHomc : C.ob → Ĉ₀ → hSet ℓ'
    ĈHomc a = elim (λ _ → isGroupoidHSet)
      (λ b → C.Hom[ a , b ] , C.isSetHom)
      (λ {b c} e → 
        -- This follows from univalence of Set:
        -- e : b ≅ c
        -- C [ a ,-] ⟪ e ⟫ : C [ a , b ] ≅ C [ a , c ]
        -- C [ a , b ] ≡ C [ a , c ]
        isUnivalent.CatIsoToPath isUnivalentSET
        (F-Iso {F = C [ a ,-]} e))
      {!!}
      {!!}
    
    isGrpdFam : (ĉ : Ĉ₀) → isGroupoid (Ĉ₀ → hSet ℓ')
    isGrpdFam _ = isGroupoidΠ (λ _ → isGroupoidHSet)
  -- Ĉ₁ : Ĉ₀ → Ĉ₀ → Type _
  -- Ĉ₁ (i a) (i b) = (C [ a , b ])
  -- Ĉ₁ (i a) (j {b} {b'} e i') = ua (isoToEquiv (iso iso→ iso⁻¹← (λ g → iso→ (iso⁻¹← g) ≡⟨ refl ⟩ g ⋆⟨ C ⟩ e⁻¹← ⋆⟨ C ⟩ e→ ≡⟨ C .⋆Assoc g e⁻¹← e→ ⟩ g ⋆⟨ C ⟩ (e⁻¹← ⋆⟨ C ⟩ e→)  ≡⟨ congS (λ eq → g ⋆⟨ C ⟩ eq) (e .snd .sec) ⟩ g ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR g ⟩ g ∎) (λ f → iso⁻¹← (iso→ f) ≡⟨ refl ⟩ f ⋆⟨ C ⟩ e→ ⋆⟨ C ⟩ e⁻¹← ≡⟨ C .⋆Assoc f e→ e⁻¹← ⟩ f ⋆⟨ C ⟩ (e→ ⋆⟨ C ⟩ e⁻¹←) ≡⟨ congS (λ eq → f ⋆⟨ C ⟩ eq) (e .snd .ret) ⟩ f ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR f ⟩ f ∎ ))) i'
  -- -- isoToPath (iso iso→ iso⁻¹← (λ g → iso→ (iso⁻¹← g) ≡⟨ refl ⟩ g ⋆⟨ C ⟩ e⁻¹← ⋆⟨ C ⟩ e→ ≡⟨ C .⋆Assoc g e⁻¹← e→ ⟩ g ⋆⟨ C ⟩ (e⁻¹← ⋆⟨ C ⟩ e→)  ≡⟨ congS (λ eq → g ⋆⟨ C ⟩ eq) (e .snd .sec) ⟩ g ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR g ⟩ g ∎) (λ f → iso⁻¹← (iso→ f) ≡⟨ refl ⟩ f ⋆⟨ C ⟩ e→ ⋆⟨ C ⟩ e⁻¹← ≡⟨ C .⋆Assoc f e→ e⁻¹← ⟩ f ⋆⟨ C ⟩ (e→ ⋆⟨ C ⟩ e⁻¹←) ≡⟨ congS (λ eq → f ⋆⟨ C ⟩ eq) (e .snd .ret) ⟩ f ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR f ⟩ f ∎ )) i'
  --   where
  --   e→ = e .fst
  --   e⁻¹← = e .snd .inv
  --   -- let f ∈ C [ a , b ], g ∈ C [ a , b' ]
  --   -- explicit types to manually supply contraints
  --   iso→ : C [ a , b ] → C [ a , b' ]
  --   iso→ f = f ⋆⟨ C ⟩ e→
  --   iso⁻¹← : C [ a , b' ] → C [ a , b ]
  --   iso⁻¹← g = g ⋆⟨ C ⟩ e⁻¹←
  -- Ĉ₁ (i a) (jid {b} i' i'') = ( proof⋆id ≡⟨ congS ua (equivEq (funExt λ f → C .⋆IdR f)) ⟩ ua (idEquiv (C [ a , b ])) ≡⟨ uaIdEquiv ⟩ refl-hom ∎) i' i''
  --   where
  --   iso→ : C [ a , b ] → C [ a , b ]
  --   iso→ f = f ⋆⟨ C ⟩ (C .id)
  --   iso⁻¹← : C [ a , b ] → C [ a , b ]
  --   iso⁻¹← g = g ⋆⟨ C ⟩ (C .id)
  --   proof⋆id : C [ a , b ] ≡ C [ a , b ]
  --   proof⋆id = ua (isoToEquiv (iso iso→ iso⁻¹← (λ g → iso→ (iso⁻¹← g) ≡⟨ refl ⟩ g ⋆⟨ C ⟩ C .id ⋆⟨ C ⟩ C .id ≡⟨ C .⋆Assoc g (C .id) (C .id) ⟩ g ⋆⟨ C ⟩ (C .id ⋆⟨ C ⟩ C .id) ≡⟨ congS (λ eq → g ⋆⟨ C ⟩ eq) (C .⋆IdL (C .id)) ⟩ g ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR g ⟩ g ∎ ) (λ f → iso⁻¹← (iso→ f) ≡⟨ refl ⟩ f ⋆⟨ C ⟩ C .id ⋆⟨ C ⟩ C .id ≡⟨ C .⋆Assoc f (C .id) (C .id) ⟩ f ⋆⟨ C ⟩ (C .id ⋆⟨ C ⟩ C .id) ≡⟨ congS (λ eq → f ⋆⟨ C ⟩ eq) (C .⋆IdL (C .id)) ⟩ f ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR f ⟩ f ∎)))
  --   refl-hom : C [ a , b ] ≡ C [ a , b ]
  --   refl-hom = refl
  -- --Ĉ₁ (i a) (jcomp {b} {c} {d} f g i' i'') = {!!}
  -- --Ĉ₁ (j {a} {a'} e i') (i b) = {!!}
