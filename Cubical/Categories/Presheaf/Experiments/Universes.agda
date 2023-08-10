module Cubical.Categories.Presheaf.Experiments.Universes where

-- A presheaf over a category, but valued in Type ℓ rather than hSet ℓ
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Slice
open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

open Category

record Presheaf (C : Category ℓ ℓ') (ℓ'' : Level) : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-suc ℓ''))) where
  field
    X   : C .ob → Type ℓ''
    act : ∀ {c} {c'} → X c → C [ c' , c ] → X c'
    act-id : ∀ c → (x : X c) → act x (C .id) ≡ x
    act-comp : ∀ c c' c'' → (x : X c)(f : C [ c' , c ])(g : C [ c'' , c' ])
             → act x (f ∘⟨ C ⟩ g) ≡ act (act x f) g
private
  record Presheaf' (C : Category ℓ ℓ') (ℓ'' : Level) : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-suc ℓ''))) where
    field
      X   : C .ob → Type ℓ''
      act : ∀ c c' → X c → C [ c' , c ] → X c'
      act-id : ∀ c → (x : X c) → act _ _ x (C .id) ≡ x
      act-comp : ∀ c c' c'' → (x : X c)(f : C [ c' , c ])(g : C [ c'' , c' ])
             → act _ _ x (f ∘⟨ C ⟩ g) ≡ act _ _ (act _ _ x f) g

  unquoteDecl Presheaf'IsoΣ = declareRecordIsoΣ Presheaf'IsoΣ (quote Presheaf')

open Presheaf

act' : ∀ {C : Category ℓ ℓ'} (P : Presheaf C ℓ'') {c d} (x : P .X d) (f : C [ c , d ])
     → P .X c
act' {C = C} P = P .act

infixr 16 act'
syntax act' P x f  = x ∘p⟨ P ⟩ f

{-# DISPLAY act P c c' x f = x ∘p⟨ P ⟩ f #-}

-- Presheaf≡ : {C : Category ℓ ℓ'} {P Q : Presheaf C ℓ''}
--           → (X≡ : P .X ≡ Q .X)
--           → (act≡ : ∀ {c}{c'}(p : P .X c')(q : Q .X c') → PathP (λ i → X≡ i c') p q → (f : C [ c , c' ]) → PathP (λ i → X≡ i c) (p ∘p⟨ P ⟩ f)  (q ∘p⟨ Q ⟩ f))
--           → (act-id≡ : ∀ {c}{c'}(p : P .X c')(q : Q .X c') → PathP (λ i → X≡ i c') p q → (f : C [ c , c' ]) → PathP (λ i → X≡ i c) (p ∘p⟨ P ⟩ f)  (q ∘p⟨ Q ⟩ f))
--           → P ≡ Q
-- Presheaf≡ 

module _ {C : Category ℓ ℓ'} where
  Groth : (P : Presheaf C ℓ''') → Category {!!} {!!}
  Groth P = {!!}



  record PresheafHom (P : Presheaf C ℓ'') (Q : Presheaf C ℓ''') : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where
    field
      fun : ∀ (c : C .ob) → P .X c → Q .X c
      eqv : ∀ c c' (f : C [ c' , c ]) (p : P .X c)
          → fun _ (p ∘p⟨ P ⟩ f) ≡ (fun _ p) ∘p⟨ Q ⟩ f
  open PresheafHom

  -- Universal Property of 𝓤 ℓ'' is that a homo
  -- A → 𝓤 ℓ'' of presheaves over 𝓒
  -- should be equivalent to a presheaf over ∫ 𝓒 A 

  -- Martin Hofmann, Thomas Streicher, Lifting Grothendieck Universes ,
  -- ms. University of Darmstadt (unpublished).
  -- https://www2.mathematik.tu-darmstadt.de/~streicher/NOTES/lift.pdf
  𝓤 : (ℓ'' : Level) → Presheaf C (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ''))
  𝓤 ℓ'' .X c = Presheaf (SliceCat C c) ℓ''
  𝓤 ℓ'' .act P f .X g = P .X (sliceob (f ∘⟨ C ⟩ g .S-arr))
  𝓤 ℓ'' .act P f .act x g =
    P .act x (slicehom (S-hom g)
      (sym (C .⋆Assoc _ _ _) ∙ cong (comp' C f) (S-comm g)))
  𝓤 ℓ'' .act P f .act-id c₁ x =
    cong (P .act x) (SliceHom-≡-intro' _ _ refl) ∙ P .act-id _ _
  𝓤 ℓ'' .act P f .act-comp c c' c'' x g h =
    cong (P .act x) (SliceHom-≡-intro' _ _ refl)
    ∙ P .act-comp _ _ _ _ _ _
  𝓤 ℓ'' .act-id = {!!}
  𝓤 ℓ'' .act-comp = {!!}

  Δ : (A : Type ℓ'') → Presheaf C ℓ''
  Δ A .X c = A
  Δ A .act = λ z _ → z
  Δ A .act-id = λ c x → refl
  Δ A .act-comp = λ c c' c'' x f g → refl

  -- Σp' : (A : Presheaf C ℓ'') (B : Presheaf {!!} ℓ''') → Presheaf C {!!}
  -- Σp' A = {!!}

  Σp : (A : Presheaf C ℓ'') (B : PresheafHom A (𝓤 ℓ''')) → Presheaf C {!!}
  Σp A B .X c = Σ[ a ∈ A .X c ] {!B .fun c a!}
  Σp A B .act = {!!}
  Σp A B .act-id = {!!}
  Σp A B .act-comp = {!!}

  Π : (A : Presheaf C ℓ'') (B : PresheafHom A (𝓤 ℓ''')) → Presheaf C {!!}
  Π A B .X = {!!}
  Π A B .act = {!!}
  Π A B .act-id = {!!}
  Π A B .act-comp = {!!}
