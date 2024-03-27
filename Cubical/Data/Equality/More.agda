{-# OPTIONS --safe #-}
module Cubical.Data.Equality.More where

open import Cubical.Foundations.Prelude
  using (Type; Level; ℓ-zero; ℓ-suc; ℓ-max; Σ; Σ-syntax; _,_)


-- Import the builtin equality type defined as an inductive family
open import Agda.Builtin.Equality

private
 variable
  a b ℓ ℓ' : Level
  A : Type a
  B : Type b
  x y z : A
open import Cubical.Data.Equality.Base

HEq : {A0 A1 : Type ℓ}(Aeq : A0 ≡ A1) (a0 : A0)(a1 : A1) → Type _
HEq Aeq a0 a1 = transport (λ A → A) Aeq a0 ≡ a1

singlP : {A0 A1 : Type ℓ}(Aeq : A0 ≡ A1) (a : A0) → Type _
singlP {A1 = A1} Aeq a = Σ[ x ∈ A1 ] HEq Aeq a x

singl : {A : Type ℓ}(a : A) → Type _
singl {A = A} a = singlP refl a
