{-# OPTIONS --safe --no-exact-split #-}
module Structures.FinOrd where

open import Meta.Prelude
open import Meta.Projection
open import Meta.Record
open import Meta.Reflection.Base

open import Combinatorics.Finiteness.Bishop.Manifest

open import Data.Bool.Base
open import Data.Fin.Computational.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Reflection.Argument

private variable
  ℓ : Level
  A : Type ℓ

record FinOrd (ℓ : Level) : Type (ℓsuc ℓ) where
  no-eta-equality
  constructor fin-ord
  field
    carrier : Type ℓ
    has-manifest-bishop-finite : Manifest-bishop-finite carrier

open FinOrd

unquoteDecl fin-ord-iso = declare-record-iso fin-ord-iso (quote FinOrd)

instance
  Underlying-FinOrd : Underlying (FinOrd ℓ)
  Underlying-FinOrd {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-FinOrd .⌞_⌟⁰ = carrier

FinOrd≃ᴱℕ : FinOrd ℓ ≃ᴱ ℕ
FinOrd≃ᴱℕ {ℓ} =
  FinOrd ℓ                                       ~⟨ ≃→≃ᴱ (≅→≃ fin-ord-iso) ⟩
  Σ[ X ꞉ 𝒰 ℓ ] Manifest-bishop-finite X         ~⟨ ≃→≃ᴱ (Σ-ap-snd (λ _ → ≅→≃ manifest-bishop-finite-iso)) ⟩
  Σ[ X ꞉ 𝒰 ℓ ] Σ[ n ꞉ ℕ ] (X ≃ Fin n)           ~⟨ ≃→≃ᴱ (Σ-ap-snd (λ _ → Σ-ap-snd λ _ → inv-≃ ∙ whisker-lₑ (lift≃id ⁻¹))) ⟩
  Σ[ X ꞉ 𝒰 ℓ ] Σ[ n ꞉ ℕ ] (Lift ℓ (Fin n) ≃ X)  ~⟨ ≃→≃ᴱ Σ-swap ⟩
  Σ[ n ꞉ ℕ ] Σ[ X ꞉ 𝒰 ℓ ] (Lift ℓ (Fin n) ≃ X)  ~⟨ Σ-contract-sndᴱ (λ n → equiv-is-contrᴱ _) ⟩
  ℕ                                              ∎

instance
  @0 H-Level-FinOrd : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → H-Level n (FinOrd ℓ)
  H-Level-FinOrd ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $ ≃→is-of-hlevel! 2 (equivᴱ≃equiv $ FinOrd≃ᴱℕ)
  {-# OVERLAPPING H-Level-FinOrd #-}

  mbf-proj-fin-ord : Struct-proj-desc false (quote carrier)
  mbf-proj-fin-ord .Struct-proj-desc.has-level = quote has-manifest-bishop-finite
  mbf-proj-fin-ord .Struct-proj-desc.get-argument (_ ∷ x v∷ []) = pure x
  mbf-proj-fin-ord .Struct-proj-desc.get-argument _ = type-error []

  mbf-projection
    : ∀ {ℓ} {A : Type ℓ}
    → {@(tactic struct-proj A nothing) A-mbf : Manifest-bishop-finite A}
    → Manifest-bishop-finite A
  mbf-projection {A-mbf} = A-mbf
  {-# OVERLAPS mbf-projection #-}


-- Usage
module _ {ℓᵃ ℓᵇ : Level} {A : FinOrd ℓᵃ} {B : A →̇ FinOrd ℓᵇ} where private
  open import Meta.Ord
  open import Logic.Discreteness
  open import Logic.Exhaustibility
  open import Logic.Omniscience

  _ : is-groupoid (A →̇ A)
  _ = hlevel 3

  _ : is-discrete (A ×̇ A)
  _ = auto

  _ : Manifest-bishop-finite (A →̇ A →̇ A)
  _ = auto

  _ : Omniscient Π[ B ]
  _ = autoω

  _ : Omniscient₁ (A ×̇ Π[ B ])
  _ = autoω

  _ : Exhaustible (A ×̇ A)
  _ = autoω
