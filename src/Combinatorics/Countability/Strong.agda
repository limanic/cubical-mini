{-# OPTIONS --safe #-}
module Combinatorics.Countability.Strong where

open import Meta.Prelude
open import Meta.Deriving.HLevel

open import Logic.Discreteness

open import Data.Nat.Path

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  P : A → Type ℓ′
  B : Type ℓ′

record Countable {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  no-eta-equality
  constructor mk-countable
  field enumeration : A ≃ ℕ

open Countable public

unquoteDecl H-Level-countable =
  declare-record-hlevel 2 H-Level-countable (quote Countable)

countable→is-discrete : Countable A → is-discrete A
countable→is-discrete cn = ≃→is-discrete! (enumeration cn)

≃→countable : B ≃ A → Countable A → Countable B
≃→countable e c .enumeration = e ∙ c .enumeration
