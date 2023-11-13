{-# OPTIONS --safe #-}
module Data.FinSum.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Dec.Base as Dec
open import Data.Nat.Base
open import Data.Sum.Path

open import Data.FinSum.Base

instance
  fin-is-discrete : ∀ {n} → is-discrete (Fin n)
  fin-is-discrete = is-discrete-η go where
    go : ∀ {n} (k l : Fin n) → Dec (k ＝ l)
    go {suc n} fzero    fzero    = yes refl
    go {suc n} fzero    (fsuc l) = no ⊎-disjoint
    go {suc n} (fsuc k) fzero    = no λ p → ⊎-disjoint (sym p)
    go {suc n} (fsuc k) (fsuc l) =
      Dec.map (ap fsuc) (λ ¬p p → ¬p (inr-inj p)) (go k l)
