{-# OPTIONS --safe #-}
module Data.Fin.Instances.Number where

open import Foundations.Base

open import Meta.Literals public

open import Data.Nat.Instances.Number public
open import Data.Nat.Order            public

open import Data.Fin.Base

instance
  Number-Fin : ∀ {n} → Number (Fin n)
  Number-Fin {n} .Number.Constraint m = m < n
  Number-Fin {n} .Number.fromNat m ⦃ (e) ⦄ = go m n e where
    go : ∀ k n → k < n → Fin n
    go zero    (suc n) _       = fzero
    go (suc k) (suc n) (s≤s e) = fsuc (go k n e)
