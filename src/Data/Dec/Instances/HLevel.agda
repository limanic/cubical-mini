{-# OPTIONS --safe #-}
module Data.Dec.Instances.HLevel where

open import Foundations.Base

open import Meta.HLevel

open import Data.List.Base

open import Data.Dec.Path

private variable
  ℓ : Level
  A : Type ℓ
  n : HLevel

instance
  decomp-dec : hlevel-decomposition (Dec A)
  decomp-dec = decomp (quote dec-is-of-hlevel) (`level ∷ `search ∷ [])
