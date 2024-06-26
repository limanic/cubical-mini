{-# OPTIONS --safe #-}
module Data.Unit.Instances.Discrete where

open import Foundations.Base

open import Logic.Discreteness

open import Data.Dec.Base
open import Data.Unit.Base

instance
  ⊤-is-discrete : is-discrete ⊤
  ⊤-is-discrete = yes refl
  {-# OVERLAPPING ⊤-is-discrete #-}
