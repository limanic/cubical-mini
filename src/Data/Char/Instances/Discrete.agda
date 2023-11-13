{-# OPTIONS --safe #-}
module Data.Char.Instances.Discrete where

open import Foundations.Base

open import Meta.Search.Discrete

open import Data.Nat.Instances.Discrete

open import Data.Char.Properties

instance
  char-is-discrete : is-discrete Char
  char-is-discrete = is-discrete-injection (char→ℕ , char→ℕ-inj) discrete!
