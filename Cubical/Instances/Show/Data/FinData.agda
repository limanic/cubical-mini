{-# OPTIONS --safe #-}
module Cubical.Instances.Show.Data.FinData where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.FinData.Base
open import Cubical.Data.String.Base

open import Cubical.Instances.Show.Base

private variable
  n : ℕ

instance
  ShowFin : Show (Fin n)
  Show.show ShowFin k = showNat (toℕ k)
