{-# OPTIONS --safe #-}
module Foundations.Pi.Base where

open import Foundations.Prim.Kan
open import Foundations.Prim.Type

open import Foundations.Correspondences.Binary.Reflexive
open import Foundations.Correspondences.Binary.Transitive
open import Foundations.Sigma.Base

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ ℓᶜ : Level

infixr 6 Π-syntax
Π-syntax : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
Π-syntax A B = (x : A) → B x
{-# INLINE Π-syntax #-}

syntax Π-syntax A (λ x → B) = Π[ x ꞉ A ] B

infixr 6 Πᴱ-syntax
Πᴱ-syntax : (A : Type ℓ) (B : @0 A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
Πᴱ-syntax A B = (@0 x : A) → B x
{-# INLINE Πᴱ-syntax #-}

syntax Πᴱ-syntax A (λ x → B) = Πᴱ[ x ꞉ A ] B

infixr 6 ∀-syntax
∀-syntax : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∀-syntax A B = {x : A} → B x
{-# INLINE ∀-syntax #-}

syntax ∀-syntax A (λ x → B) = ∀[ x ꞉ A ] B

infixr 6 ∀ᴱ-syntax
∀ᴱ-syntax : (A : Type ℓ) (B : @0 A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∀ᴱ-syntax A B = {@0 x : A} → B x
{-# INLINE ∀ᴱ-syntax #-}

syntax ∀ᴱ-syntax A (λ x → B) = ∀ᴱ[ x ꞉ A ] B


-- non-dependent stuff

module _ where
  private variable
    A : Type ℓᵃ
    B : Type ℓᵇ
    C : Type ℓᶜ

  Fun : (A : Type ℓᵃ) (B : Type ℓᵇ) → Type (ℓᵃ ⊔ ℓᵇ)
  Fun A B = A → B

  flip : {C : A → B → Type ℓᶜ} → (∀ a b → C a b) → (∀ b a → C a b)
  flip f b a = f a b
  {-# INLINE flip #-}

  flipˢ : (A → B → C) → (B → A → C)
  flipˢ f b a = f a b
  {-# INLINE flipˢ #-}

  const : A → @0 B → A
  const x _ = x
  {-# INLINE const #-}

  id : A → A
  id x = x
  {-# INLINE id #-}

  infixr 9 _∘ₜˢ_
  _∘ₜˢ_ : (B → C) → (A → B) → (A → C)
  (g ∘ₜˢ f) x = g (f x)
  {-# INLINE _∘ₜˢ_ #-}

instance
  Refl-Fun : Refl (Fun {ℓ})
  Refl-Fun .refl = id

  Trans-Fun : Trans (Fun {ℓᵃ} {ℓᵇ}) (Fun {ℓᵇ = ℓᶜ}) Fun
  Trans-Fun ._∙_ f g = g ∘ₜˢ f


-- dependent stuff

module _ where

  private variable
    A : Type ℓᵃ
    B : A → Type ℓᵇ
    C : (a : A) → B a → Type ℓᶜ

  infixr -1 _$_
  _$_ : (f : (a : A) → B a) (x : A) → B x
  f $ a = f a
  {-# INLINE _$_ #-}

  infixl -1 _&_
  _&_ : (x : A) (f : (a : A) → B a) → B x
  a & f = f a
  {-# INLINE _&_ #-}

  infixr 9 _∘_
  _∘_ : (g : {a : A} (b : B a) → C a b)
        (f : (a : A) → B a)
        (x : A)
      → C x (f x)
  (g ∘ f) x = g (f x)
  {-# INLINE _∘_ #-}

  infixr -1 _$ₛ_
  _$ₛ_ : {B : A → SSet ℓᵇ}
         (f : (a : A) → B a) (x : A) → B x
  f $ₛ x = f x
  {-# INLINE _$ₛ_ #-}

  case_return_of_ : (x : A) (B : A → Type ℓᵇ) (f : (a : A) → B a) → B x
  case x return P of f = f x
  {-# INLINE case_return_of_ #-}

  case_of_ : (x : A) (f : (a : A) → B a) → B x
  case x of f = f x
  {-# INLINE case_of_ #-}

  implicit : ((a : A) → B a) → ({x : A} → B x)
  implicit f {x} = f x

  explicit : ({a : A} → B a) → ((x : A) → B x)
  explicit f x = f {x}

is-contrᴱ : ∀ {ℓ} → Type ℓ → Type ℓ
is-contrᴱ A = Σ[ x ꞉ A ] Erased (Π[ y ꞉ A ] (x ＝ y))

is-equivᴱ : {A : Type ℓ} {B : Type ℓ′} (f : A → B) → Type _
is-equivᴱ {B} f = Π[ b ꞉ B ] is-contrᴱ (fibreᴱ f b)
