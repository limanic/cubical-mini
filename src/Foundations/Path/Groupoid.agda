{-# OPTIONS --safe #-}
module Foundations.Path.Groupoid where

open import Foundations.Base
open import Foundations.Transport

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  w x y z : A

opaque
  unfolding _∙_

  ∙-id-l : (p : x ＝ y) → refl ∙ p ＝ p
  ∙-id-l p = sym (∙-filler-r refl p)

  ∙-id-r : (p : x ＝ y) → p ∙ refl ＝ p
  ∙-id-r p = sym (∙-filler-l p refl)

  ∙-assoc : (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
          → p ∙ (q ∙ r) ＝ (p ∙ q) ∙ r
  ∙-assoc p q r i = ∙-filler-l p q i ∙ ∙-filler-r q r (~ i)

  ∙-inv-l : (p : x ＝ y) → sym p ∙ p ＝ refl
  ∙-inv-l {y} p i j = hcomp (∂ j ∨ i) λ where
    k (j = i0) → p (k ∨ i)
    k (j = i1) → p (k ∨ i)
    k (i = i1) → y
    k (k = i0) → p i

  ∙-cancel-l : (p : x ＝ y) (q : y ＝ z)
             → sym p ∙ p ∙ q ＝ q
  ∙-cancel-l {y} p q i j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → p (i ∨ ~ j)
    k (i = i0) → ∙-filler-l (sym p) (p ∙ q) k j
    k (i = i1) → q (j ∧ k)
    k (j = i0) → y
    k (j = i1) → ∙-filler-r p q (~ i) k

  ∙-inv-r : (p : x ＝ y) → p ∙ sym p ＝ refl
  ∙-inv-r p = ∙-inv-l (sym p)

  ∙-cancel-r : (p : x ＝ y) (q : z ＝ y)
             → (p ∙ sym q) ∙ q ＝ p
  ∙-cancel-r q p = sym $ ∙-unique q λ i j → ∙-filler-l p (sym q) (~ j) i

  commutes→square : {p : w ＝ x} {q : w ＝ y} {s : x ＝ z} {r : y ＝ z}
                  → p ∙ s ＝ q ∙ r
                  → Square p q r s
  commutes→square {p} {q} {s} {r} θ i j =
    hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → θ j i
      k (i = i0) → q (  k ∧ j)
      k (i = i1) → s (~ k ∨ j)
      k (j = i0) → ∙-filler-l p s (~ k) i
      k (j = i1) → ∙-filler-r q r (~ k) i

  square→commutes : {p : w ＝ x} {q : w ＝ y} {s : x ＝ z} {r : y ＝ z}
                  → Square p q r s
                  → p ∙ s ＝ q ∙ r
  square→commutes {p} {q} {s} {r} θ i j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → θ j i
    k (i = i0) → ∙-filler-l p s k j
    k (i = i1) → ∙-filler-r q r k j
    k (j = i0) → q (~ k ∧ i)
    k (j = i1) → s (k ∨ i)

  square→conjugate
    : {p : x ＝ y} {q : x ＝ z} {r : z ＝ w} {s : y ＝ w}
    → Square p q r s
    → s ＝ sym p ∙ q ∙ r
  square→conjugate {p} {q} {r} {s} θ =
    sym (ap fst (∙∙-contract _ _ _ (_ , θ))) ∙ ∙∙＝∙ _ _ _

  conjugate→square
    : {p : x ＝ y} {q : x ＝ z} {r : z ＝ w} {s : y ＝ w}
    → s ＝ sym p ∙ q ∙ r
    → Square p q r s
  conjugate→square {p} {q} {r} {s} u =
    to-pathP (transport-path q p r ∙ sym u)

  ∙-cancel′-l : (p : x ＝ y) (q r : y ＝ z)
              → p ∙ q ＝ p ∙ r
              → q ＝ r
  ∙-cancel′-l p q r sq =
       sym (∙-cancel-l p q)
    ∙∙ ap (sym p ∙_) sq
    ∙∙ ∙-cancel-l p r

  ∙-cancel′-r : (p : y ＝ z) (q r : x ＝ y)
              → q ∙ p ＝ r ∙ p
              → q ＝ r
  ∙-cancel′-r p q r sq =
       sym (∙-cancel-r q (sym p))
    ∙∙ ap (_∙ sym p) sq
    ∙∙ ∙-cancel-r r (sym p)

  whisker-path-l : (x ＝ y) → (x ＝ z) ＝ (y ＝ z)
  whisker-path-l {z} p i = p i ＝ z

  whisker-path-r : (y ＝ z) → (x ＝ y) ＝ (x ＝ z)
  whisker-path-r {x} q i = x ＝ q i

  homotopy-invert : {f : A → A}
                  → (H : Π[ x ꞉ A ] (f x ＝ x)) {x : A}
                  → H (f x) ＝ ap f (H x)
  homotopy-invert {f} H {x} i j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → H x       (j ∧ i)
    k (j = i0) → H (f x)   (~ k)
    k (j = i1) → H x       (~ k ∧ i)
    k (i = i0) → H (f x)   (~ k ∨ j)
    k (i = i1) → H (H x j) (~ k)

  homotopy-natural : {f g : A → B}
                     (H : Π[ a ꞉ A ] (f a ＝ g a))
                     {x y : A} (p : x ＝ y)
                   → H x ∙ ap g p ＝ ap f p ∙ H y
  homotopy-natural {f} H {x} p =
    square→commutes λ j i → hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → H x           (j ∧ k)
      k (i = i1) → H (p k)       (j ∧ k)
      k (j = i0) → f (p (i ∧ k))
      k (j = i1) → H (p (i ∧ k)) k
      k (k = i0) → f x

  homotopy-sym-inv : {f : A → A}
                     (H : Π[ a ꞉ A ] (f a ＝ a))
                     (x : A)
                   → Path (f x ＝ f x) (λ i → H (H x (~ i)) i) refl
  homotopy-sym-inv {f} H x i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → H (H x (~ j)) j
    k (i = i1) → H x (j ∧ ~ k)
    k (j = i0) → f x
    k (j = i1) → H x (i ∧ ~ k)
    k (k = i0) → H (H x (i ∨ ~ j)) j
