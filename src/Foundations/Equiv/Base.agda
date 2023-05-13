{-# OPTIONS --safe #-}
module Foundations.Equiv.Base where

open import Foundations.Equiv public

open import Foundations.Base
open import Foundations.Path
open import Foundations.HLevel

-- include `Equiv` or `_≃_`      if the definition is about equivalences (`_≃_`)
-- include `equiv` or `is-equiv` if the definition is about function being an equivalence (`is-equiv`)
-- use `ₑ` subscript for common operators on equivalences

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  f : A → B

_is-left-inverse-of_ : (B → A) → (A → B) → Type _
g is-left-inverse-of f = (x : _) → g (f x) ＝ x
retraction = _is-left-inverse-of_

_is-right-inverse-of_ : (B → A) → (A → B) → Type _
g is-right-inverse-of f = (y : _) → f (g y) ＝ y
section = _is-right-inverse-of_

-- Helper function for constructing equivalences from pairs (f,g) that cancel each other up to definitional
-- equality. For such (f,g), the result type simplifies to is-contr (fibre f b).
strict-contr-fibres : (g : B → A) (b : B)
                    → Σ[ t  ꞉ fibre f (f (g b)) ]
                      Π[ t′ ꞉ fibre f       b   ]
                      Path (fibre f (f (g b))) t (g (f (t′ .fst)) , ap (f ∘ g) (t′ .snd))
strict-contr-fibres     g b .fst = g b , refl
strict-contr-fibres {f} g b .snd (a , p) i = g (p (~ i)) , λ j → f (g (p (~ i ∨ j)))

id-is-equiv : is-equiv (id {A = A})
id-is-equiv .equiv-proof = strict-contr-fibres id

idₑ : A ≃ A
idₑ = id , id-is-equiv

Equiv-centre : (e : A ≃ B) (y : B) → fibre (e .fst) y
Equiv-centre e y = e .snd .equiv-proof y .fst

Equiv-path : (e : A ≃ B) (y : B) (v : fibre (e .fst ) y) → Equiv-centre e y ＝ v
Equiv-path e y = e .snd .equiv-proof y .snd

is-equiv-is-prop : (f : A → B) → is-prop (is-equiv f)
is-equiv-is-prop f p q i .equiv-proof y =
  let p₂ = p .equiv-proof y .snd
      q₂ = q .equiv-proof y .snd
  in p₂ (q .equiv-proof y .fst) i , λ w j → hcomp (∂ i ∨ ∂ j) λ where
     k (i = i0) → p₂ w j
     k (i = i1) → q₂ w (j ∨ ~ k)
     k (j = i0) → p₂ (q₂ w (~ k)) i
     k (j = i1) → w
     k (k = i0) → p₂ w (i ∨ j)

Equiv-ext : {e₀ e₁ : A ≃ B} (h : e₀ .fst ＝ e₁ .fst) → e₀ ＝ e₁
Equiv-ext {e₀} {e₁} h i = h i , is-prop→PathP (λ i → is-equiv-is-prop (h i)) (e₀ .snd) (e₁ .snd) i

is-equiv→inverse : {f : A → B} → is-equiv f → (B → A)
is-equiv→inverse eqv y = eqv .equiv-proof y .fst .fst

is-equiv→counit : (eqv : is-equiv f) (y : B) → f (is-equiv→inverse eqv y) ＝ y
is-equiv→counit eqv y = eqv .equiv-proof y .fst .snd

is-equiv→unit : (eqv : is-equiv f) (x : A) → is-equiv→inverse eqv (f x) ＝ x
is-equiv→unit {f} eqv x i = eqv .equiv-proof (f x) .snd (x , refl) i .fst

is-equiv→zig : (eqv : is-equiv f) (x : A)
             → ap f (is-equiv→unit eqv x) ＝ is-equiv→counit eqv (f x)
is-equiv→zig {f} eqv x i j = hcomp (∂ i ∨ ∂ j) λ where
   k (i = i0) → f (is-equiv→unit eqv x j)
   k (i = i1) → is-equiv→counit eqv (f x) (j ∨ ~ k)
   k (j = i0) → is-equiv→counit eqv (f x) (i ∧ ~ k)
   k (j = i1) → f x
   k (k = i0) → eqv .equiv-proof (f x) .snd (x , refl) j .snd i

is-equiv→zag : (eqv : is-equiv f) (y : B)
             → ap (is-equiv→inverse eqv) (is-equiv→counit eqv y) ＝ is-equiv→unit eqv (is-equiv→inverse eqv y)
is-equiv→zag {f} eqv b =
  subst (λ b → ap g (ε b) ＝ η (g b)) (ε b) (helper (g b)) where
  g = is-equiv→inverse eqv
  ε = is-equiv→counit eqv
  η = is-equiv→unit eqv

  helper : ∀ a → ap g (ε (f a)) ＝ η (g (f a))
  helper a i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → g (ε (f a) (j ∨ ~ k))
    k (i = i1) → η (η a (~ k)) j
    k (j = i0) → g (is-equiv→zig eqv a (~ i) (~ k))
    k (j = i1) → η a (i ∧ ~ k)
    k (k = i0) → η a (i ∧ j)

infixr 30 _∙ₑ_
_∙ₑ_ : A ≃ B → B ≃ C → A ≃ C
(u ∙ₑ (g , v)) .fst = g ∘ u .fst
((f , u) ∙ₑ (g , v)) .snd .equiv-proof c = contr
  where
  contract-inv = Equiv-path (g , v) c

  θ : (a : _) (p : g (f a) ＝ c) → _
  θ a p = ∙-filler (ap (is-equiv→inverse u ∘ fst) (contract-inv (_ , p))) (is-equiv→unit u a)

  contr : is-contr (fibre (g ∘ f) c)
  contr .fst .fst = is-equiv→inverse u (is-equiv→inverse v c)
  contr .fst .snd = ap g (is-equiv→counit u (is-equiv→inverse v c)) ∙ is-equiv→counit v c
  contr .snd (a , p) i .fst = θ a p i1 i
  contr .snd (a , p) i .snd j = hcomp (i ∨ ∂ j) λ where
    k (i = i1) → f-square k
    k (j = i0) → g (f (θ a p k i))
    k (j = i1) → contract-inv (_ , p) i .snd k
    k (k = i0) → g (is-equiv→counit u (contract-inv  (_ , p) i .fst) j)
      where
      f-square : I → _
      f-square k = hcomp (∂ j ∨ ∂ k) λ where
        l (j = i0) → g (f (is-equiv→unit u a k))
        l (j = i1) → p (k ∧ l)
        l (k = i0) → g (is-equiv→counit u (f a) j)
        l (k = i1) → p (j ∧ l)
        l (l = i0) → g (Equiv-path (f , u) (f a) (a , refl) k .snd j)

is-equiv-comp : {g : B → C}
              → is-equiv f
              → is-equiv g
              → is-equiv (g ∘ f)
is-equiv-comp {f} {g} r s = ((f , r) ∙ₑ (g , s)) .snd
