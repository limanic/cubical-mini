{-# OPTIONS --safe #-}
module Structures.Base where

open import Foundations.Base
open import Foundations.HLevel.Base
open import Foundations.Pi
open import Foundations.Sigma
open import Foundations.Univalence

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A : Type ℓ
  S T : Type ℓ → Type ℓ₁

Constant-str : (A : Type ℓ) → Structure {ℓ₁} ℓ (const A)
Constant-str T .is-hom (A , x) (B , y) f = x ＝ y

Constant-str-is-univalent : is-univalent (Constant-str {ℓ₁ = ℓ₁} A)
Constant-str-is-univalent f = idₑ

Constant-action : (A : Type ℓ) → Equiv-action {ℓ = ℓ₁} (λ X → A)
Constant-action A eqv = idₑ

Constant-action-is-transport
  : is-transport-str {ℓ = ℓ₁} (Constant-action A)
Constant-action-is-transport f s = sym (transport-refl _)


Pointed-str : Structure ℓ id
Pointed-str .is-hom (A , x) (B , y) f = f .fst x ＝ y

@0 Pointed-str-is-univalent : is-univalent (Pointed-str {ℓ})
Pointed-str-is-univalent f = ua-PathP≃path _

Id-action-is-transport : is-transport-str {ℓ} {ℓ} id
Id-action-is-transport f s = sym (transport-refl _)


Product-str : Structure ℓ S → Structure ℓ₂ T → Structure _ (λ X → S X × T X)
Product-str S T .is-hom (A , x , y) (B , x′ , y′) f =
  S .is-hom (A , x) (B , x′) f × T .is-hom (A , y) (B , y′) f

@0 Product-str-is-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                            → is-univalent σ → is-univalent τ
                            → is-univalent (Product-str σ τ)
Product-str-is-univalent {S} {T} {σ} {τ} θ₁ θ₂ {X , x , y} {Y , x′ , y′} f =
  (σ .is-hom (X , x) (Y , x′) _ × τ .is-hom (X , y) (Y , y′) _) ≃⟨ Σ-ap (θ₁ f) (λ _ → θ₂ f) ⟩
  (PathP _ _ _ × PathP _ _ _)                                   ≃⟨ Iso→Equiv Σ-PathP-iso ⟩
  PathP (λ i → S (ua f i) × T (ua f i)) (x , y) (x′ , y′)       ≃∎

Product-action : Equiv-action S → Equiv-action T → Equiv-action (λ X → S X × T X)
Product-action actx acty eqv = Σ-ap (actx eqv) λ x → acty eqv

@0 Product-action-is-transport
  : {α : Equiv-action S} {β : Equiv-action T}
  → is-transport-str α → is-transport-str β
  → is-transport-str (Product-action α β)
Product-action-is-transport α-tr β-tr e s =
  Σ-PathP (α-tr e (s .fst)) (β-tr e (s .snd))


Str-function-str : Structure ℓ₁ S → Structure ℓ₂ T → Structure _ (λ X → S X → T X)
Str-function-str {S} σ τ .is-hom (A , f) (B , g) h =
  {s : S A} {t : S B} → σ .is-hom (A , s) (B , t) h
                      → τ .is-hom (A , f s) (B , g t) h

@0 Str-function-str-is-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                                 → is-univalent σ → is-univalent τ
                                 → is-univalent (Str-function-str σ τ)
Str-function-str-is-univalent {S} {T} {σ} {τ} θ₁ θ₂ eqv =
  Π-impl-cod-≃ (λ s → Π-impl-cod-≃ λ t → function-≃ (θ₁ eqv) (θ₂ eqv)) ∙ₑ fun-ext-dep-≃

-- prefer this one
Function-str : Equiv-action S → Structure ℓ T → Structure _ (λ X → S X → T X)
Function-str {S} act str .is-hom (A , f) (B , g) e =
  Π[ s ꞉ S A ] str .is-hom (A , f s) (B , g (act e .fst s)) e

@0 Function-str-is-univalent
  : (α : Equiv-action S) → is-transport-str α
  → (τ : Structure ℓ T) → is-univalent τ
  → is-univalent (Function-str α τ)
Function-str-is-univalent {S} {T} α α-tr τ τ-univ {X , f} {Y , g} eqv =
  ((s : S X) → τ .is-hom (X , f s) (Y , _) eqv)     ≃⟨ Π-cod-≃ (λ s → τ-univ eqv ∙ₑ path→Equiv (ap (PathP (λ i → T (ua eqv i)) (f s) ∘ g) (α-tr _ _))) ⟩
  ((s : S X) → PathP (λ i → T (ua eqv i)) (f s) _)  ≃⟨ (hetero-homotopy≃homotopy ₑ⁻¹) ∙ₑ fun-ext-dep-≃ ⟩
  _                                                 ≃∎

Function-action : Equiv-action S → Equiv-action T → Equiv-action (λ X → S X → T X)
Function-action actx acty eqv = function-≃ (actx eqv) (acty eqv)

@0 Function-action-is-transport
  : {α : Equiv-action S} {β : Equiv-action T}
  → is-transport-str α → is-transport-str β
  → is-transport-str (Function-action α β)
Function-action-is-transport {S} {α} {β} α-tr β-tr eqv f =
  fun-ext λ x → ap (β eqv .fst ∘ f) (sym-transport-str α α-tr eqv x)
              ∙ β-tr eqv (f (subst S (sym (ua eqv)) x))


_on-paths-of_ : (Type ℓ → Type ℓ₁) → Type ℓ → Type (ℓ ⊔ ℓ₁)
S on-paths-of A = Π[ a ꞉ A ] Π[ a′ ꞉ A ] S (a ＝ a′)

-- observe that "being a proposition" is a pointed structure on paths
_ : id on-paths-of_ ＝ is-prop {ℓ}
_ = fun-ext (λ _ → refl)

_stable_ : (S : Type ℓ → Type ℓ₁) → Type ℓ → Type (ℓ ⊔ ℓ₁)
S stable A = S A → A


module _
  (σ : Structure ℓ S)
  (axioms : (X : _) → S X → Type ℓ₃)
  where

  Axiom-str : Structure ℓ (λ X → Σ[ s ꞉ S X ] (axioms X s))
  Axiom-str .is-hom (A , s , a) (B , t , b) f =
    σ .is-hom (A , s) (B , t) f

  module _
    (univ : is-univalent σ)
    (axioms-prop : ∀ {X} {s} → is-prop (axioms X s)) where

    @0 Axiom-str-univalent : is-univalent Axiom-str
    Axiom-str-univalent {X = A , s , a} {Y = B , t , b} f =
      σ .is-hom (A , s) (B , t) f
        ≃⟨ univ f ⟩
      ＜ s ／ (λ i → S (ua f i)) ＼ t ＞
        ≃⟨ Σ-contract (λ x → PathP-is-of-hlevel 0 (b , (axioms-prop b))) ₑ⁻¹ ⟩
      (Σ[ p ꞉ ＜ s ／ (λ i → S (ua f i)) ＼ t ＞ ] ＜ a ／ (λ i → axioms (ua f i) (p i)) ＼ b ＞)
        ≃⟨ Iso→Equiv Σ-PathP-iso ⟩
      _
        ≃∎

@0 transfer-axioms
  : {σ : Structure ℓ S} {univ : is-univalent σ}
    {axioms : (X : _) → S X → Type ℓ₃}
  → (A : Type-with (Axiom-str σ axioms)) (B : Type-with σ)
  → (A .fst , A .snd .fst) ≃[ σ ] B
  → axioms (B .fst) (B .snd)
transfer-axioms {univ} {axioms} A B eqv =
  subst (λ { (x , y) → axioms x y }) (sip univ eqv) (A .snd .snd)