{-# OPTIONS --safe #-}
module Data.Fin.Inductive.Closure where

open import Meta.Prelude

open import Data.Empty.Base as ⊥
open import Data.Empty.Properties as ⊥
open import Data.Fin.Inductive.Path
open import Data.Fin.Inductive.Properties
open import Data.Nat.Base
open import Data.Sum.Base as ⊎
open import Data.Sum.Properties as ⊎
open import Data.Unit.Base
open import Data.Unit.Properties as ⊤

private variable
  ℓ : Level
  @0 m n : ℕ

fin-suc : Fin (suc n) ≃ ⊤ ⊎ Fin n
fin-suc = ≅→≃ (f , iso g rinv linv) where
  f : Fin (suc n) → ⊤ ⊎ Fin n
  f fzero = inl tt
  f (fsuc x) = inr x

  g : ⊤ ⊎ Fin n → Fin (suc n)
  g (inr x) = fsuc x
  g (inl _) = fzero

  rinv : g is-right-inverse-of f
  rinv (inr _) = refl
  rinv (inl _) = refl

  linv : g is-left-inverse-of f
  linv fzero = refl
  linv (fsuc x) = refl

fin-suc-universal
  : {A : Fin (suc n) → Type ℓ}
  → Π[ x ꞉ Fin _ ] A x
  ≃ A fzero × (∀ x → A (fsuc x))
fin-suc-universal = ≅→≃ λ where
  .fst f → f fzero , (λ x → f (fsuc x))

  .snd .is-iso.inv (z , f) fzero    → z
  .snd .is-iso.inv (z , f) (fsuc x) → f x

  .snd .is-iso.rinv x → refl

  .snd .is-iso.linv k i fzero    → k fzero
  .snd .is-iso.linv k i (fsuc n) → k (fsuc n)

fin-coproduct : {n m : ℕ}
              → Fin n ⊎ Fin m
              ≃ Fin (n + m)
fin-coproduct {0} {m}  =
  Fin 0 ⊎ Fin m  ~⟨ ⊎-ap-l fin0-is-initial ⟩
  ⊥ ⊎ Fin m      ~⟨ ⊎-zero-l ⟩
  Fin m          ∎
fin-coproduct {suc n} {m} =
  Fin (suc n) ⊎ Fin m  ~⟨ ⊎-ap-l fin-suc ⟩
  (⊤ ⊎ Fin n) ⊎ Fin m  ~⟨ ⊎-assoc ⟩
  ⊤ ⊎ Fin n ⊎ Fin m    ~⟨ ⊎-ap-r (fin-coproduct {n} {m}) ⟩
  ⊤ ⊎ Fin (n + m)      ~⟨ fin-suc ⁻¹ ⟩
  Fin (suc (n + m))    ∎

sum : ∀ n → (Fin n → ℕ) → ℕ
sum 0       f = 0
sum (suc n) f = f fzero + sum n (f ∘ fsuc)

fin-sum : {n : ℕ} (B : Fin n → ℕ)
        → Σ[ k ꞉ Fin n ] Fin (B k)
        ≃ Fin (sum n B)
fin-sum {0}     B .fst ()
fin-sum {0}     B .snd .equiv-proof ()
fin-sum {suc n} B =
  fin-coproduct .fst ∘ f ,
  is-equiv-comp (is-iso→is-equiv f-iso) (fin-coproduct .snd)
    where
      rec″ = fin-sum (B ∘ fsuc)
      module mrec = Equiv rec″

      f : Σ _ (λ k → Fin (B k)) → Fin (B fzero) ⊎ Fin (sum n (B ∘ fsuc))
      f (fzero  , x) = inl x
      f (fsuc x , y) = inr (rec″ .fst (x , y))

      f-iso : is-iso f
      f-iso .is-iso.inv (inl x) = fzero , x
      f-iso .is-iso.inv (inr x) with mrec.from x
      ... | x , y = fsuc x , y

      f-iso .is-iso.rinv (inl x) = refl
      f-iso .is-iso.rinv (inr x) = ap inr (mrec.ε _)

      f-iso .is-iso.linv (fzero  , _) = refl
      f-iso .is-iso.linv (fsuc x , y)
        =  ap (fsuc ∘ fst) (mrec.η _)
        ,ₚ ap snd (mrec.η _)

fin-product : {n m : ℕ}
            → Fin n × Fin m
            ≃ Fin (n · m)
fin-product {n} {m} =
  Fin n × Fin m          ~⟨ fin-sum (λ _ → m) ⟩
  Fin (sum n (λ _ → m))  ~⟨ cast (sum=* n m) , cast-is-equiv _ _ ⟩
  Fin (n · m)            ∎
  where
    sum=* : ∀ n m → sum n (λ _ → m) ＝ n · m
    sum=* 0       m = refl
    sum=* (suc n) m = ap (m +_) (sum=* n m)

fin-fun : {n m : ℕ}
        → (Fin n → Fin m)
        ≃ Fin (m ^ n)
fin-fun {0} {m} =
  (Fin 0 → Fin m)  ~⟨ Π-dom-≃ fin0-is-initial ⟨
  (⊥ → Fin m)      ~⟨ ⊥.universal ⟩
  ⊤                ~⟨ is-contr→equiv-⊤ fin1-is-contr ⟨
  Fin 1            ∎
fin-fun {suc n} {m} =
  (Fin (suc n) → Fin m)          ~⟨ Π-dom-≃ fin-suc ⟨
  (⊤ ⊎ Fin n → Fin m)            ~⟨ ⊎.universal ⟩
  (⊤ → Fin m) × (Fin n → Fin m)  ~⟨ ×-ap ⊤.universal fin-fun ⟩
  Fin m × Fin (m ^ n)            ~⟨ fin-product ⟩
  Fin (m · m ^ n)                ∎
