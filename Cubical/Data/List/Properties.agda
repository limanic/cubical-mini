{-# OPTIONS --safe #-}
module Cubical.Data.List.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.IdentitySystem

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Fin
open import Cubical.Data.List.Base

open import Cubical.Relation.Nullary

open isIdentitySystem

module _ {ℓ} {A : Type ℓ} where

  ++-unit-r : (xs : List A) → xs ++ [] ≡ xs
  ++-unit-r [] = refl
  ++-unit-r (x ∷ xs) = cong (_∷_ x) (++-unit-r xs)

  ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

  rev-snoc : (xs : List A) (y : A) → rev (xs ++ [ y ]) ≡ y ∷ rev xs
  rev-snoc [] y = refl
  rev-snoc (x ∷ xs) y = cong (_++ [ x ]) (rev-snoc xs y)

  rev-++ : (xs ys : List A) → rev (xs ++ ys) ≡ rev ys ++ rev xs
  rev-++ [] ys = sym (++-unit-r (rev ys))
  rev-++ (x ∷ xs) ys =
    cong (λ zs → zs ++ [ x ]) (rev-++ xs ys)
    ∙ ++-assoc (rev ys) (rev xs) [ x ]

  rev-rev : (xs : List A) → rev (rev xs) ≡ xs
  rev-rev [] = refl
  rev-rev (x ∷ xs) = rev-snoc (rev xs) x ∙ cong (_∷_ x) (rev-rev xs)

  rev-rev-snoc : (xs : List A) (y : A) →
    Square (rev-rev (xs ++ [ y ])) (cong (_++ [ y ]) (rev-rev xs)) (cong rev (rev-snoc xs y)) refl
  rev-rev-snoc [] y = sym (lUnit refl)
  rev-rev-snoc (x ∷ xs) y i j =
    hcomp
      (λ k → λ
        { (i = i1) → compPath-filler (rev-snoc (rev xs) x) (cong (x ∷_) (rev-rev xs)) k j ++ [ y ]
        ; (j = i0) → rev (rev-snoc xs y i ++ [ x ])
        ; (j = i1) → x ∷ rev-rev-snoc xs y i k
        })
      (rev-snoc (rev-snoc xs y i) x j)

  data SnocView : List A → Type ℓ where
    nil : SnocView []
    snoc : (x : A) → (xs : List A) → (sx : SnocView xs) → SnocView (xs ∷ʳ x)

  snocView : (xs : List A) → SnocView xs
  snocView xs = helper nil xs
    where
    helper : {l : List A} -> SnocView l -> (r : List A) -> SnocView (l ++ r)
    helper {l} sl [] = subst SnocView (sym (++-unit-r l)) sl
    helper {l} sl (x ∷ r) = subst SnocView (++-assoc l (x ∷ []) r) (helper (snoc x l sl) r)

-- Path space of list type
module ListPath {ℓ} {A : Type ℓ} where

  Cover : List A → List A → Type ℓ
  Cover [] [] = Lift Unit
  Cover [] (_ ∷ _) = Lift ⊥
  Cover (_ ∷ _) [] = Lift ⊥
  Cover (x ∷ xs) (y ∷ ys) = (x ≡ y) × Cover xs ys

  reflCode : ∀ xs → Cover xs xs
  reflCode [] = lift tt
  reflCode (_ ∷ xs) = refl , reflCode xs

  decode : ∀ xs ys → Cover xs ys → xs ≡ ys
  decode []       []       _       = refl
  decode (x ∷ xs) (y ∷ ys) (p , c) = cong₂ _∷_ p (decode xs ys c)

  isOfHLevelCover : (n : HLevel) (p : isOfHLevel (suc (suc n)) A)
    (xs ys : List A) → isOfHLevel (suc n) (Cover xs ys)
  isOfHLevelCover n p [] [] =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isPropUnit)
  isOfHLevelCover n p [] (y ∷ ys) =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (x ∷ xs) [] =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (x ∷ xs) (y ∷ ys) =
    isOfHLevelΣ (suc n) (p x y) (\ _ → isOfHLevelCover n p xs ys)

  ListIds : isIdentitySystem Cover reflCode
  toPath     ListIds = decode _ _
  toPathOver ListIds = helper _ _
    where
    helper : ∀ xs ys → (p : Cover xs ys) → PathP (λ i → Cover xs (decode xs ys p i)) (reflCode xs) p
    helper []       []       tt*     = refl
    helper (x ∷ xs) (y ∷ ys) (p , c) = ΣPathP ((λ i j → p (i ∧ j)) , helper _ _ c)

isOfHLevelList : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
  → isOfHLevel (suc (suc n)) A → isOfHLevel (suc (suc n)) (List A)
isOfHLevelList n ofLevel xs ys =
  isOfHLevelRespectEquiv (suc n)
    (identitySystem≃PathSpace ListPath.ListIds)
    (ListPath.isOfHLevelCover n ofLevel xs ys)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  x y : A
  xs ys : List A

caseList : (n c : B) → List A → B
caseList n _ []      = n
caseList _ c (_ ∷ _) = c

safe-head : A → List A → A
safe-head x []      = x
safe-head _ (x ∷ _) = x

safe-tail : List A → List A
safe-tail []       = []
safe-tail (_ ∷ xs) = xs

cons-inj₁ : x ∷ xs ≡ y ∷ ys → x ≡ y
cons-inj₁ {x = x} p = cong (safe-head x) p

cons-inj₂ : x ∷ xs ≡ y ∷ ys → xs ≡ ys
cons-inj₂ = cong safe-tail

¬cons≡nil : {xs : List A} → ¬ (x ∷ xs ≡ [])
¬cons≡nil {A = A} p = lower (subst (caseList (Lift ⊥) (List A)) p [])

¬nil≡cons : {xs : List A} → ¬ ([] ≡ x ∷ xs)
¬nil≡cons {A = A} p = lower (subst (caseList (List A) (Lift ⊥)) p [])

¬snoc≡nil : {xs : List A} → ¬ (xs ∷ʳ x ≡ [])
¬snoc≡nil {xs = []} contra = ¬cons≡nil contra
¬snoc≡nil {xs = x ∷ xs} contra = ¬cons≡nil contra

¬nil≡snoc : {xs : List A} → ¬ ([] ≡ xs ∷ʳ x)
¬nil≡snoc contra = ¬snoc≡nil (sym contra)

cons≡rev-snoc : (x : A) → (xs : List A) → x ∷ rev xs ≡ rev (xs ∷ʳ x)
cons≡rev-snoc _ [] = refl
cons≡rev-snoc x (y ∷ ys) = λ i → cons≡rev-snoc x ys i ++ y ∷ []

isContr[]≡[] : isContr (Path (List A) [] [])
isContr[]≡[] = isOfHLevelRespectEquiv 0 (identitySystem≃PathSpace ListPath.ListIds) isContrUnit*

isPropXs≡[] : isProp (xs ≡ [])
isPropXs≡[] {xs = []} = isOfHLevelSuc 0 isContr[]≡[]
isPropXs≡[] {xs = x ∷ xs} = λ p _ → ⊥.rec (¬cons≡nil p)

discreteList : Discrete A → Discrete (List A)
discreteList eqA []       []       = yes refl
discreteList eqA []       (y ∷ ys) = no ¬nil≡cons
discreteList eqA (x ∷ xs) []       = no ¬cons≡nil
discreteList eqA (x ∷ xs) (y ∷ ys) with eqA x y | discreteList eqA xs ys
... | yes p | yes q = yes (λ i → p i ∷ q i)
... | yes _ | no ¬q = no (λ p → ¬q (cons-inj₂ p))
... | no ¬p | _     = no (λ q → ¬p (cons-inj₁ q))

foldrCons : (xs : List A) → foldr _∷_ [] xs ≡ xs
foldrCons [] = refl
foldrCons (x ∷ xs) = cong (x ∷_) (foldrCons xs)

length-map : (f : A → B)
             (as : List A)
           → length (map f as) ≡ length as
length-map f []       = refl
length-map f (a ∷ as) = cong suc (length-map f as)

length-tabulate : (n : ℕ) → (f : Fin n → A) → length (tabulate n f) ≡ n
length-tabulate zero    _ = refl
length-tabulate (suc n) f = cong suc (length-tabulate n (f ∘ suc))

tabulate-lookup : (xs : List A) → tabulate (length xs) (lookup xs) ≡ xs
tabulate-lookup []       = refl
tabulate-lookup (x ∷ xs) = cong (x ∷_) (tabulate-lookup xs)

lookup-map : (f : A → B) (xs : List A)
             (p0 : Fin (length (map f xs)))
             (p1 : Fin (length xs))
             (p : PathP (λ i → Fin (length-map f xs i)) p0 p1)
           → lookup (map f xs) p0 ≡ f (lookup xs p1)
lookup-map f (x ∷ xs) zero    zero     p = refl
lookup-map f (x ∷ xs) zero    (suc _)  p = ⊥.rec (znotsP p)
lookup-map f (x ∷ xs) (suc k) zero     p = ⊥.rec (snotzP p)
lookup-map f (x ∷ xs) (suc k) (suc k′) p = lookup-map f xs k k′ (injSucFinP p)
