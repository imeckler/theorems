module Inf where

open import Data.Product
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
-- open import Data.List
open import Data.Vec

Onto : {A B : Set} → (f : A → B) → Set
Onto {A} {B} f = (y : B) → Σ A (λ x → f x ≡ y)

idOnto : {A : Set} → Onto (λ (x : A) → x)
idOnto = λ y → y , refl

inf : Set → Set
inf A = (n : ℕ) → (f : Fin n → A) → ¬ (Onto f)

FinZempty : {P : Fin 0 → Set} → (x : Fin 0) → P x
FinZempty ()

ℕ-is-inf : inf ℕ
ℕ-is-inf 0 f onto  = FinZempty (proj₁ (onto 0))
ℕ-is-inf (suc n) f onto = {!!}

finUp : (n : ℕ) → Fin n → Fin (suc n)
finUp (suc n) x = suc x
finUp zero ()

finUpId : (n : ℕ) → Fin n → Fin (suc n)
finUpId (suc n) zero = zero
finUpId (suc n) (suc k) = suc (finUp n k)
finUpId 0 ()

fins : (n : ℕ) → Σ (Vec (Fin n) n) (λ xs → (x : Fin n) → x ∈ xs)
fins 0 = ([] , FinZempty)
fins 1 = (zero ∷ [] , oneLem) where
  oneLem : (x : Fin 1) → x ∈ (zero ∷ [])
  oneLem zero = here
  oneLem (suc k) = FinZempty k
 
fins (suc (suc m)) = xs , {!!} where
  ih : Σ (Vec (Fin (suc m)) (suc m)) (λ xs → (x : Fin (suc m)) → x ∈ xs)
  ih = fins (suc m)

  n : ℕ
  n = suc m

  xs : Vec (Fin (suc (suc m))) (suc (suc m))
  xs = zero ∷ Data.Vec.map (finUp (suc m)) (proj₁ ih)

  in-xs-lem : (x : Fin n) → x ∈ proj₁ ih → finUp n x ∈ xs
  in-xs-lem zero ()
  in-xs-lem (suc x) p = {!there p!}

  in-xs : (x : Fin (suc (suc m))) → x ∈ xs
  in-xs zero = here
  in-xs (suc x) = {!!} -- ((proj₂ ih) x)

