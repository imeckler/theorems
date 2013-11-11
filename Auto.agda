module Auto where

open import Data.Bool
open import Function
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Nullary
open ≡-Reasoning

is-equiv : {A B : Set} → (f : A → B) → Set
is-equiv {A} {B} f = Σ (B → A)
                       (λ g → (∀ x → g (f x) ≡ x) × (∀ y → f (g y) ≡ y))


_≅_ : Set → Set → Set 
A ≅ B = Σ (A → B) is-equiv

-- ℕ → (A → A) → (A → A)
 
iter : {A : Set} → ℕ → (A → A) → (A → A)
iter 0 _ = id
iter (suc n) f = f ∘ (iter n f)

≅-surj : {A B : Set} {f : A → B}
       → is-equiv f
       → (y : B)
       → ∃ (λ x → f x ≡ y)
≅-surj (g , (there , back)) y = (g y) , (back y)

injective : {A B : Set} → (A → B) → Set
injective f = ∀ {x y} → (f x ≡ f y) → x ≡ y

≅-inj : {A B : Set} {f : A → B}
      → is-equiv f
      → injective f
≅-inj {A} {B} {f} (g , there , back) {x} {y} p =
  begin
    x
  ≡⟨ sym (there x) ⟩
    g (f x)
  ≡⟨ cong g p ⟩
    g (f y)
  ≡⟨ there y ⟩
    y
  ∎

nah : ¬ (ℕ ≅ (ℕ → ℕ))
nah (f , (g , (there , back))) = uh-oh hmm where
  diag : ℕ → ℕ
  diag n = suc ((f n) n)

  suc-inj : ∀ {n m} → (suc n ≡ suc m) → n ≡ m
  suc-inj refl = refl

  suclem : ∀ {n} → ¬ (n ≡ suc n)
  suclem {zero} = λ ()
  suclem {suc n} with suclem {n}
  ...| ¬p = λ q → ¬p (suc-inj q)

  hmm : ∃ (λ n → f n ≡ diag)
  hmm = ≅-surj (g , there , back) diag

  uh-oh : ¬ (∃ (λ n → f n ≡ diag))
  uh-oh (n , p) = 
    suclem (
      begin
        f n n
      ≡⟨ cong (λ h → h n) p ⟩
        diag n
      ∎
    )

no-inj :
  {A : Set}
  → ¬ (Σ ((A → A) → A) injective)
no-inj (f , inj) = {!!}

generally-no :
  {A : Set}
  → (i : A → A)
  → (∀ {x} → ¬ (i x ≡ x))
  → ¬ (A ≅ (A → A))
generally-no {A} i nfix (f , g , there , back) = well-hm sure-there-is where
  diag : A → A 
  diag x = i (f x x)

  sure-there-is : ∃ (λ x → f x ≡ diag)
  sure-there-is = ≅-surj (g , there , back) diag

  well-hm : ¬ (∃ (λ x → f x ≡ diag))
  well-hm (x , p) = 
    nfix (
      begin
        i (f x x)
      ≡⟨ sym (cong (λ h → h x) p) ⟩
        f x x
      ∎
    )

  {-
  y : a
  y = {!!}
  sps : a ≡ f y y
  sps = {!!}
  -- lem : ∃ (λ y → f y y ≡ a)
  -- lem = {!!} , {!!}

  uh-oh : ∃ (λ x → ¬ (diag x ≡ f x x)) 
  uh-oh = ( y 
          , (λ p →
            nid (
              begin
                i a
              ≡⟨ cong i sps ⟩
                i (f y y)
              ≡⟨ p ⟩
                f y y 
              ≡⟨ sym sps ⟩
                a
              ∎
            ))
           )
-}


trivial-fun-space : {A : Set} → {f g : A → A} → (p q : f ≡ g) → (p ≡ q)
trivial-fun-space p q = {!!}

module Gen where
  open import Data.Integer

  gens : {A : Set}
       → (f : A → A)
       → (e : is-equiv f)
       → Set
  gens f (finv , _) = ∃ (λ g → (∃ (λ n → (iter n f ≡ g) ⊎ (iter (ℕ.suc n) finv ≡ g))))

  t : {A : Set}
    → ¬ (ℤ ≅ (A ≅ A))
  t {A} (f , g , there , back) = {!!}

  -- This isn't true.
  gen-is-z : {A : Set} {f : A ≅ A} → ℤ ≅ (gens (proj₁ f) (proj₂ f))
  gen-is-z {A} {(f , g , there , back)} = fromℤ , toℤ , ( inv₁ , inv₂) where
    fromℤ : ℤ → gens f (g , there , back)
    fromℤ -[1+ n ] = iter (ℕ.suc n) g , n , inj₂ refl 
    fromℤ (+ n) = (iter n f) , (n , (inj₁ refl))

    toℤ : gens f (g , there , back) → ℤ
    toℤ (h , n , inj₁ p) = + n
    toℤ (h , n , inj₂ q) = -[1+ n ]

    inv₁ : (x : ℤ) → toℤ (fromℤ x) ≡ x
    inv₁ -[1+ n ] = refl
    inv₁ (+ n) = refl

    inv₂ : (h : gens f (g , there , back)) → (fromℤ (toℤ h)) ≡ h
    inv₂ (h , zero , inj₁ p) =
      begin
        id , zero , inj₁ refl
      ≡⟨ {!!} ⟩
        h , zero , inj₁ p
      ∎

    inv₂ (h , ℕ.suc n , inj₁ p) =
      begin
        (λ x₁ → f (iter n f x₁)) , ℕ.suc n , inj₁ refl
      ≡⟨ {!!} ⟩
        h , ℕ.suc n , inj₁ p
      ∎

    inv₂ (h , zero , inj₂ y) =
      begin
        g , zero , inj₂ refl
      ≡⟨ {!!} ⟩
        h , zero , inj₂ y
      ∎
    inv₂ (h , ℕ.suc n , inj₂ y) =
      begin
        (λ x → g (g (iter n g x))) , ℕ.suc n , inj₂ refl
      ≡⟨ {!!} ⟩
        h , ℕ.suc n , inj₂ y
      ∎

pow : {A : Set}
    → ¬ (A ≅ (A → Bool))
pow {A} (f , g , there , back) = uh-oh otoh where
  diag : A → Bool
  diag x = not (f x x)

  notlem : {b : Bool} → ¬ (b ≡ not b)
  notlem {true} = λ ()
  notlem {false} = λ ()

  uh-oh : ¬ (∃ (λ x → f x ≡ diag))
  uh-oh (x , eq) =
    notlem (
      begin
        f x x 
      ≡⟨ cong (λ h → h x) eq ⟩
        not (f x x)
      ∎
    )

  otoh : ∃ (λ x → f x ≡ diag)
  otoh = ≅-surj (g , there , back) diag

{-
mainly : {A : Set}
       → (i : A → A)
       → (∀ x → ¬ (i x ≡ x))
       → (f : A → A)
       → (e : is-equiv f)
       → ¬ ((A ≡ A) ≡ Gen.gens f e)
mainly = ?


t : {A : Set}
  → (f : A → A)
  → is-equiv f
  → ∃ (λ g → ¬ (gens f g))
t f _ = (λ x → {!!}) , (λ x → {!!})
-}
