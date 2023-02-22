module prelude where
  -- top
  data ⊤ : Set where
    ⟨⟩ : ⊤

  -- bottom
  data ⊥ : Set where

  ⊥-elim : ∀ {A : Set} → ⊥ → A
  ⊥-elim ()

  -- negation
  module negation where
    open import Agda.Primitive using (Level)

    ¬_ : ∀ {ℓ : Level} → Set ℓ → Set ℓ
    ¬ A = A → ⊥

  -- decidability
  module decidability where
    open negation

    data Dec (A : Set) : Set where
      yes :   A → Dec A
      no  : ¬ A → Dec A

  -- equality
  module eq where
    open import Agda.Primitive using (Level)
    open negation

    infix 4 _≡_
    infix 4 _≢_

    data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
      refl : x ≡ x
    {-# BUILTIN EQUALITY _≡_ #-}

    _≢_ : ∀ {ℓ : Level} {A : Set ℓ} → A → A → Set ℓ
    x ≢ y = ¬ (x ≡ y)

    ≡-sym : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
    ≡-sym refl = refl

    postulate
      extensionality : ∀ {A B : Set} {f g : A → B}
        → (∀ (x : A) → f x ≡ g x)
          -----------------------
        → f ≡ g

    ¬-≡ : ∀ {A : Set} → (¬a : ¬ A) → (¬a′ : ¬ A) → ¬a ≡ ¬a′
    ¬-≡ ¬a ¬a′ = extensionality λ { a → ⊥-elim (¬a a) }

    transport : {ℓ ℓ′ : Level} {A : Set ℓ} {x y : A}
              → (B : A → Set ℓ′) → x ≡ y → B x → B y
    transport B refl x = x

    assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
    assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

  -- naturals
  module nat where
    open eq
    open decidability

    data ℕ : Set where
      zero : ℕ
      suc  : ℕ → ℕ
    {-# BUILTIN NATURAL ℕ #-}

    suc-≡ : ∀ {m n} → m ≡ n → suc m ≡ suc n
    suc-≡ refl = refl

    suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl

    suc-≢ : ∀ {m n} → m ≢ n → suc m ≢ suc n
    suc-≢ {zero}  z≢z   refl    = z≢z refl
    suc-≢ {suc m} sm≢sn ssm≡ssn = sm≢sn (suc-inj ssm≡ssn)

    _≡ℕ?_ : (m : ℕ) → (n : ℕ) → Dec (m ≡ n)
    zero  ≡ℕ? zero               = yes refl
    zero  ≡ℕ? suc n              = no (λ ())
    suc m ≡ℕ? zero               = no (λ ())
    suc m ≡ℕ? suc n with m ≡ℕ? n
    ...                | yes m≡n = yes (suc-≡ m≡n)
    ...                | no m≢n  = no  (suc-≢ m≢n)

  -- products
  module product where
    open import Agda.Primitive using (Level; _⊔_)

    -- dependent products
    record Σ {ℓ ℓ′ : Level} (A : Set ℓ) (B : A → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
      constructor ⟨_,_⟩
      field
        fst : A
        snd : B fst
    infixr 4 ⟨_,_⟩
    {-# BUILTIN SIGMA Σ #-}

    -- nice syntax
    open Σ public
      renaming (fst to proj₁; snd to proj₂)

    Σ-syntax = Σ
    syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
    infix 2 Σ-syntax

    -- existence
    ∃ : ∀ {ℓ ℓ′ : Level} {A : Set ℓ} → (A → Set ℓ′) → Set (ℓ ⊔ ℓ′)
    ∃ = Σ _

    -- existence syntax
    infix 2 ∃-syntax
    ∃-syntax : ∀ {ℓ ℓ′ : Level} {A : Set ℓ} → (A → Set ℓ′) → Set (ℓ ⊔ ℓ′)
    ∃-syntax = ∃
    syntax ∃-syntax (λ x → B) = ∃[ x ] B

    -- non-dependent products
    _×_ : ∀ {ℓ ℓ′ : Level} (A : Set ℓ) (B : Set ℓ′) → Set (ℓ ⊔ ℓ′)
    A × B = Σ[ x ∈ A ] B
    infixr 2 _×_

  module list where
    data List (A : Set) : Set where
      []  : List A
      _∷_ : A → List A → List A

    infixr 99 _∷_
    infixr 9 _++_


    pattern ∣[_] z = z ∷ []
    pattern ∣[_,_] y z = y ∷ z ∷ []
    pattern ∣[_,_,_] x y z = x ∷ y ∷ z ∷ []
    pattern ∣[_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
    pattern ∣[_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
    pattern ∣[_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

    _++_ : ∀ {A : Set} → List A → List A → List A
    []       ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  open negation public
  open decidability public
  open eq public
  open nat public
  open product public
  open list public
