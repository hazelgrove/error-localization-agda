module prelude where
  data ⊥ : Set where

  ⊥-elim : ∀ {A : Set} → ⊥ → A
  ⊥-elim ()

  data Triv : Set where
    unit : Triv

  -- negation
  module negation where
    ¬_ : Set → Set
    ¬ A = A → ⊥

  -- decidability
  module decidability where
    open negation

    data Dec (A : Set) : Set where
      yes :   A → Dec A
      no  : ¬ A → Dec A

  -- equality
  module eq where
    open negation

    infix 4 _≡_
    infix 4 _≢_

    data _≡_ {A : Set} (x : A) : A → Set where
      refl : x ≡ x
    {-# BUILTIN EQUALITY _≡_ #-}

    _≢_ : ∀ {A : Set} → A → A → Set
    x ≢ y = ¬ (x ≡ y)

    ≡sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    ≡sym refl = refl

    postulate
      extensionality : ∀ {A B : Set} {f g : A → B}
        → (∀ (x : A) → f x ≡ g x)
          -----------------------
        → f ≡ g

    ¬≡ : ∀ {A : Set} → (¬a : ¬ A) → (¬a′ : ¬ A) → ¬a ≡ ¬a′
    ¬≡ ¬a ¬a′ = extensionality λ { a → ⊥-elim (¬a a) }

  -- naturals
  module nat where
    open eq
    open decidability

    data ℕ : Set where
      zero : ℕ
      suc  : ℕ → ℕ
    {-# BUILTIN NATURAL ℕ #-}

    ≡suc : ∀ {m n} → m ≡ n → suc m ≡ suc n
    ≡suc refl = refl

    suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl

    ≢suc : ∀ {m n} → m ≢ n → suc m ≢ suc n
    ≢suc {zero}  z≢z   refl    = z≢z refl
    ≢suc {suc m} sm≢sn ssm≡ssn = sm≢sn (suc-inj ssm≡ssn)

    _≡ℕ?_ : (m : ℕ) → (n : ℕ) → Dec (m ≡ n)
    zero  ≡ℕ? zero               = yes refl
    zero  ≡ℕ? suc n              = no (λ ())
    suc m ≡ℕ? zero               = no (λ ())
    suc m ≡ℕ? suc n with m ≡ℕ? n
    ...                | yes m≡n = yes (≡suc m≡n)
    ...                | no m≢n  = no  (≢suc m≢n)

  -- maybe
  module maybe where
    data Maybe (A : Set) : Set where
      Some : A → Maybe A
      None : Maybe A

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

  open negation public
  open decidability public
  open eq public
  open nat public
  open maybe public
  open product public
