module prelude where
  data ⊥ : Set where

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
    infix 4 _≡_
    infix 4 _≢_

    data _≡_ {A : Set} (x : A) : A → Set where
      refl : x ≡ x
    {-# BUILTIN EQUALITY _≡_ #-}

    _≢_ : ∀ {A : Set} → A → A → Set
    x ≢ y = x ≡ y → ⊥

    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

  -- naturals
  module nat where
    data ℕ : Set where
      zero : ℕ
      suc  : ℕ → ℕ
    {-# BUILTIN NATURAL ℕ #-}

  -- maybe
  module maybe where
    data Maybe (A : Set) : Set where
      Some : A → Maybe A
      None : Maybe A

  -- products
  module product where
    open import Agda.Primitive using (Level; _⊔_)

    private
      variable
        a b : Level

    -- dependent products
    record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
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

    -- non-dependent products
    _×_ : ∀ (A : Set a) (B : Set b) → Set (a ⊔ b)
    A × B = Σ[ x ∈ A ] B
    infixr 2 _×_

  open negation public
  open decidability public
  open eq public
  open nat public
  open maybe public
  open product public
