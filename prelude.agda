module prelude where
  -- equality
  module eq where
    data _≡_ {A : Set} (x : A) : A → Set where
      refl : x ≡ x
    infix 4 _≡_
    {-# BUILTIN EQUALITY _≡_ #-}

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
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

  open eq public
  open nat public
  open maybe public
