module prelude where
  module eq where
    -- equality
    data _≡_ {A : Set} (x : A) : A → Set where
      refl : x ≡ x
    infix 4 _≡_
    {-# BUILTIN EQUALITY _≡_ #-}

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

  module nat where
    -- naturals
    data ℕ : Set where
      zero : ℕ
      suc  : ℕ → ℕ
    {-# BUILTIN NATURAL ℕ #-}

  open eq public
  open nat public
