open import prelude

-- variables contexts
module context where
  _Ctx  : Set → Set
  A Ctx = ℕ → Maybe A

  -- empty context
  ∅ : {A : Set} → A Ctx
  ∅ _ = None
