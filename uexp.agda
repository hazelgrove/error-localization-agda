open import prelude
open import typ using (Typ)

-- unmarked expressions
module uexp where
  data UExp : Set where
    ‵⦇-⦈[_] : ℕ → UExp
    ‵_      : ℕ → UExp
    ‵λ_∶_∙_ : ℕ → Typ → UExp → UExp
    ‵_∘_    : UExp → UExp → UExp
    ‵n_     : ℕ → UExp
    ‵_+_    : UExp → UExp → UExp
    ‵tt     : UExp
    ‵ff     : UExp
    ‵_∙_∙_  : UExp → UExp → UExp → UExp
