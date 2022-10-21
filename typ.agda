open import prelude

-- types
module typ where
  data Typ : Set where
    num     : Typ
    bool    : Typ
    unknown : Typ
    _-→_    : Typ → Typ → Typ

  infixr 25  _-→_

  -- base types
  data _base : (τ : Typ) → Set where
    BNum  : num base
    BBool : bool base

  -- consistency
  data _~_ : (τ₁ τ₂ : Typ) → Set where
    TCRefl     : {τ : Typ} → τ ~ τ
    TCUnknown1 : {τ : Typ} → τ ~ unknown
    TCUnknown2 : {τ : Typ} → unknown ~ τ
    TCArr      : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                → τ₁ ~ τ₁′
                → τ₂ ~ τ₂′
                → τ₁ -→ τ₂ ~ τ₁′ -→ τ₂′

  -- inconsistency
  data _~̸_ : (τ₁ τ₂ : Typ) → Set where
    TICBaseArr1 : {τ τ₁ τ₂ : Typ} {b : τ base}
                 → τ ~̸ τ₁ -→ τ₂
    TICBaseArr2 : {τ τ₁ τ₂ : Typ} {b : τ base}
                 → τ₁ -→ τ₂ ~̸ τ
    TICArr1     : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                 → τ₁ ~̸ τ₁′
                 → τ₁ -→ τ₂ ~̸ τ₁′ -→ τ₂′
    TICArr2     : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                 → τ₂ ~̸ τ₂′
                 → τ₁ -→ τ₂ ~̸ τ₁′ -→ τ₂′

  -- matched arrow
  data _▸_-→_ : (τ τ₁ τ₂ : Typ) → Set where
    TMAHole : unknown ▸ unknown -→ unknown
    TMAArr  : {τ₁ τ₂ : Typ} → τ₁ -→ τ₂ ▸ τ₁ -→ τ₂

  -- lub join
  data _⊔_⇒_ : Typ → Typ → Typ → Set where
    TJUnknown1 : ∀ {τ} → unknown ⊔ τ ⇒ unknown
    TJUnknown2 : ∀ {τ} → τ ⊔ unknown ⇒ unknown
    TJNum       : num ⊔ num ⇒ num
    TJBool      : bool ⊔ bool ⇒ bool
    TJArr       : ∀ {τ₁ τ₂ τ₁′ τ₂′ τ₁″ τ₂″}
                → τ₁ ⊔ τ₁′ ⇒ τ₁″
                → τ₂ ⊔ τ₂′ ⇒ τ₂″
                → τ₁ -→ τ₂ ⊔ τ₁′ -→ τ₂′ ⇒ τ₁″ -→ τ₂″
