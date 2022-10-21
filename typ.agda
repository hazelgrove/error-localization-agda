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
  _⊔_ : (τ₁ τ₂ : Typ) → Maybe Typ
  unknown    ⊔ τ                                     = Some τ
  τ          ⊔ unknown                               = Some τ
  num        ⊔ num                                   = Some num
  bool       ⊔ bool                                  = Some bool
  (τ₁ -→ τ₂) ⊔ (τ₁′ -→ τ₂′) with τ₁ ⊔ τ₁′ | τ₂ ⊔ τ₂′
  ...                          | Some τ₁″ | Some τ₂″ = Some (τ₁″ -→ τ₂″)
  ...                          | _        | _        = None
  τ₁         ⊔ τ₂                                    = None
