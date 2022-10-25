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

  _!▸ : Typ → Set
  τ !▸ = ∀ {τ₁ τ₂} → (τ ▸ τ₁ -→ τ₂) → ⊥

  -- lub join
  data _⊔_⇒_ : (τ₁ τ₂ τ : Typ) → Set where
    TJUnknown1 : {τ : Typ} → τ ⊔ unknown ⇒ unknown
    TJUnknown2 : {τ : Typ} → unknown ⊔ τ ⇒ unknown
    TJNum      : num ⊔ num ⇒ num
    TJBool     : bool ⊔ bool ⇒ bool
    TJArr      : {τ₁ τ₂ τ₁′ τ₂′ τ₁″ τ₂″ : Typ}
                → τ₁ ⊔ τ₁′ ⇒ τ₁″
                → τ₂ ⊔ τ₂′ ⇒ τ₂″
                → τ₁ -→ τ₂ ⊔ τ₁′ -→ τ₂′ ⇒ τ₁″ -→ τ₂″

  -→≡ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₁ ≡ τ₁′ → τ₂ ≡ τ₂′ → τ₁ -→ τ₂ ≡ τ₁′ -→ τ₂′
  -→≡ refl refl = refl

  ⊔-unicity : ∀ {τ₁ τ₂ τ τ′} → τ₁ ⊔ τ₂ ⇒ τ → τ₁ ⊔ τ₂ ⇒ τ′ → τ ≡ τ′ 
  ⊔-unicity TJUnknown1 TJUnknown1                         = refl
  ⊔-unicity TJUnknown1 TJUnknown2                         = refl
  ⊔-unicity TJUnknown2 TJUnknown1                         = refl
  ⊔-unicity TJUnknown2 TJUnknown2                         = refl
  ⊔-unicity TJNum TJNum                                   = refl
  ⊔-unicity TJBool TJBool                                 = refl
  ⊔-unicity (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) (TJArr τ₁⊔τ₁′′ τ₂⊔τ₂′′) = -→≡ (⊔-unicity τ₁⊔τ₁′ τ₁⊔τ₁′′) (⊔-unicity τ₂⊔τ₂′ τ₂⊔τ₂′′)

  ⊔-iff-~ : ∀ {τ τ₁ τ₂} → τ₁ ⊔ τ₂ ⇒ τ → τ₁ ~ τ₂
  ⊔-iff-~ TJUnknown1            = TCUnknown1
  ⊔-iff-~ TJUnknown2            = TCUnknown2
  ⊔-iff-~ TJNum                 = TCRefl
  ⊔-iff-~ TJBool                = TCRefl
  ⊔-iff-~ (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) = TCArr (⊔-iff-~ τ₁⊔τ₁′) (⊔-iff-~ τ₂⊔τ₂′)
