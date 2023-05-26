open import prelude

open import core.typ

module patterned.ptyp where
  data PTyp : Set where
    num     : PTyp
    bool    : PTyp
    unknown : PTyp
    uswitch : PTyp
    _-→_    : (τ₁ : PTyp) → (τ₂ : PTyp) → PTyp
    _-×_    : (τ₁ : PTyp) → (τ₂ : PTyp) → PTyp

  Typ→PTyp : Typ → PTyp
  Typ→PTyp num = num
  Typ→PTyp bool = bool
  Typ→PTyp unknown = unknown
  Typ→PTyp (τ₁ -→ τ₂) = Typ→PTyp τ₁ -→ Typ→PTyp τ₂
  Typ→PTyp (τ₁ -× τ₂) = Typ→PTyp τ₁ -× Typ→PTyp τ₂
