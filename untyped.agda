open import prelude
open import typ
open import uexp
open import zexp
open import action

module untyped where
  -- type actions
  data _+_+τ>_ : (τ : ZTyp) → (α : Action) → (τ′ : ZTyp) → Set where
    -- movement
    TMArrChild1 : ∀ {τ₁ τ₂ : Typ}
                 → ▹ τ₁ -→ τ₂ ◃ + move (child 1) +τ> ▹ τ₁ ◃ -→₁ τ₂
    TMArrChild2 : ∀ {τ₁ τ₂ : Typ}
                 → ▹ τ₁ -→ τ₂ ◃ + move (child 2) +τ> τ₁ -→₂ ▹ τ₂ ◃
    TMArrParent1 : ∀ {τ₁ τ₂ : Typ}
                 → ▹ τ₁ ◃ -→₁ τ₂ + move parent +τ> ▹ τ₁ -→ τ₂ ◃
    TMArrParent2 : ∀ {τ₁ τ₂ : Typ}
                 → τ₁ -→₂ ▹ τ₂ ◃ + move parent +τ> ▹ τ₁ -→ τ₂ ◃

    -- deletion
    TDel : ∀ {τ : Typ}
         → ▹ τ ◃ + del +τ> ▹ unknown ◃

    -- construction
    TConArrow1 : ∀ {τ : Typ}
               → ▹ τ ◃ + construct tarrow₁ +τ> τ -→₂ ▹ unknown ◃
    TConArrow2 : ∀ {τ : Typ}
               → ▹ τ ◃ + construct tarrow₂ +τ> ▹ unknown ◃ -→₁ τ
    TConNum    : ▹ unknown ◃ + construct tnum +τ> ▹ num ◃
    TConBool   : ▹ unknown ◃ + construct tbool +τ> ▹ bool ◃

    -- zipper
    TZipArr1 : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
             → τ^ + α +τ> τ^′
             → τ^ -→₁ τ + α +τ> τ^′ -→₁ τ
    TZipArr2 : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
             → τ^ + α +τ> τ^′
             → τ -→₂ τ^ + α +τ> τ -→₂ τ^′
