open import prelude
open import core

open import hazelnut.action
open import hazelnut.typed.ztyp
open import hazelnut.typed.zexp

module hazelnut.typed.action where
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
    TDel : ∀ {τ : Typ} {u : Hole}
         → ▹ τ ◃ + (del u) +τ> ▹ unknown ◃

    -- construction
    TConArrow1 : ∀ {τ : Typ}
               → ▹ τ ◃ + construct tarrow₁ +τ> τ -→₂ ▹ unknown ◃
    TConArrow2 : ∀ {τ : Typ}
               → ▹ τ ◃ + construct tarrow₂ +τ> ▹ unknown ◃ -→₁ τ
    TConNum    : ▹ unknown ◃ + construct tnum +τ> ▹ num ◃
    TConBool   : ▹ unknown ◃ + construct tbool +τ> ▹ bool ◃

    -- zipper
    TZipArr1 : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
             → (τ^+>τ^′ : τ^ + α +τ> τ^′)
             → τ^ -→₁ τ + α +τ> τ^′ -→₁ τ
    TZipArr2 : ∀ {τ^ τ^′ : ZTyp} {τ : Typ} {α : Action}
             → (τ^+>τ^′ : τ^ + α +τ> τ^′)
             → τ -→₂ τ^ + α +τ> τ -→₂ τ^′

  -- iterated type actions
  data _+_+τ>*_ : (τ^ : ZTyp) → (ᾱ : ActionList) → (τ^′ : ZTyp) → Set where
    TIRefl : ∀ {τ^}
           → τ^ + [] +τ>* τ^
    TITyp  : ∀ {τ^ τ^′ τ^″ α ᾱ}
           → (τ^+>τ^′ : τ^ + α +τ> τ^′)
           → (τ^′+>*τ^″ : τ^′ + ᾱ +τ>* τ^″)
           → τ^ + α ∷ ᾱ +τ>* τ^″

  +τ>*-++ : ∀ {τ^ τ^′ τ^″ ᾱ₁ ᾱ₂} → τ^ + ᾱ₁ +τ>* τ^′ → τ^′ + ᾱ₂ +τ>* τ^″ → τ^ + (ᾱ₁ ++ ᾱ₂) +τ>* τ^″
  +τ>*-++ TIRefl                    τ^+>*τ^″  = τ^+>*τ^″
  +τ>*-++ (TITyp τ^+>τ^′ τ^′+>*τ^″) τ^″+>*τ^‴ = TITyp τ^+>τ^′ (+τ>*-++ τ^′+>*τ^″ τ^″+>*τ^‴)

  -- type zippers
  ziplem-tarr1 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ^ -→₁ τ) + ᾱ +τ>* (τ^′ -→₁ τ)
  ziplem-tarr1 TIRefl                    = TIRefl
  ziplem-tarr1 (TITyp τ^+>τ^′ τ^′+>*τ^″) = TITyp (TZipArr1 τ^+>τ^′) (ziplem-tarr1 τ^′+>*τ^″)

  ziplem-tarr2 : ∀ {τ^ τ^′ τ ᾱ} → τ^ + ᾱ +τ>* τ^′ → (τ -→₂ τ^) + ᾱ +τ>* (τ -→₂ τ^′)
  ziplem-tarr2 TIRefl                    = TIRefl
  ziplem-tarr2 (TITyp τ^+>τ^′ τ^′+>*τ^″) = TITyp (TZipArr2 τ^+>τ^′) (ziplem-tarr2 τ^′+>*τ^″)
