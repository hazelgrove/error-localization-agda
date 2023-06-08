open import prelude
open import core

-- zippered types
module hazelnut.typed.ztyp where
  data ZTyp : Set where
    ▹_◃   : (τ  : Typ)  → ZTyp
    _-→₁_ : (τ^ : ZTyp) → (τ : Typ)   → ZTyp
    _-→₂_ : (τ  : Typ)  → (τ^ : ZTyp) → ZTyp

  infixr 25  _-→₁_
  infixr 25  _-→₂_

  -- judgmental cursor erasure
  data erase-τ : (τ^ : ZTyp) → (τ : Typ) → Set where
    ETTop  : ∀ {τ} → erase-τ (▹ τ ◃) τ
    ETArr1 : ∀ {τ₁^ τ₂ τ₁} → (τ₁^◇ : erase-τ τ₁^ τ₁) → erase-τ (τ₁^ -→₁ τ₂) (τ₁ -→ τ₂)
    ETArr2 : ∀ {τ₁ τ₂^ τ₂} → (τ₂^◇ : erase-τ τ₂^ τ₂) → erase-τ (τ₁ -→₂ τ₂^) (τ₁ -→ τ₂)

  -- functional cursor erasure
  _◇τ : (τ^ : ZTyp) → Typ
  ▹ τ ◃      ◇τ = τ
  (τ^ -→₁ τ) ◇τ = (τ^ ◇τ) -→ τ
  (τ -→₂ τ^) ◇τ = τ -→ (τ^ ◇τ)

  -- convert judgmental cursor erasure to functional cursor erasure
  erase-τ→◇ : ∀ {τ^ τ} → erase-τ τ^ τ → τ^ ◇τ ≡ τ
  erase-τ→◇ ETTop          = refl
  erase-τ→◇ (ETArr1 τ₁^◇)
    rewrite erase-τ→◇ τ₁^◇ = refl
  erase-τ→◇ (ETArr2 τ₂^◇)
    rewrite erase-τ→◇ τ₂^◇ = refl
