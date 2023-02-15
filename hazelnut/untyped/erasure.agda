open import prelude
open import core

open import hazelnut.untyped.zexp

module hazelnut.untyped.erasure where
  -- judgmental cursor erasure
  data erase-τ : (τ^ : ZTyp) → (τ : Typ) → Set where
    ETTop  : ∀ {τ} → erase-τ (▹ τ ◃) τ
    ETArr1 : ∀ {τ₁^ τ₂ τ₁} → (τ₁^◇ : erase-τ τ₁^ τ₁) → erase-τ (τ₁^ -→₁ τ₂) (τ₁ -→ τ₂)
    ETArr2 : ∀ {τ₁ τ₂^ τ₂} → (τ₂^◇ : erase-τ τ₂^ τ₂) → erase-τ (τ₁ -→₂ τ₂^) (τ₁ -→ τ₂)

  data erase-e : (ê : ZExp) → (e : UExp) → Set where
    EETop   : ∀ {e}
            → erase-e (‵▹ e ◃) e
    EELam1  : ∀ {x τ^ e τ}
            → (τ^◇ : erase-τ τ^ τ)
            → erase-e (‵λ₁ x ∶ τ^ ∙ e) (‵λ x ∶ τ ∙ e)
    EELam2  : ∀ {x τ ê e}
            → (ê◇ : erase-e ê e)
            → erase-e (‵λ₂ x ∶ τ ∙ ê) (‵λ x ∶ τ ∙ e)
    EEAp1   : ∀ {ê₁ e₂ e₁}
            → (ê₁◇ : erase-e ê₁ e₁)
            → erase-e (‵ ê₁ ∙₁ e₂) (‵ e₁ ∙ e₂)
    EEAp2   : ∀ {e₁ ê₂ e₂}
            → (ê₂◇ : erase-e ê₂ e₂)
            → erase-e (‵ e₁ ∙₂ ê₂) (‵ e₁ ∙ e₂)
    EELet1  : ∀ {x ê₁ e₂ e₁}
            → (ê₁◇ : erase-e ê₁ e₁)
            → erase-e (‵ x ←₁ ê₁ ∙ e₂) (‵ x ← e₁ ∙ e₂)
    EELet2  : ∀ {x e₁ ê₂ e₂}
            → (ê₂◇ : erase-e ê₂ e₂)
            → erase-e (‵ x ←₂ e₁ ∙ ê₂) (‵ x ← e₁ ∙ e₂)
    EEPlus1 : ∀ {ê₁ e₂ e₁}
            → (ê₁◇ : erase-e ê₁ e₁)
            → erase-e (‵ ê₁ +₁ e₂) (‵ e₁ + e₂)
    EEPlus2 : ∀ {e₁ ê₂ e₂}
            → (ê₂◇ : erase-e ê₂ e₂)
            → erase-e (‵ e₁ +₂ ê₂) (‵ e₁ + e₂)
    EEIf1   : ∀ {ê₁ e₂ e₃ e₁}
            → (ê₁◇ : erase-e ê₁ e₁)
            → erase-e (‵ ê₁ ∙₁ e₂ ∙ e₃) (‵ e₁ ∙ e₂ ∙ e₃)
    EEIf2   : ∀ {e₁ ê₂ e₃ e₂}
            → (ê₂◇ : erase-e ê₂ e₂)
            → erase-e (‵ e₁ ∙₂ ê₂ ∙ e₃) (‵ e₁ ∙ e₂ ∙ e₃)
    EEIf3   : ∀ {e₁ e₂ ê₃ e₃}
            → (ê₃◇ : erase-e ê₃ e₃)
            → erase-e (‵ e₁ ∙₃ e₂ ∙ ê₃) (‵ e₁ ∙ e₂ ∙ e₃)

  -- functional cursor erasure
  _◇τ : (τ^ : ZTyp) → Typ
  ▹ τ ◃      ◇τ = τ
  (τ^ -→₁ τ) ◇τ = (τ^ ◇τ) -→ τ
  (τ -→₂ τ^) ◇τ = τ -→ (τ^ ◇τ)

  _◇ : (ê : ZExp) → UExp
  ‵▹ e ◃ ◇ = e
  (‵λ₁ x ∶ τ^ ∙ e) ◇ = ‵λ x ∶ (τ^ ◇τ) ∙ e
  (‵λ₂ x ∶ τ ∙ ê)  ◇ = ‵λ x ∶ τ ∙ (ê ◇)
  (‵ ê ∙₁ e)       ◇ = ‵ (ê ◇) ∙ e
  (‵ e ∙₂ ê)       ◇ = ‵ e ∙ (ê ◇)
  (‵ x ←₁ ê ∙ e)   ◇ = ‵ x ← (ê ◇) ∙ e
  (‵ x ←₂ e ∙ ê)   ◇ = ‵ x ← e ∙ (ê ◇)
  (‵ ê +₁ e)       ◇ = ‵ (ê ◇) + e
  (‵ e +₂ ê)       ◇ = ‵ e + (ê ◇)
  (‵ ê ∙₁ e₂ ∙ e₃) ◇ = ‵ (ê ◇) ∙ e₂ ∙ e₃
  (‵ e₁ ∙₂ ê ∙ e₃) ◇ = ‵ e₁ ∙ (ê ◇) ∙ e₃
  (‵ e₁ ∙₃ e₂ ∙ ê) ◇ = ‵ e₁ ∙ e₂ ∙ (ê ◇)

  -- convert judgmental cursor erasure to functional cursor erasure
  erase-τ→◇ : ∀ {τ^ τ} → erase-τ τ^ τ → τ^ ◇τ ≡ τ
  erase-τ→◇ ETTop          = refl
  erase-τ→◇ (ETArr1 τ₁^◇)
    rewrite erase-τ→◇ τ₁^◇ = refl
  erase-τ→◇ (ETArr2 τ₂^◇)
    rewrite erase-τ→◇ τ₂^◇ = refl

  erase-e→◇ : ∀ {ê e} → erase-e ê e → ê ◇ ≡ e
  erase-e→◇ EETop = refl
  erase-e→◇ (EELam1 τ^◇)
    rewrite erase-τ→◇ τ^◇ = refl
  erase-e→◇ (EELam2 ê◇)
    rewrite erase-e→◇ ê◇ = refl
  erase-e→◇ (EEAp1 ê◇)
    rewrite erase-e→◇ ê◇ = refl
  erase-e→◇ (EEAp2 ê◇)
    rewrite erase-e→◇ ê◇ = refl
  erase-e→◇ (EELet1 ê◇)
    rewrite erase-e→◇ ê◇ = refl
  erase-e→◇ (EELet2 ê◇)
    rewrite erase-e→◇ ê◇ = refl
  erase-e→◇ (EEPlus1 ê◇)
    rewrite erase-e→◇ ê◇ = refl
  erase-e→◇ (EEPlus2 ê◇)
    rewrite erase-e→◇ ê◇ = refl
  erase-e→◇ (EEIf1 ê◇)
    rewrite erase-e→◇ ê◇ = refl
  erase-e→◇ (EEIf2 ê◇)
    rewrite erase-e→◇ ê◇ = refl
  erase-e→◇ (EEIf3 ê◇)
    rewrite erase-e→◇ ê◇ = refl

  -- convert functional cursor erasure to judgmental cursor erasure
  ◇τ→erase : ∀ {τ^ τ} → τ^ ◇τ ≡ τ → erase-τ τ^ τ
  ◇τ→erase {▹ τ ◃} refl                      = ETTop
  ◇τ→erase {τ₁^ -→₁ τ₂} refl
    with τ₁^◇ ← ◇τ→erase {τ₁^} {τ₁^ ◇τ} refl = ETArr1 τ₁^◇
  ◇τ→erase {τ₁ -→₂ τ₂^} refl
    with τ₂^◇ ← ◇τ→erase {τ₂^} {τ₂^ ◇τ} refl = ETArr2 τ₂^◇

  ◇e→erase : ∀ {ê e} → ê ◇ ≡ e → erase-e ê e
  ◇e→erase {‵▹ e ◃} refl                  = EETop
  ◇e→erase {‵λ₁ x ∶ τ^ ∙ e} refl
    with τ^◇ ← ◇τ→erase {τ^} {τ^ ◇τ} refl = EELam1 τ^◇
  ◇e→erase {‵λ₂ x ∶ τ ∙ ê} refl
    with ê◇ ← ◇e→erase {ê} {ê ◇} refl     = EELam2 ê◇
  ◇e→erase {‵ ê ∙₁ e} refl
    with ê◇ ← ◇e→erase {ê} {ê ◇} refl     = EEAp1 ê◇
  ◇e→erase {‵ e ∙₂ ê} refl
    with ê◇ ← ◇e→erase {ê} {ê ◇} refl     = EEAp2 ê◇
  ◇e→erase {‵ x ←₁ ê ∙ e} refl
    with ê◇ ← ◇e→erase {ê} {ê ◇} refl     = EELet1 ê◇
  ◇e→erase {‵ x ←₂ e ∙ ê} refl
    with ê◇ ← ◇e→erase {ê} {ê ◇} refl     = EELet2 ê◇
  ◇e→erase {‵ ê +₁ e} refl
    with ê◇ ← ◇e→erase {ê} {ê ◇} refl     = EEPlus1 ê◇
  ◇e→erase {‵ e +₂ ê} refl
    with ê◇ ← ◇e→erase {ê} {ê ◇} refl     = EEPlus2 ê◇
  ◇e→erase {‵ ê ∙₁ e₂ ∙ e₃} refl
    with ê◇ ← ◇e→erase {ê} {ê ◇} refl     = EEIf1 ê◇
  ◇e→erase {‵ e₁ ∙₂ ê ∙ e₃} refl
    with ê◇ ← ◇e→erase {ê} {ê ◇} refl     = EEIf2 ê◇
  ◇e→erase {‵ e₁ ∙₃ e₂ ∙ ê} refl
    with ê◇ ← ◇e→erase {ê} {ê ◇} refl     = EEIf3 ê◇
