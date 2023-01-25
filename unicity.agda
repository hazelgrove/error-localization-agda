open import prelude
open import typ
open import uexp renaming (Ctx to UCtx; Subsumable to Subsumable)
open import mexp renaming (Ctx to MCtx; Subsumable to MSubsumable)
open import marking

module unicity where
  ∋→τ≡ : ∀ {Γ x τ₁ τ₂} → (Γ ∋ x ∶ τ₁) → (Γ ∋ x ∶ τ₂) → τ₁ ≡ τ₂
  ∋→τ≡ Z         Z         = refl
  ∋→τ≡ Z         (S x≢x _) = ⊥-elim (x≢x refl)
  ∋→τ≡ (S x≢x _) Z         = ⊥-elim (x≢x refl)
  ∋→τ≡ (S _ ∋x)  (S _ ∋x′) = ∋→τ≡ ∋x ∋x′

  ∋→≡ : ∀ {Γ x τ} → (∋x : Γ ∋ x ∶ τ) → (∋x′ : Γ ∋ x ∶ τ) → ∋x ≡ ∋x′
  ∋→≡ Z           Z                                                           = refl
  ∋→≡ Z           (S x≢x _)                                                   = ⊥-elim (x≢x refl)
  ∋→≡ (S x≢x _)   Z                                                           = ⊥-elim (x≢x refl)
  ∋→≡ (S x≢x′ ∋x) (S x≢x′′ ∋x′)
    with refl ← ¬≡ x≢x′ x≢x′′ | refl ← ∋→≡ ∋x ∋x′ = refl

  ↬⇒-τ-unicity : ∀ {Γ : UCtx} {e : UExp} {τ₁ τ₂ : Typ} {ě₁ : ⟦ Γ ⟧ ⊢⇒ τ₁} {ě₂ : ⟦ Γ ⟧ ⊢⇒ τ₂} → Γ ⊢ e ↬⇒ ě₁ → Γ ⊢ e ↬⇒ ě₂ → τ₁ ≡ τ₂
  ↬⇒-τ-unicity ISHole         ISHole          = refl
  ↬⇒-τ-unicity (ISVar ∋x)     (ISVar ∋x′)     = ∋→τ≡ ∋x ∋x′
  ↬⇒-τ-unicity (ISVar ∋x)     (ISUnbound ∌x)  = ⊥-elim (∌x ∋x)
  ↬⇒-τ-unicity (ISUnbound ∌x) (ISVar ∋x)      = ⊥-elim (∌x ∋x)
  ↬⇒-τ-unicity (ISUnbound ∌x) (ISUnbound ∌x′) = refl
  ↬⇒-τ-unicity (ISLam e↬⇒ě) (ISLam e↬⇒ě′)
    with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = refl
  ↬⇒-τ-unicity (ISAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (ISAp1 e₁↬⇒ě₁′ τ′▸ e₂↬⇐ě₂′)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = proj₂ (≡▸-→→≡ refl τ▸ τ′▸)
  ↬⇒-τ-unicity (ISAp1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (ISAp2 e₁↬⇒ě₁′ τ!▸ e₂↬⇐ě₂′)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ↬⇒-τ-unicity (ISAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (ISAp1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁′ τ▸ e₂↬⇐ě₂′)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ↬⇒-τ-unicity (ISAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (ISAp2 e₁↬⇒ě₁′ τ!▸′ e₂↬⇐ě₂′) = refl
  ↬⇒-τ-unicity ISNum                  ISNum                    = refl
  ↬⇒-τ-unicity (ISPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (ISPlus e₁↬⇐ě₁′ e₂↬⇐ě₂′) = refl
  ↬⇒-τ-unicity ISTrue                 ISTrue                   = refl
  ↬⇒-τ-unicity ISFalse                ISFalse                  = refl
  ↬⇒-τ-unicity (ISIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (ISIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂′)
    with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
       | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊔-unicity τ₁⊔τ₂ τ₁⊔τ₂′
  ↬⇒-τ-unicity (ISIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (ISInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂)
    with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
       | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
  ↬⇒-τ-unicity (ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂) (ISIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂)
    with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
       | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
  ↬⇒-τ-unicity (ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂) (ISInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂′) = refl

  mutual
    ↬⇒-ě-unicity : ∀ {Γ : UCtx} {e : UExp} {τ : Typ} {ě₁ : ⟦ Γ ⟧ ⊢⇒ τ} {ě₂ : ⟦ Γ ⟧ ⊢⇒ τ} → Γ ⊢ e ↬⇒ ě₁ → Γ ⊢ e ↬⇒ ě₂ → ě₁ ≡ ě₂
    ↬⇒-ě-unicity ISHole ISHole = refl
    ↬⇒-ě-unicity (ISVar ∋x) (ISVar ∋x′)
      with refl ← ∋→≡ ∋x ∋x′ = refl
    ↬⇒-ě-unicity (ISVar ∋x) (ISUnbound ∌x) = ⊥-elim (∌x ∋x)
    ↬⇒-ě-unicity (ISUnbound ∌x) (ISVar ∋x) = ⊥-elim (∌x ∋x)
    ↬⇒-ě-unicity (ISUnbound ∌x) (ISUnbound ∌x′) = refl
    ↬⇒-ě-unicity (ISLam e↬⇒ě) (ISLam e↬⇒ě′)
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′ = refl
    ↬⇒-ě-unicity (ISAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (ISAp1 e₁↬⇒ě₁′ τ▸′ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      with refl ← ▸-→-unicity τ▸ τ▸′
      with refl ← ▸-→≡ τ▸ τ▸′
      with refl ← ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      with refl ← ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′ = refl
    ↬⇒-ě-unicity (ISAp1 {τ₁ = τ₁} e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (ISAp2 e₁↬⇒ě₁′ τ!▸ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (ISAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (ISAp1 {τ₁ = τ₁} e₁↬⇒ě₁′ τ▸ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (ISAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (ISAp2 e₁↬⇒ě₁′ τ!▸′ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      with refl ← ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      with refl ← ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′
      with refl ← !▸≡ τ!▸ τ!▸′ = refl
    ↬⇒-ě-unicity ISNum ISNum = refl
    ↬⇒-ě-unicity (ISPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (ISPlus e₁↬⇐ě₁′ e₂↬⇐ě₂′)
      with refl ← ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
         | refl ← ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′ = refl
    ↬⇒-ě-unicity ISTrue ISTrue = refl
    ↬⇒-ě-unicity ISFalse ISFalse = refl
    ↬⇒-ě-unicity (ISIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (ISIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂′)
      with refl ← ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
      with refl ← ↬⇒-ě-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-ě-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
      with refl ← ⊔-≡ τ₁⊔τ₂ τ₁⊔τ₂′ = refl
    ↬⇒-ě-unicity (ISIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (ISInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂)
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
    ↬⇒-ě-unicity (ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂) (ISIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂)
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
    ↬⇒-ě-unicity (ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂) (ISInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂′)
      with refl ← ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
      with refl ← ↬⇒-ě-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-ě-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
      with refl ← ~̸-≡ τ₁~̸τ₂ τ₁~̸τ₂′ = refl

    ↬⇐-ě-unicity : ∀ {Γ : UCtx} {e : UExp} {τ : Typ} {ě₁ : ⟦ Γ ⟧ ⊢⇐ τ} {ě₂ : ⟦ Γ ⟧ ⊢⇐ τ} → Γ ⊢ e ↬⇐ ě₁ → Γ ⊢ e ↬⇐ ě₂ → ě₁ ≡ ě₂
