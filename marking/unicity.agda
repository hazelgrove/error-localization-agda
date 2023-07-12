open import prelude
open import core

open import marking.marking

module marking.unicity where
  ↬⇒-τ-unicity : ∀ {Γ : Ctx} {e : UExp} {τ₁ τ₂ : Typ} {ě₁ : Γ ⊢⇒ τ₁} {ě₂ : Γ ⊢⇒ τ₂}
               → Γ ⊢ e ↬⇒ ě₁
               → Γ ⊢ e ↬⇒ ě₂
               → τ₁ ≡ τ₂
  ↬⇒-τ-unicity           MKSHole         MKSHole          = refl
  ↬⇒-τ-unicity           (MKSVar ∋x)     (MKSVar ∋x′)     = ∋→τ-≡ ∋x ∋x′
  ↬⇒-τ-unicity {τ₁ = τ₁} (MKSVar ∋x)     (MKSFree ∌x)  = ⊥-elim (∌x ⟨ τ₁ , ∋x ⟩)
  ↬⇒-τ-unicity {τ₂ = τ₂} (MKSFree ∌x) (MKSVar ∋x)      = ⊥-elim (∌x ⟨ τ₂ , ∋x ⟩)
  ↬⇒-τ-unicity           (MKSFree ∌x) (MKSFree ∌x′) = refl
  ↬⇒-τ-unicity (MKSLam e↬⇒ě) (MKSLam e↬⇒ě′)
    rewrite ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = refl
  ↬⇒-τ-unicity (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp1 e₁↬⇒ě₁′ τ′▸ e₂↬⇐ě₂′)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = proj₂ (-→-inj (▸-→-unicity τ▸ τ′▸))
  ↬⇒-τ-unicity (MKSAp1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁′ τ!▸ e₂↬⇐ě₂′)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ↬⇒-τ-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁′ τ▸ e₂↬⇐ě₂′)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ↬⇒-τ-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁′ τ!▸′ e₂↬⇐ě₂′) = refl
  ↬⇒-τ-unicity (MKSLet e₁↬⇒ě₁ e₂↬⇒ě₂) (MKSLet e₁↬⇒ě₁′ e₂↬⇒ě₂′)
    rewrite ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
    rewrite ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′ = refl
  ↬⇒-τ-unicity MKSNum                  MKSNum                    = refl
  ↬⇒-τ-unicity (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (MKSPlus e₁↬⇐ě₁′ e₂↬⇐ě₂′) = refl
  ↬⇒-τ-unicity MKSTrue                 MKSTrue                   = refl
  ↬⇒-τ-unicity MKSFalse                MKSFalse                  = refl
  ↬⇒-τ-unicity (MKSIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (MKSIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂′)
    with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
       | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊔-unicity τ₁⊔τ₂ τ₁⊔τ₂′
  ↬⇒-τ-unicity (MKSIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (MKSInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂)
    with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
       | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
  ↬⇒-τ-unicity (MKSInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂) (MKSIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂)
    with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
       | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
  ↬⇒-τ-unicity (MKSInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂) (MKSInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂′) = refl
  ↬⇒-τ-unicity (MKSPair e₁↬⇒ě₁ e₂↬⇒ě₂) (MKSPair e₁↬⇒ě₁′ e₂↬⇒ě₂′)
    rewrite ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
    rewrite ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′ = refl
  ↬⇒-τ-unicity (MKSProjL1 e↬⇒ě τ▸) (MKSProjL1 e↬⇒ě′ τ′▸)
    with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = proj₁ (-×-inj (▸-×-unicity τ▸ τ′▸))
  ↬⇒-τ-unicity (MKSProjL1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁ τ▸) (MKSProjL2 e₁↬⇒ě₁′ τ!▸)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ↬⇒-τ-unicity (MKSProjL2 e₁↬⇒ě₁ τ!▸) (MKSProjL1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁′ τ▸)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ↬⇒-τ-unicity (MKSProjL2 e₁↬⇒ě₁ τ!▸) (MKSProjL2 e₁↬⇒ě₁′ τ!▸′) = refl
  ↬⇒-τ-unicity (MKSProjR1 e↬⇒ě τ▸) (MKSProjR1 e↬⇒ě′ τ′▸)
    with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = proj₂ (-×-inj (▸-×-unicity τ▸ τ′▸))
  ↬⇒-τ-unicity (MKSProjR1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁ τ▸) (MKSProjR2 e₁↬⇒ě₁′ τ!▸)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ↬⇒-τ-unicity (MKSProjR2 e₁↬⇒ě₁ τ!▸) (MKSProjR1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁′ τ▸)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ↬⇒-τ-unicity (MKSProjR2 e₁↬⇒ě₁ τ!▸) (MKSProjR2 e₁↬⇒ě₁′ τ!▸′) = refl

  mutual
    ↬⇒-ě-unicity : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě₁ : Γ ⊢⇒ τ} {ě₂ : Γ ⊢⇒ τ}
                 → Γ ⊢ e ↬⇒ ě₁
                 → Γ ⊢ e ↬⇒ ě₂
                 → ě₁ ≡ ě₂
    ↬⇒-ě-unicity MKSHole MKSHole = refl
    ↬⇒-ě-unicity (MKSVar ∋x) (MKSVar ∋x′)
      rewrite ∋-≡ ∋x ∋x′ = refl
    ↬⇒-ě-unicity (MKSVar ∋x) (MKSFree ∌x) = ⊥-elim (∌x ⟨ unknown , ∋x ⟩)
    ↬⇒-ě-unicity (MKSFree ∌x) (MKSVar ∋x) = ⊥-elim (∌x ⟨ unknown , ∋x ⟩)
    ↬⇒-ě-unicity (MKSFree ∌x) (MKSFree ∌x′)
      rewrite assimilation ∌x ∌x′ = refl
    ↬⇒-ě-unicity (MKSLam e↬⇒ě) (MKSLam e↬⇒ě′)
      rewrite ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′ = refl
    ↬⇒-ě-unicity (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp1 e₁↬⇒ě₁′ τ▸′ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      with refl ← ▸-→-unicity τ▸ τ▸′
      with refl ← ▸-→-≡ τ▸ τ▸′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′ = refl
    ↬⇒-ě-unicity (MKSAp1 {τ₁ = τ₁} e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁′ τ!▸ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp1 {τ₁ = τ₁} e₁↬⇒ě₁′ τ▸ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (MKSAp2 e₁↬⇒ě₁′ τ!▸′ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′
            | !▸-→-≡ τ!▸ τ!▸′ = refl
    ↬⇒-ě-unicity (MKSLet e₁↬⇒ě₁ e₂↬⇒ě₂) (MKSLet e₁↬⇒ě₁′ e₂↬⇒ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      rewrite ↬⇒-ě-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′ = refl
    ↬⇒-ě-unicity MKSNum MKSNum = refl
    ↬⇒-ě-unicity (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (MKSPlus e₁↬⇐ě₁′ e₂↬⇐ě₂′)
      rewrite ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′ = refl
    ↬⇒-ě-unicity MKSTrue MKSTrue = refl
    ↬⇒-ě-unicity MKSFalse MKSFalse = refl
    ↬⇒-ě-unicity (MKSIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (MKSIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂′)
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
      rewrite ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
            | ↬⇒-ě-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
            | ↬⇒-ě-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
            | ⊔-≡ τ₁⊔τ₂ τ₁⊔τ₂′ = refl
    ↬⇒-ě-unicity (MKSIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (MKSInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂)
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
    ↬⇒-ě-unicity (MKSInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂) (MKSIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂)
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
    ↬⇒-ě-unicity (MKSInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂) (MKSInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂′)
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
      rewrite ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
            | ↬⇒-ě-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
            | ↬⇒-ě-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
            | ~̸-≡ τ₁~̸τ₂ τ₁~̸τ₂′ = refl
    ↬⇒-ě-unicity (MKSPair e₁↬⇒ě₁ e₂↬⇒ě₂) (MKSPair e₁↬⇒ě₁′ e₂↬⇒ě₂′)
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
            | ↬⇒-ě-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
            = refl
    ↬⇒-ě-unicity (MKSProjL1 e₁↬⇒ě₁ τ▸) (MKSProjL1 e₁↬⇒ě₁′ τ▸′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      with refl ← ▸-×-unicity τ▸ τ▸′
      with refl ← ▸-×-≡ τ▸ τ▸′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = refl
    ↬⇒-ě-unicity (MKSProjL1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁ τ▸) (MKSProjL2 e₁↬⇒ě₁′ τ!▸)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (MKSProjL2 e₁↬⇒ě₁ τ!▸) (MKSProjL1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁′ τ▸)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (MKSProjL2 e₁↬⇒ě₁ τ!▸) (MKSProjL2 e₁↬⇒ě₁′ τ!▸′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
            | !▸-×-≡ τ!▸ τ!▸′ = refl
    ↬⇒-ě-unicity (MKSProjR1 e₁↬⇒ě₁ τ▸) (MKSProjR1 e₁↬⇒ě₁′ τ▸′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      with refl ← ▸-×-unicity τ▸ τ▸′
      with refl ← ▸-×-≡ τ▸ τ▸′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = refl
    ↬⇒-ě-unicity (MKSProjR1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁ τ▸) (MKSProjR2 e₁↬⇒ě₁′ τ!▸)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (MKSProjR2 e₁↬⇒ě₁ τ!▸) (MKSProjR1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇒ě₁′ τ▸)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (MKSProjR2 e₁↬⇒ě₁ τ!▸) (MKSProjR2 e₁↬⇒ě₁′ τ!▸′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
            | !▸-×-≡ τ!▸ τ!▸′ = refl

    USu→MSu-unicity : ∀ {e : UExp} {Γ : Ctx} {τ : Typ} {ě : Γ ⊢⇒ τ}
                      → (s : USubsumable e)
                      → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
                      → (e↬⇒ě′ : Γ ⊢ e ↬⇒ ě)
                      → USu→MSu s e↬⇒ě ≡ USu→MSu s e↬⇒ě′
    USu→MSu-unicity USuHole  MKSHole         _ = refl
    USu→MSu-unicity USuVar   (MKSVar _)      _ = refl
    USu→MSu-unicity USuVar   (MKSFree _)  _ = refl
    USu→MSu-unicity USuAp    (MKSAp1 _ _ _)  _ = refl
    USu→MSu-unicity USuAp    (MKSAp2 _ _ _)  _ = refl
    USu→MSu-unicity USuNum   MKSNum          _ = refl
    USu→MSu-unicity USuPlus  (MKSPlus _ _)   _ = refl
    USu→MSu-unicity USuTrue  MKSTrue         _ = refl
    USu→MSu-unicity USuFalse MKSFalse        _ = refl
    USu→MSu-unicity USuProjL (MKSProjL1 _ _) _ = refl
    USu→MSu-unicity USuProjL (MKSProjL2 _ _) _ = refl
    USu→MSu-unicity USuProjR (MKSProjR1 _ _) _ = refl
    USu→MSu-unicity USuProjR (MKSProjR2 _ _) _ = refl

    ↬⇐-ě-unicity : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě₁ : Γ ⊢⇐ τ} {ě₂ : Γ ⊢⇐ τ}
                 → Γ ⊢ e ↬⇐ ě₁
                 → Γ ⊢ e ↬⇐ ě₂
                 → ě₁ ≡ ě₂
    ↬⇐-ě-unicity (MKALam1 τ▸ τ₁~τ₂ e↬⇐ě) (MKALam1 τ▸′ τ₁~τ₂′ e↬⇐ě′)
      with refl ← ▸-→-unicity τ▸ τ▸′
      rewrite ▸-→-≡ τ▸ τ▸′
            | ~-≡ τ₁~τ₂ τ₁~τ₂′
            | ↬⇐-ě-unicity e↬⇐ě e↬⇐ě′ = refl
    ↬⇐-ě-unicity (MKALam1 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~τ₁ e↬⇐ě) (MKALam2 τ!▸ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (MKALam1 τ▸ τ~τ₁ e↬⇐ě) (MKALam3 τ▸′ τ~̸τ₁ e↬⇐ě′)
      with refl ← ▸-→-unicity τ▸ τ▸′ = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ↬⇐-ě-unicity (MKALam2 τ!▸ e↬⇐ě) (MKALam1 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~τ₁ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (MKALam2 τ!▸ e↬⇐ě) (MKALam2 τ!▸′ e↬⇐ě′)
      rewrite !▸-→-≡ τ!▸ τ!▸′
            | ↬⇐-ě-unicity e↬⇐ě e↬⇐ě′ = refl
    ↬⇐-ě-unicity (MKALam2 τ!▸ e↬⇐ě) (MKALam3 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~̸τ₁ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (MKALam3 τ▸ τ~̸τ₁ e↬⇐ě) (MKALam1 τ▸′ τ~τ₁ e↬⇐ě′)
      with refl ← ▸-→-unicity τ▸ τ▸′ = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ↬⇐-ě-unicity (MKALam3 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~̸τ₁ e↬⇐ě) (MKALam2 τ!▸ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (MKALam3 τ▸ τ~̸τ₁ e↬⇐ě) (MKALam3 τ▸′ τ~̸τ₁′ e↬⇐ě′)
      with refl ← ▸-→-unicity τ▸ τ▸′
      rewrite ▸-→-≡ τ▸ τ▸′
            | ~̸-≡ τ~̸τ₁ τ~̸τ₁′
            | ↬⇐-ě-unicity e↬⇐ě e↬⇐ě′ = refl
    ↬⇐-ě-unicity (MKALet e₁↬⇒ě₁ e₂↬⇐ě₂) (MKALet e₁↬⇒ě₁′ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      rewrite ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′ = refl
    ↬⇐-ě-unicity (MKAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃) (MKAIf e₁↬⇐ě₁′ e₂↬⇐ě₂′ e₃↬⇐ě₃′)
      rewrite ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′
            | ↬⇐-ě-unicity e₃↬⇐ě₃ e₃↬⇐ě₃′ = refl
    ↬⇐-ě-unicity (MKAPair1 e₁↬⇐ě₁ e₂↬⇐ě₂ τ▸) (MKAPair1 e₁↬⇐ě₁′ e₂↬⇐ě₂′ τ▸′)
      with refl ← ▸-×-unicity τ▸ τ▸′
      rewrite ▸-×-≡ τ▸ τ▸′
            | ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′ = refl
    ↬⇐-ě-unicity (MKAPair1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇐ě₁ e₂↬⇐ě₂ τ▸) (MKAPair2 e₁↬⇐ě₁′ e₂↬⇐ě₂′ τ!▸) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (MKAPair2 e₁↬⇐ě₁ e₂↬⇐ě₂ τ!▸) (MKAPair1 {τ₁ = τ₁} {τ₂ = τ₂} e₁↬⇐ě₁′ e₂↬⇐ě₂′ τ▸) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (MKAPair2 e₁↬⇐ě₁ e₂↬⇐ě₂ τ!▸) (MKAPair2 e₁↬⇐ě₁′ e₂↬⇐ě₂′ τ!▸′)
      rewrite !▸-×-≡ τ!▸ τ!▸′
            | ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuHole) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuHole)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuHole e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuVar) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuVar)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuVar e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuAp) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuAp)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuAp e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuNum) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuNum)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuNum e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuPlus) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuPlus)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuPlus e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuTrue) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuTrue)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuTrue e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuFalse) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuFalse)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuFalse e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuProjL) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuProjL)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuProjL e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ USuProjR) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′′ USuProjR)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity USuProjR e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKAInconsistentTypes e↬⇒ě τ~̸τ′ s) (MKASubsume e↬⇒ě′ τ~τ′ s′)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = ⊥-elim (τ~̸τ′ τ~τ′)
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ s) (MKAInconsistentTypes e↬⇒ě′ τ~̸τ′ s′)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = ⊥-elim (τ~̸τ′ τ~τ′)
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuHole) (MKASubsume e↬⇒ě′ τ~τ′′ USuHole)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuHole e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuVar) (MKASubsume e↬⇒ě′ τ~τ′′ USuVar)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuVar e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuAp) (MKASubsume e↬⇒ě′ τ~τ′′ USuAp)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuAp e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuNum) (MKASubsume e↬⇒ě′ τ~τ′′ USuNum)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuNum e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuPlus) (MKASubsume e↬⇒ě′ τ~τ′′ USuPlus)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuPlus e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuTrue) (MKASubsume e↬⇒ě′ τ~τ′′ USuTrue)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuTrue e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuFalse) (MKASubsume e↬⇒ě′ τ~τ′′ USuFalse)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuFalse e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuProjL) (MKASubsume e↬⇒ě′ τ~τ′′ USuProjL)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuProjL e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (MKASubsume e↬⇒ě τ~τ′ USuProjR) (MKASubsume e↬⇒ě′ τ~τ′′ USuProjR)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity USuProjR e↬⇒ě e↬⇒ě′ = refl

  ↬⇒-unicity-sig : ∀ {Γ : Ctx} {τ₁ τ₂ : Typ} → τ₁ ≡ τ₂ → Γ ⊢⇒ τ₁ → Γ ⊢⇒ τ₂ → Set
  ↬⇒-unicity-sig refl e₁ e₂ = e₁ ≡ e₂

  ↬⇒-unicity : ∀ {Γ : Ctx} {e : UExp} {τ₁ τ₂ : Typ} {ě₁ : Γ ⊢⇒ τ₁} {ě₂ : Γ ⊢⇒ τ₂}
             → (e↬⇒ě₁ : Γ ⊢ e ↬⇒ ě₁)
             → (e↬⇒ě₂ : Γ ⊢ e ↬⇒ ě₂)
             → Σ[ τ₁≡τ₂ ∈ τ₁ ≡ τ₂ ] ↬⇒-unicity-sig τ₁≡τ₂ ě₁ ě₂
  ↬⇒-unicity e↬⇒ě₁ e↬⇒ě₂
    with refl ← ↬⇒-τ-unicity e↬⇒ě₁ e↬⇒ě₂
       = ⟨ refl , ↬⇒-ě-unicity e↬⇒ě₁ e↬⇒ě₂ ⟩

  ↬⇐-unicity : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě₁ : Γ ⊢⇐ τ} {ě₂ : Γ ⊢⇐ τ}
             → Γ ⊢ e ↬⇐ ě₁
             → Γ ⊢ e ↬⇐ ě₂
             → ě₁ ≡ ě₂
  ↬⇐-unicity = ↬⇐-ě-unicity
