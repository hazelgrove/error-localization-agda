open import prelude
open import typ
open import uexp renaming (Ctx to UCtx; Subsumable to USubsumable)
open import mexp renaming (Ctx to MCtx; Subsumable to MSubsumable)
open import marking

module unicity where
  ∋→τ-≡ : ∀ {Γ x τ₁ τ₂} → (Γ ∋ x ∶ τ₁) → (Γ ∋ x ∶ τ₂) → τ₁ ≡ τ₂
  ∋→τ-≡ Z         Z         = refl
  ∋→τ-≡ Z         (S x≢x _) = ⊥-elim (x≢x refl)
  ∋→τ-≡ (S x≢x _) Z         = ⊥-elim (x≢x refl)
  ∋→τ-≡ (S _ ∋x)  (S _ ∋x′) = ∋→τ-≡ ∋x ∋x′

  ∋-≡ : ∀ {Γ x τ} → (∋x : Γ ∋ x ∶ τ) → (∋x′ : Γ ∋ x ∶ τ) → ∋x ≡ ∋x′
  ∋-≡ Z           Z                                                           = refl
  ∋-≡ Z           (S x≢x _)                                                   = ⊥-elim (x≢x refl)
  ∋-≡ (S x≢x _)   Z                                                           = ⊥-elim (x≢x refl)
  ∋-≡ (S x≢x′ ∋x) (S x≢x′′ ∋x′)
    rewrite ¬-≡ x≢x′ x≢x′′
          | ∋-≡ ∋x ∋x′ = refl

  ⇒-unicity : ∀ {Γ : UCtx} {e : UExp} {τ₁ τ₂ : Typ} → Γ ⊢ e ⇒ τ₁ → Γ ⊢ e ⇒ τ₂ → τ₁ ≡ τ₂
  ⇒-unicity USHole                 USHole                   = refl
  ⇒-unicity (USVar ∋x)             (USVar ∋x′)              = ∋→τ-≡ ∋x ∋x′
  ⇒-unicity (USLam e⇒τ₁)           (USLam e⇒τ₂)
    rewrite ⇒-unicity e⇒τ₁ e⇒τ₂                             = refl
  ⇒-unicity (USAp e₁⇒τ₁ τ▸ e₂⇐τ₂)  (USAp e₁⇒τ₁′ τ▸′ e₂⇐τ₂′)
    rewrite ⇒-unicity e₁⇒τ₁ e₁⇒τ₁′
    with refl ← ▸-unicity τ▸ τ▸′                            = refl
  ⇒-unicity USNum                  USNum                    = refl
  ⇒-unicity (USPlus e₁⇐num e₂⇐num) (USPlus e₁⇐num′ e₂⇐num′) = refl
  ⇒-unicity USTrue                 USTrue                   = refl
  ⇒-unicity USFalse                USFalse                  = refl
  ⇒-unicity (USIf e₁⇐bool e₂⇒τ₁ e₃⇒τ₂ τ₁⊔τ₂) (USIf e₁⇐bool′ e₂⇒τ₁′ e₃⇒τ₂′ τ₁⊔τ₂′)
    rewrite ⇒-unicity e₂⇒τ₁ e₂⇒τ₁′
          | ⇒-unicity e₃⇒τ₂ e₃⇒τ₂′
          | ⊔-unicity τ₁⊔τ₂ τ₁⊔τ₂′                          = refl

  ↬⇒-τ-unicity : ∀ {Γ : UCtx} {e : UExp} {τ₁ τ₂ : Typ} {ě₁ : ⟦ Γ ⟧ ⊢⇒ τ₁} {ě₂ : ⟦ Γ ⟧ ⊢⇒ τ₂} → Γ ⊢ e ↬⇒ ě₁ → Γ ⊢ e ↬⇒ ě₂ → τ₁ ≡ τ₂
  ↬⇒-τ-unicity ISHole         ISHole          = refl
  ↬⇒-τ-unicity (ISVar ∋x)     (ISVar ∋x′)     = ∋→τ-≡ ∋x ∋x′
  ↬⇒-τ-unicity (ISVar ∋x)     (ISUnbound ∌x)  = ⊥-elim (∌x ∋x)
  ↬⇒-τ-unicity (ISUnbound ∌x) (ISVar ∋x)      = ⊥-elim (∌x ∋x)
  ↬⇒-τ-unicity (ISUnbound ∌x) (ISUnbound ∌x′) = refl
  ↬⇒-τ-unicity (ISLam e↬⇒ě) (ISLam e↬⇒ě′)
    rewrite ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = refl
  ↬⇒-τ-unicity (ISAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (ISAp1 e₁↬⇒ě₁′ τ′▸ e₂↬⇐ě₂′)
    with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = proj₂ (-→-inj (▸-unicity τ▸ τ′▸))
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
      rewrite ∋-≡ ∋x ∋x′ = refl
    ↬⇒-ě-unicity (ISVar ∋x) (ISUnbound ∌x) = ⊥-elim (∌x ∋x)
    ↬⇒-ě-unicity (ISUnbound ∌x) (ISVar ∋x) = ⊥-elim (∌x ∋x)
    ↬⇒-ě-unicity (ISUnbound ∌x) (ISUnbound ∌x′) = refl
    ↬⇒-ě-unicity (ISLam e↬⇒ě) (ISLam e↬⇒ě′)
      rewrite ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′ = refl
    ↬⇒-ě-unicity (ISAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (ISAp1 e₁↬⇒ě₁′ τ▸′ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      with refl ← ▸-unicity τ▸ τ▸′
      with refl ← ▸-≡ τ▸ τ▸′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′ = refl
    ↬⇒-ě-unicity (ISAp1 {τ₁ = τ₁} e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (ISAp2 e₁↬⇒ě₁′ τ!▸ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (ISAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (ISAp1 {τ₁ = τ₁} e₁↬⇒ě₁′ τ▸ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′ = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)
    ↬⇒-ě-unicity (ISAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (ISAp2 e₁↬⇒ě₁′ τ!▸′ e₂↬⇐ě₂′)
      with refl ← ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
      rewrite ↬⇒-ě-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′
            | !▸-≡ τ!▸ τ!▸′ = refl
    ↬⇒-ě-unicity ISNum ISNum = refl
    ↬⇒-ě-unicity (ISPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (ISPlus e₁↬⇐ě₁′ e₂↬⇐ě₂′)
      rewrite ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′ = refl
    ↬⇒-ě-unicity ISTrue ISTrue = refl
    ↬⇒-ě-unicity ISFalse ISFalse = refl
    ↬⇒-ě-unicity (ISIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (ISIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂′)
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
      rewrite ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
            | ↬⇒-ě-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
            | ↬⇒-ě-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
            | ⊔-≡ τ₁⊔τ₂ τ₁⊔τ₂′ = refl
    ↬⇒-ě-unicity (ISIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (ISInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂)
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
    ↬⇒-ě-unicity (ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂) (ISIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂)
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′ = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
    ↬⇒-ě-unicity (ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂) (ISInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂′)
      with refl ← ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
         | refl ← ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
      rewrite ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
            | ↬⇒-ě-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′
            | ↬⇒-ě-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
            | ~̸-≡ τ₁~̸τ₂ τ₁~̸τ₂′ = refl

    USu→MSu-unicity : ∀ {e : UExp} {Γ : UCtx} {τ : Typ} {ě : ⟦ Γ ⟧ ⊢⇒ τ}
                      → (s : USubsumable e) → (e↬⇒ě : Γ ⊢ e ↬⇒ ě) → (e↬⇒ě′ : Γ ⊢ e ↬⇒ ě) → USu→MSu s e↬⇒ě ≡ USu→MSu s e↬⇒ě′
    USu→MSu-unicity SuHole  ISHole      _   = refl
    USu→MSu-unicity SuVar   (ISVar _)     _ = refl
    USu→MSu-unicity SuVar   (ISUnbound _) _ = refl
    USu→MSu-unicity SuAp    (ISAp1 _ _ _) _ = refl
    USu→MSu-unicity SuAp    (ISAp2 _ _ _) _ = refl
    USu→MSu-unicity SuNum   ISNum       _   = refl
    USu→MSu-unicity SuPlus  (ISPlus _ _)  _ = refl
    USu→MSu-unicity SuTrue  ISTrue      _   = refl
    USu→MSu-unicity SuFalse ISFalse     _   = refl

    ↬⇐-ě-unicity : ∀ {Γ : UCtx} {e : UExp} {τ : Typ} {ě₁ : ⟦ Γ ⟧ ⊢⇐ τ} {ě₂ : ⟦ Γ ⟧ ⊢⇐ τ} → Γ ⊢ e ↬⇐ ě₁ → Γ ⊢ e ↬⇐ ě₂ → ě₁ ≡ ě₂
    ↬⇐-ě-unicity (IALam1 τ▸ τ₁~τ₂ e↬⇐ě) (IALam1 τ▸′ τ₁~τ₂′ e↬⇐ě′)
      with refl ← ▸-unicity τ▸ τ▸′
      rewrite ▸-≡ τ▸ τ▸′
            | ~-≡ τ₁~τ₂ τ₁~τ₂′
            | ↬⇐-ě-unicity e↬⇐ě e↬⇐ě′ = refl
    ↬⇐-ě-unicity (IALam1 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~τ₁ e↬⇐ě) (IALam2 τ!▸ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (IALam1 τ▸ τ~τ₁ e↬⇐ě) (IALam3 τ▸′ τ~̸τ₁ e↬⇐ě′)
      with refl ← ▸-unicity τ▸ τ▸′ = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ↬⇐-ě-unicity (IALam2 τ!▸ e↬⇐ě) (IALam1 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~τ₁ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (IALam2 τ!▸ e↬⇐ě) (IALam2 τ!▸′ e↬⇐ě′)
      rewrite !▸-≡ τ!▸ τ!▸′
            | ↬⇐-ě-unicity e↬⇐ě e↬⇐ě′ = refl
    ↬⇐-ě-unicity (IALam2 τ!▸ e↬⇐ě) (IALam3 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~̸τ₁ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (IALam3 τ▸ τ~̸τ₁ e↬⇐ě) (IALam1 τ▸′ τ~τ₁ e↬⇐ě′)
      with refl ← ▸-unicity τ▸ τ▸′ = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ↬⇐-ě-unicity (IALam3 {τ₁ = τ₁} {τ₂ = τ₂} τ▸ τ~̸τ₁ e↬⇐ě) (IALam2 τ!▸ e↬⇐ě′) = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ↬⇐-ě-unicity (IALam3 τ▸ τ~̸τ₁ e↬⇐ě) (IALam3 τ▸′ τ~̸τ₁′ e↬⇐ě′)
      with refl ← ▸-unicity τ▸ τ▸′
      rewrite ▸-≡ τ▸ τ▸′
            | ~̸-≡ τ~̸τ₁ τ~̸τ₁′
            | ↬⇐-ě-unicity e↬⇐ě e↬⇐ě′ = refl
    ↬⇐-ě-unicity (IAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃) (IAIf e₁↬⇐ě₁′ e₂↬⇐ě₂′ e₃↬⇐ě₃′)
      rewrite ↬⇐-ě-unicity e₁↬⇐ě₁ e₁↬⇐ě₁′
            | ↬⇐-ě-unicity e₂↬⇐ě₂ e₂↬⇐ě₂′
            | ↬⇐-ě-unicity e₃↬⇐ě₃ e₃↬⇐ě₃′ = refl
    ↬⇐-ě-unicity (IAInconsistentTypes e↬⇒ě τ~̸τ′ SuHole) (IAInconsistentTypes e↬⇒ě′ τ~̸τ′′ SuHole)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity SuHole e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IAInconsistentTypes e↬⇒ě τ~̸τ′ SuVar) (IAInconsistentTypes e↬⇒ě′ τ~̸τ′′ SuVar)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity SuVar e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IAInconsistentTypes e↬⇒ě τ~̸τ′ SuAp) (IAInconsistentTypes e↬⇒ě′ τ~̸τ′′ SuAp)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity SuAp e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IAInconsistentTypes e↬⇒ě τ~̸τ′ SuNum) (IAInconsistentTypes e↬⇒ě′ τ~̸τ′′ SuNum)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity SuNum e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IAInconsistentTypes e↬⇒ě τ~̸τ′ SuPlus) (IAInconsistentTypes e↬⇒ě′ τ~̸τ′′ SuPlus)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity SuPlus e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IAInconsistentTypes e↬⇒ě τ~̸τ′ SuTrue) (IAInconsistentTypes e↬⇒ě′ τ~̸τ′′ SuTrue)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity SuTrue e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IAInconsistentTypes e↬⇒ě τ~̸τ′ SuFalse) (IAInconsistentTypes e↬⇒ě′ τ~̸τ′′ SuFalse)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~̸-≡ τ~̸τ′ τ~̸τ′′
      rewrite USu→MSu-unicity SuFalse e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IAInconsistentTypes e↬⇒ě τ~̸τ′ s) (IASubsume e↬⇒ě′ τ~τ′ s′)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = ⊥-elim (τ~̸τ′ τ~τ′)
    ↬⇐-ě-unicity (IASubsume e↬⇒ě τ~τ′ s) (IAInconsistentTypes e↬⇒ě′ τ~̸τ′ s′)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′ = ⊥-elim (τ~̸τ′ τ~τ′)
    ↬⇐-ě-unicity (IASubsume e↬⇒ě τ~τ′ SuHole) (IASubsume e↬⇒ě′ τ~τ′′ SuHole)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity SuHole e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IASubsume e↬⇒ě τ~τ′ SuVar) (IASubsume e↬⇒ě′ τ~τ′′ SuVar)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity SuVar e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IASubsume e↬⇒ě τ~τ′ SuAp) (IASubsume e↬⇒ě′ τ~τ′′ SuAp)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity SuAp e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IASubsume e↬⇒ě τ~τ′ SuNum) (IASubsume e↬⇒ě′ τ~τ′′ SuNum)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity SuNum e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IASubsume e↬⇒ě τ~τ′ SuPlus) (IASubsume e↬⇒ě′ τ~τ′′ SuPlus)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity SuPlus e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IASubsume e↬⇒ě τ~τ′ SuTrue) (IASubsume e↬⇒ě′ τ~τ′′ SuTrue)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity SuTrue e↬⇒ě e↬⇒ě′ = refl
    ↬⇐-ě-unicity (IASubsume e↬⇒ě τ~τ′ SuFalse) (IASubsume e↬⇒ě′ τ~τ′′ SuFalse)
      with refl ← ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
      with refl ← ↬⇒-ě-unicity e↬⇒ě e↬⇒ě′
         | refl ← ~-≡ τ~τ′ τ~τ′′
      rewrite USu→MSu-unicity SuFalse e↬⇒ě e↬⇒ě′ = refl
