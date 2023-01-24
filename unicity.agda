open import prelude
open import typ
open import uexp renaming (Ctx to UCtx; Subsumable to Subsumable)
open import mexp renaming (Ctx to MCtx; Subsumable to MSubsumable)
open import marking

module unicity where
  ↬⇒-τ-unicity : ∀ {Γ : UCtx} {e : UExp} {τ₁ τ₂ : Typ} {ě₁ : ⟦ Γ ⟧ ⊢⇒ τ₁} {ě₂ : ⟦ Γ ⟧ ⊢⇒ τ₂} → Γ ⊢ e ↬⇒ ě₁ → Γ ⊢ e ↬⇒ ě₂ → τ₁ ≡ τ₂
  ↬⇒-τ-unicity ISHole ISHole = refl
  ↬⇒-τ-unicity (ISVar ∋x) (ISVar ∋x′) = {! !}
  ↬⇒-τ-unicity (ISVar ∋x) (ISUnbound ∌x) = {! !}
  ↬⇒-τ-unicity (ISUnbound ∌x) (ISVar ∋x) = {! !}
  ↬⇒-τ-unicity (ISUnbound ∌x) (ISUnbound ∌x′) = {! !}
  ↬⇒-τ-unicity (ISLam e↬⇒ě) (ISLam e↬⇒ě′) with ↬⇒-τ-unicity e↬⇒ě e↬⇒ě′
  ...                                        | refl = refl
  ↬⇒-τ-unicity (ISAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (ISAp1 e₁↬⇒ě₁′ τ′▸ e₂↬⇐ě₂′) with ↬⇒-τ-unicity e₁↬⇒ě₁ e₁↬⇒ě₁′
  ...                                                                  | τ≡τ′ = proj₂ (≡▸-→→≡ τ≡τ′ τ▸ τ′▸)
  ↬⇒-τ-unicity (ISAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (ISAp2 e₁↬⇒ě₁′ τ!▸ e₂↬⇐ě₂′) = {! !}
  ↬⇒-τ-unicity (ISAp2 a τ!▸ x) (ISAp1 b τ▸ x₁) = {! !}
  ↬⇒-τ-unicity (ISAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂) (ISAp2 e₁↬⇒ě₁′ τ!▸′ e₂↬⇐ě₂′) = refl
  ↬⇒-τ-unicity ISNum ISNum = refl
  ↬⇒-τ-unicity (ISPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (ISPlus e₁↬⇐ě₁′ e₂↬⇐ě₂′) = refl
  ↬⇒-τ-unicity ISTrue ISTrue = refl
  ↬⇒-τ-unicity ISFalse ISFalse = refl
  ↬⇒-τ-unicity (ISIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (ISIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂′) with ↬⇒-τ-unicity e₂↬⇒ě₂ e₂↬⇒ě₂′ | ↬⇒-τ-unicity e₃↬⇒ě₃ e₃↬⇒ě₃′
  ...                                                                                     | refl                        | refl = ⊔-unicity τ₁⊔τ₂ τ₁⊔τ₂′
  ↬⇒-τ-unicity (ISIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (ISInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂) = {! !}
  ↬⇒-τ-unicity (ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (ISIf e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁⊔τ₂′) = {! !}
  ↬⇒-τ-unicity (ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂) (ISInconsistentBranches e₁↬⇐ě₁′ e₂↬⇒ě₂′ e₃↬⇒ě₃′ τ₁~̸τ₂′) = {! !}

  -- mutual
    -- ↬⇒-ě-unicity : ∀ {Γ : UCtx} {e : UExp} {τ : Typ} {ě₁ : ⟦ Γ ⟧ ⊢⇒ τ} {ě₂ : ⟦ Γ ⟧ ⊢⇒ τ} → Γ ⊢ e ↬⇒ ě₁ → Γ ⊢ e ↬⇒ ě₂ → ě₁ ≡ ě₂
