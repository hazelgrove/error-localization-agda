open import prelude
open import typ
open import uexp renaming (Ctx to UCtx; Subsumable to USubsumable)
open import mexp renaming (Ctx to MCtx; Subsumable to MSubsumable)
open import marking
open import erasure

module wellformed where
  mutual
    ⊢↬⇒□ : ∀ {Γ : UCtx} {e : UExp} {τ : Typ} {ě : ⟦ Γ ⟧ ⊢⇒ τ} → Γ ⊢ e ↬⇒ ě → ě ⇒□ ≡ e
    ⊢↬⇒□ ISHole           = refl
    ⊢↬⇒□ (ISVar ∋x)       = refl
    ⊢↬⇒□ (ISUnbound ∌x)   = refl
    ⊢↬⇒□ (ISLam e↬⇒ě)
      rewrite ⊢↬⇒□ e↬⇒ě   = refl
    ⊢↬⇒□ (ISAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂)
      rewrite ⊢↬⇒□ e₁↬⇒ě₁
            | ⊢↬⇐□ e₂↬⇐ě₂ = refl
    ⊢↬⇒□ (ISAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂)
      rewrite ⊢↬⇒□ e₁↬⇒ě₁
            | ⊢↬⇐□ e₂↬⇐ě₂ = refl
    ⊢↬⇒□ ISNum            = refl
    ⊢↬⇒□ (ISPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
      rewrite ⊢↬⇐□ e₁↬⇐ě₁
            | ⊢↬⇐□ e₂↬⇐ě₂ = refl
    ⊢↬⇒□ ISTrue           = refl
    ⊢↬⇒□ ISFalse          = refl
    ⊢↬⇒□ (ISIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂)
      rewrite ⊢↬⇐□ e₁↬⇐ě₁
            | ⊢↬⇒□ e₂↬⇒ě₂
            | ⊢↬⇒□ e₃↬⇒ě₃ = refl
    ⊢↬⇒□ (ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂)
      rewrite ⊢↬⇐□ e₁↬⇐ě₁
            | ⊢↬⇒□ e₂↬⇒ě₂
            | ⊢↬⇒□ e₃↬⇒ě₃ = refl

    ⊢↬⇐□ : ∀ {Γ : UCtx} {e : UExp} {τ : Typ} {ě : ⟦ Γ ⟧ ⊢⇐ τ} → Γ ⊢ e ↬⇐ ě → ě ⇐□ ≡ e
    ⊢↬⇐□ (IALam1 τ₁▸ τ~τ₁ e↬⇐ě)
      rewrite ⊢↬⇐□ e↬⇐ě = refl
    ⊢↬⇐□ (IALam2 τ₁!▸ e↬⇐ě)
      rewrite ⊢↬⇐□ e↬⇐ě = refl
    ⊢↬⇐□ (IALam3 τ₁▸ τ~̸τ₁ e↬⇐ě)
      rewrite ⊢↬⇐□ e↬⇐ě = refl
    ⊢↬⇐□ (IAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃)
      rewrite ⊢↬⇐□ e₁↬⇐ě₁
            | ⊢↬⇐□ e₂↬⇐ě₂
            | ⊢↬⇐□ e₃↬⇐ě₃ = refl
    ⊢↬⇐□ (IAInconsistentTypes e↬⇒ě τ~̸τ′ s)
      rewrite ⊢↬⇒□ e↬⇒ě = refl
    ⊢↬⇐□ (IASubsume e↬⇒ě τ~τ′ s)
      rewrite ⊢↬⇒□ e↬⇒ě = refl
