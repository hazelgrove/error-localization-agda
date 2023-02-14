open import prelude
open import typ
open import uexp renaming (Ctx to UCtx; Subsumable to USubsumable)
open import mexp renaming (Ctx to MCtx; Subsumable to MSubsumable)
open import marking
open import erasure

module wellformed where
  mutual
    -- marking preserves syntactic structure
    ↬⇒□ : ∀ {Γ : UCtx} {e : UExp} {τ : Typ} {ě : ⟦ Γ ⟧ ⊢⇒ τ} → Γ ⊢ e ↬⇒ ě → ě ⇒□ ≡ e
    ↬⇒□ ISHole           = refl
    ↬⇒□ (ISVar ∋x)       = refl
    ↬⇒□ (ISUnbound ∌x)   = refl
    ↬⇒□ (ISLam e↬⇒ě)
      rewrite ↬⇒□ e↬⇒ě   = refl
    ↬⇒□ (ISAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂)
      rewrite ↬⇒□ e₁↬⇒ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇒□ (ISAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂)
      rewrite ↬⇒□ e₁↬⇒ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇒□ (ISLet e₁↬⇒ě₁ e₂↬⇒ě₂)
      rewrite ↬⇒□ e₁↬⇒ě₁
            | ↬⇒□ e₂↬⇒ě₂ = refl
    ↬⇒□ ISNum            = refl
    ↬⇒□ (ISPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇒□ ISTrue           = refl
    ↬⇒□ ISFalse          = refl
    ↬⇒□ (ISIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇒□ e₂↬⇒ě₂
            | ↬⇒□ e₃↬⇒ě₃ = refl
    ↬⇒□ (ISInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇒□ e₂↬⇒ě₂
            | ↬⇒□ e₃↬⇒ě₃ = refl

    ↬⇐□ : ∀ {Γ : UCtx} {e : UExp} {τ : Typ} {ě : ⟦ Γ ⟧ ⊢⇐ τ} → Γ ⊢ e ↬⇐ ě → ě ⇐□ ≡ e
    ↬⇐□ (IALam1 τ₁▸ τ~τ₁ e↬⇐ě)
      rewrite ↬⇐□ e↬⇐ě   = refl
    ↬⇐□ (IALam2 τ₁!▸ e↬⇐ě)
      rewrite ↬⇐□ e↬⇐ě   = refl
    ↬⇐□ (IALam3 τ₁▸ τ~̸τ₁ e↬⇐ě)
      rewrite ↬⇐□ e↬⇐ě   = refl
    ↬⇐□ (IALet e₁↬⇒ě₁ e₂↬⇐ě₂)
      rewrite ↬⇒□ e₁↬⇒ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇐□ (IAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇐□ e₂↬⇐ě₂
            | ↬⇐□ e₃↬⇐ě₃ = refl
    ↬⇐□ (IAInconsistentTypes e↬⇒ě τ~̸τ′ s)
      rewrite ↬⇒□ e↬⇒ě   = refl
    ↬⇐□ (IASubsume e↬⇒ě τ~τ′ s)
      rewrite ↬⇒□ e↬⇒ě   = refl

    -- well-typed unmarked expression are marked into marked expressions of the same type
    ⇒τ→↬⇒τ : ∀ {Γ : UCtx} {e : UExp} {τ : Typ}  → Γ ⊢ e ⇒ τ → Σ[ ě ∈ ⟦ Γ ⟧ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě
    ⇒τ→↬⇒τ {e = ‵⦇-⦈^ u} USHole            = ⟨ ⊢⦇-⦈^ u , ISHole ⟩
    ⇒τ→↬⇒τ {e = ‵ x} (USVar ∋x)            = ⟨ ⊢ ⟦ ∋x ⟧∋ [ x ] , ISVar ∋x ⟩
    ⇒τ→↬⇒τ {e = ‵λ x ∶ τ ∙ e} (USLam e⇒τ)
      with ⟨ ě  , e↬⇒ě   ⟩ ← ⇒τ→↬⇒τ e⇒τ    = ⟨ ⊢λ∶ τ ∙ ě [ x ] , ISLam e↬⇒ě ⟩
    ⇒τ→↬⇒τ {e = ‵ e₁ ∙ e₂} (USAp e₁⇒τ τ▸ e₂⇐τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₂  = ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸ ] , ISAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂ ⟩
    ⇒τ→↬⇒τ {e = ‵ x ← e₁ ∙ e₂} (USLet e₁⇒τ e₂⇒τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ
         | ⟨ ě₂ , e₂↬⇒ě₂ ⟩ ← ⇒τ→↬⇒τ e₂⇒τ₂  = ⟨ ⊢← ě₁ ∙ ě₂ [ x ] , ISLet e₁↬⇒ě₁ e₂↬⇒ě₂ ⟩
    ⇒τ→↬⇒τ {e = ‵ℕ n} USNum                = ⟨ ⊢ℕ n , ISNum ⟩
    ⇒τ→↬⇒τ {e = ‵ e₁ + e₂} (USPlus e₁⇐num e₂⇐num)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐num
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐num = ⟨ ⊢ ě₁ + ě₂ , ISPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩
    ⇒τ→↬⇒τ {e = ‵tt} USTrue                = ⟨ ⊢tt , ISTrue ⟩
    ⇒τ→↬⇒τ {e = ‵ff} USFalse               = ⟨ ⊢ff , ISFalse ⟩
    ⇒τ→↬⇒τ {e = ‵ e₁ ∙ e₂ ∙ e₃} (USIf e₁⇐bool e₂⇒τ₁ e₃⇒τ₂ τ₁⊔τ₂)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐bool
         | ⟨ ě₂ , e₂↬⇒ě₂ ⟩ ← ⇒τ→↬⇒τ e₂⇒τ₁
         | ⟨ ě₃ , e₃↬⇒ě₃ ⟩ ← ⇒τ→↬⇒τ e₃⇒τ₂  = ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] , ISIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂ ⟩

    ⇐τ→↬⇐τ : ∀ {Γ : UCtx} {e : UExp} {τ : Typ}  → Γ ⊢ e ⇐ τ → Σ[ ě ∈ ⟦ Γ ⟧ ⊢⇐ τ ] Γ ⊢ e ↬⇐ ě
    ⇐τ→↬⇐τ {e = ‵λ x ∶ τ ∙ e} (UALam τ₃▸ τ~τ₁ e⇐τ₂)
      with ⟨ ě , e↬⇐ě ⟩ ← ⇐τ→↬⇐τ e⇐τ₂     = ⟨ ⊢λ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ∙ x ] , IALam1 τ₃▸ τ~τ₁ e↬⇐ě ⟩
    ⇐τ→↬⇐τ {e = ‵ x ← e₁ ∙ e₂} (UALet e₁⇒τ e₂⇐τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₂ = ⟨ ⊢← ě₁ ∙ ě₂ [ x ] , IALet e₁↬⇒ě₁ e₂↬⇐ě₂ ⟩
    ⇐τ→↬⇐τ {e = ‵ e₁ ∙ e₂ ∙ e₃} (UAIf e₁⇐τ e₂⇐τ₁ e₃⇐τ₂)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐τ
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₁
         | ⟨ ě₃ , e₃↬⇐ě₃ ⟩ ← ⇐τ→↬⇐τ e₃⇐τ₂ = ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ , IAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃ ⟩
    ⇐τ→↬⇐τ {e = e} (UASubsume e⇒τ′ τ~τ′ su)
      with ⟨ ě , e↬⇒ě ⟩ ← ⇒τ→↬⇒τ e⇒τ′     = ⟨ ⊢∙ ě [ τ~τ′ ∙ USu→MSu su e↬⇒ě ] , IASubsume e↬⇒ě τ~τ′ su ⟩
