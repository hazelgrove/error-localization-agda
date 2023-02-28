open import prelude
open import core

open import marking.marking

module marking.wellformed where
  mutual
    -- marking preserves syntactic structure
    ↬⇒□ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇒ τ}
        → Γ ⊢ e ↬⇒ ě
        → ě ⇒□ ≡ e
    ↬⇒□ MKSHole           = refl
    ↬⇒□ (MKSVar ∋x)       = refl
    ↬⇒□ (MKSUnbound ∌x)   = refl
    ↬⇒□ (MKSLam e↬⇒ě)
      rewrite ↬⇒□ e↬⇒ě   = refl
    ↬⇒□ (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂)
      rewrite ↬⇒□ e₁↬⇒ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇒□ (MKSAp2 e₁↬⇒ě₁ τ!▸ e₂↬⇐ě₂)
      rewrite ↬⇒□ e₁↬⇒ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇒□ (MKSLet e₁↬⇒ě₁ e₂↬⇒ě₂)
      rewrite ↬⇒□ e₁↬⇒ě₁
            | ↬⇒□ e₂↬⇒ě₂ = refl
    ↬⇒□ MKSNum            = refl
    ↬⇒□ (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇒□ MKSTrue           = refl
    ↬⇒□ MKSFalse          = refl
    ↬⇒□ (MKSIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇒□ e₂↬⇒ě₂
            | ↬⇒□ e₃↬⇒ě₃ = refl
    ↬⇒□ (MKSInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇒□ e₂↬⇒ě₂
            | ↬⇒□ e₃↬⇒ě₃ = refl
    ↬⇒□ (MKSPair e₁↬⇒ě₁ e₂↬⇒ě₂)
      rewrite ↬⇒□ e₁↬⇒ě₁
            | ↬⇒□ e₂↬⇒ě₂ = refl
    ↬⇒□ (MKSProjL1 e↬⇒ě τ▸)
      rewrite ↬⇒□ e↬⇒ě = refl
    ↬⇒□ (MKSProjL2 e↬⇒ě τ!▸)
      rewrite ↬⇒□ e↬⇒ě = refl
    ↬⇒□ (MKSProjR1 e↬⇒ě τ▸)
      rewrite ↬⇒□ e↬⇒ě = refl
    ↬⇒□ (MKSProjR2 e↬⇒ě τ!▸)
      rewrite ↬⇒□ e↬⇒ě = refl

    ↬⇐□ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇐ τ}
        → Γ ⊢ e ↬⇐ ě
        → ě ⇐□ ≡ e
    ↬⇐□ (MKALam1 τ₁▸ τ~τ₁ e↬⇐ě)
      rewrite ↬⇐□ e↬⇐ě   = refl
    ↬⇐□ (MKALam2 τ₁!▸ e↬⇐ě)
      rewrite ↬⇐□ e↬⇐ě   = refl
    ↬⇐□ (MKALam3 τ₁▸ τ~̸τ₁ e↬⇐ě)
      rewrite ↬⇐□ e↬⇐ě   = refl
    ↬⇐□ (MKALet e₁↬⇒ě₁ e₂↬⇐ě₂)
      rewrite ↬⇒□ e₁↬⇒ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇐□ (MKAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇐□ e₂↬⇐ě₂
            | ↬⇐□ e₃↬⇐ě₃ = refl
    ↬⇐□ (MKAPair1 e₁↬⇐ě₁ e₂↬⇐ě₂ τ▸)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇐□ (MKAPair2 e₁↬⇐ě₁ e₂↬⇐ě₂ τ!▸)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇐□ (MKAInconsistentTypes e↬⇒ě τ~̸τ′ s)
      rewrite ↬⇒□ e↬⇒ě   = refl
    ↬⇐□ (MKASubsume e↬⇒ě τ~τ′ s)
      rewrite ↬⇒□ e↬⇒ě   = refl

    -- well-typed unmarked expression are marked into marked expressions of the same type
    ⇒τ→↬⇒τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ}
           → Γ ⊢ e ⇒ τ
           → Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě
    ⇒τ→↬⇒τ {e = ‵⦇-⦈^ u} USHole            = ⟨ ⊢⦇-⦈^ u , MKSHole ⟩
    ⇒τ→↬⇒τ {e = ‵ x} (USVar ∋x)            = ⟨ ⊢ ∋x , MKSVar ∋x ⟩
    ⇒τ→↬⇒τ {e = ‵λ x ∶ τ ∙ e} (USLam e⇒τ)
      with ⟨ ě  , e↬⇒ě   ⟩ ← ⇒τ→↬⇒τ e⇒τ    = ⟨ ⊢λ x ∶ τ ∙ ě , MKSLam e↬⇒ě ⟩
    ⇒τ→↬⇒τ {e = ‵ e₁ ∙ e₂} (USAp e₁⇒τ τ▸ e₂⇐τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₂  = ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸ ] , MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂ ⟩
    ⇒τ→↬⇒τ {e = ‵ x ← e₁ ∙ e₂} (USLet e₁⇒τ e₂⇒τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ
         | ⟨ ě₂ , e₂↬⇒ě₂ ⟩ ← ⇒τ→↬⇒τ e₂⇒τ₂  = ⟨ ⊢ x ← ě₁ ∙ ě₂ , MKSLet e₁↬⇒ě₁ e₂↬⇒ě₂ ⟩
    ⇒τ→↬⇒τ {e = ‵ℕ n} USNum                = ⟨ ⊢ℕ n , MKSNum ⟩
    ⇒τ→↬⇒τ {e = ‵ e₁ + e₂} (USPlus e₁⇐num e₂⇐num)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐num
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐num = ⟨ ⊢ ě₁ + ě₂ , MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩
    ⇒τ→↬⇒τ {e = ‵tt} USTrue                = ⟨ ⊢tt , MKSTrue ⟩
    ⇒τ→↬⇒τ {e = ‵ff} USFalse               = ⟨ ⊢ff , MKSFalse ⟩
    ⇒τ→↬⇒τ {e = ‵ e₁ ∙ e₂ ∙ e₃} (USIf e₁⇐bool e₂⇒τ₁ e₃⇒τ₂ τ₁⊔τ₂)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐bool
         | ⟨ ě₂ , e₂↬⇒ě₂ ⟩ ← ⇒τ→↬⇒τ e₂⇒τ₁
         | ⟨ ě₃ , e₃↬⇒ě₃ ⟩ ← ⇒τ→↬⇒τ e₃⇒τ₂  = ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] , MKSIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂ ⟩
    ⇒τ→↬⇒τ {e = ‵⟨ e₁ , e₂ ⟩} (USPair e₁⇒τ₁ e₂⇒τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ₁
         | ⟨ ě₂ , e₂↬⇒ě₂ ⟩ ← ⇒τ→↬⇒τ e₂⇒τ₂  = ⟨ ⊢⟨ ě₁ , ě₂ ⟩ , MKSPair e₁↬⇒ě₁ e₂↬⇒ě₂ ⟩
    ⇒τ→↬⇒τ {e = ‵π₁ e} (USProjL e⇒τ τ▸)
      with ⟨ ě , e↬⇒ě ⟩ ← ⇒τ→↬⇒τ e⇒τ       = ⟨ ⊢π₁ ě [ τ▸ ] , MKSProjL1 e↬⇒ě τ▸ ⟩
    ⇒τ→↬⇒τ {e = ‵π₂ e} (USProjR e⇒τ τ▸)
      with ⟨ ě , e↬⇒ě ⟩ ← ⇒τ→↬⇒τ e⇒τ       = ⟨ ⊢π₂ ě [ τ▸ ] , MKSProjR1 e↬⇒ě τ▸ ⟩

    ⇐τ→↬⇐τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ}
           → Γ ⊢ e ⇐ τ
           → Σ[ ě ∈ Γ ⊢⇐ τ ] Γ ⊢ e ↬⇐ ě
    ⇐τ→↬⇐τ {e = ‵λ x ∶ τ ∙ e} (UALam τ₃▸ τ~τ₁ e⇐τ₂)
      with ⟨ ě , e↬⇐ě ⟩ ← ⇐τ→↬⇐τ e⇐τ₂     = ⟨ ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ] , MKALam1 τ₃▸ τ~τ₁ e↬⇐ě ⟩
    ⇐τ→↬⇐τ {e = ‵ x ← e₁ ∙ e₂} (UALet e₁⇒τ e₂⇐τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₂ = ⟨ ⊢ x ← ě₁ ∙ ě₂ , MKALet e₁↬⇒ě₁ e₂↬⇐ě₂ ⟩
    ⇐τ→↬⇐τ {e = ‵ e₁ ∙ e₂ ∙ e₃} (UAIf e₁⇐τ e₂⇐τ₁ e₃⇐τ₂)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐τ
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₁
         | ⟨ ě₃ , e₃↬⇐ě₃ ⟩ ← ⇐τ→↬⇐τ e₃⇐τ₂ = ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ , MKAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃ ⟩
    ⇐τ→↬⇐τ {e = ‵⟨ e₁ , e₂ ⟩} (UAPair τ▸ e₁⇐τ₁ e₂⇐τ₂)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐τ₁
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₂ = ⟨ ⊢⟨ ě₁ , ě₂ ⟩[ τ▸ ] , MKAPair1 e₁↬⇐ě₁ e₂↬⇐ě₂ τ▸ ⟩
    ⇐τ→↬⇐τ {e = e} (UASubsume e⇒τ′ τ~τ′ su)
      with ⟨ ě , e↬⇒ě ⟩ ← ⇒τ→↬⇒τ e⇒τ′     = ⟨ ⊢∙ ě [ τ~τ′ ∙ USu→MSu su e↬⇒ě ] , MKASubsume e↬⇒ě τ~τ′ su ⟩
