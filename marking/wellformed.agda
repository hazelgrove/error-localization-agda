open import prelude
open import core

open import marking.marking

module marking.wellformed where
  mutual
    -- marking preserves syntactic structure
    ↬⇒□ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇒ τ}
        → Γ ⊢ e ↬⇒ ě
        → ě ⇒□ ≡ e
    ↬⇒□ MKSHole          = refl
    ↬⇒□ (MKSVar ∋x)      = refl
    ↬⇒□ (MKSFree ∌x)     = refl
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
    ↬⇒□ MKSNum           = refl
    ↬⇒□ (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
      rewrite ↬⇐□ e₁↬⇐ě₁
            | ↬⇐□ e₂↬⇐ě₂ = refl
    ↬⇒□ MKSTrue          = refl
    ↬⇒□ MKSFalse         = refl
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
      rewrite ↬⇒□ e↬⇒ě   = refl
    ↬⇒□ (MKSProjL2 e↬⇒ě τ!▸)
      rewrite ↬⇒□ e↬⇒ě   = refl
    ↬⇒□ (MKSProjR1 e↬⇒ě τ▸)
      rewrite ↬⇒□ e↬⇒ě   = refl
    ↬⇒□ (MKSProjR2 e↬⇒ě τ!▸)
      rewrite ↬⇒□ e↬⇒ě   = refl

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

  mutual
    -- well-typed unmarked expression are marked into marked expressions of the same type
    ⇒τ→↬⇒τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ}
           → Γ ⊢ e ⇒ τ
           → Σ[ ě ∈ Γ ⊢⇒ τ ] Γ ⊢ e ↬⇒ ě
    ⇒τ→↬⇒τ {e = ‵⦇-⦈^ u}        USHole     = ⟨ ⊢⦇-⦈^ u , MKSHole ⟩
    ⇒τ→↬⇒τ {e = ‵ x}            (USVar ∋x) = ⟨ ⊢ ∋x , MKSVar ∋x ⟩
    ⇒τ→↬⇒τ {e = ‵λ x ∶ τ ∙ e}   (USLam e⇒τ)
      with ⟨ ě  , e↬⇒ě   ⟩ ← ⇒τ→↬⇒τ e⇒τ    = ⟨ ⊢λ x ∶ τ ∙ ě , MKSLam e↬⇒ě ⟩
    ⇒τ→↬⇒τ {e = ‵ e₁ ∙ e₂} (USAp e₁⇒τ τ▸ e₂⇐τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₂  = ⟨ ⊢ ě₁ ∙ ě₂ [ τ▸ ] , MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂ ⟩
    ⇒τ→↬⇒τ {e = ‵ x ← e₁ ∙ e₂}  (USLet e₁⇒τ e₂⇒τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ
         | ⟨ ě₂ , e₂↬⇒ě₂ ⟩ ← ⇒τ→↬⇒τ e₂⇒τ₂  = ⟨ ⊢ x ← ě₁ ∙ ě₂ , MKSLet e₁↬⇒ě₁ e₂↬⇒ě₂ ⟩
    ⇒τ→↬⇒τ {e = ‵ℕ n}           USNum      = ⟨ ⊢ℕ n , MKSNum ⟩
    ⇒τ→↬⇒τ {e = ‵ e₁ + e₂}      (USPlus e₁⇐num e₂⇐num)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐num
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐num = ⟨ ⊢ ě₁ + ě₂ , MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂ ⟩
    ⇒τ→↬⇒τ {e = ‵tt}            USTrue     = ⟨ ⊢tt , MKSTrue ⟩
    ⇒τ→↬⇒τ {e = ‵ff}            USFalse    = ⟨ ⊢ff , MKSFalse ⟩
    ⇒τ→↬⇒τ {e = ‵ e₁ ∙ e₂ ∙ e₃} (USIf e₁⇐bool e₂⇒τ₁ e₃⇒τ₂ τ₁⊔τ₂)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐bool
         | ⟨ ě₂ , e₂↬⇒ě₂ ⟩ ← ⇒τ→↬⇒τ e₂⇒τ₁
         | ⟨ ě₃ , e₃↬⇒ě₃ ⟩ ← ⇒τ→↬⇒τ e₃⇒τ₂  = ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ] , MKSIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂ ⟩
    ⇒τ→↬⇒τ {e = ‵⟨ e₁ , e₂ ⟩}   (USPair e₁⇒τ₁ e₂⇒τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ₁
         | ⟨ ě₂ , e₂↬⇒ě₂ ⟩ ← ⇒τ→↬⇒τ e₂⇒τ₂  = ⟨ ⊢⟨ ě₁ , ě₂ ⟩ , MKSPair e₁↬⇒ě₁ e₂↬⇒ě₂ ⟩
    ⇒τ→↬⇒τ {e = ‵π₁ e}          (USProjL e⇒τ τ▸)
      with ⟨ ě , e↬⇒ě ⟩ ← ⇒τ→↬⇒τ e⇒τ       = ⟨ ⊢π₁ ě [ τ▸ ] , MKSProjL1 e↬⇒ě τ▸ ⟩
    ⇒τ→↬⇒τ {e = ‵π₂ e}          (USProjR e⇒τ τ▸)
      with ⟨ ě , e↬⇒ě ⟩ ← ⇒τ→↬⇒τ e⇒τ       = ⟨ ⊢π₂ ě [ τ▸ ] , MKSProjR1 e↬⇒ě τ▸ ⟩

    ⇐τ→↬⇐τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ}
           → Γ ⊢ e ⇐ τ
           → Σ[ ě ∈ Γ ⊢⇐ τ ] Γ ⊢ e ↬⇐ ě
    ⇐τ→↬⇐τ {e = ‵λ x ∶ τ ∙ e}   (UALam τ₃▸ τ~τ₁ e⇐τ₂)
      with ⟨ ě , e↬⇐ě ⟩ ← ⇐τ→↬⇐τ e⇐τ₂     = ⟨ ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ] , MKALam1 τ₃▸ τ~τ₁ e↬⇐ě ⟩
    ⇐τ→↬⇐τ {e = ‵ x ← e₁ ∙ e₂}  (UALet e₁⇒τ e₂⇐τ₂)
      with ⟨ ě₁ , e₁↬⇒ě₁ ⟩ ← ⇒τ→↬⇒τ e₁⇒τ
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₂ = ⟨ ⊢ x ← ě₁ ∙ ě₂ , MKALet e₁↬⇒ě₁ e₂↬⇐ě₂ ⟩
    ⇐τ→↬⇐τ {e = ‵ e₁ ∙ e₂ ∙ e₃} (UAIf e₁⇐τ e₂⇐τ₁ e₃⇐τ₂)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐τ
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₁
         | ⟨ ě₃ , e₃↬⇐ě₃ ⟩ ← ⇐τ→↬⇐τ e₃⇐τ₂ = ⟨ ⊢ ě₁ ∙ ě₂ ∙ ě₃ , MKAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃ ⟩
    ⇐τ→↬⇐τ {e = ‵⟨ e₁ , e₂ ⟩}   (UAPair τ▸ e₁⇐τ₁ e₂⇐τ₂)
      with ⟨ ě₁ , e₁↬⇐ě₁ ⟩ ← ⇐τ→↬⇐τ e₁⇐τ₁
         | ⟨ ě₂ , e₂↬⇐ě₂ ⟩ ← ⇐τ→↬⇐τ e₂⇐τ₂ = ⟨ ⊢⟨ ě₁ , ě₂ ⟩[ τ▸ ] , MKAPair1 e₁↬⇐ě₁ e₂↬⇐ě₂ τ▸ ⟩
    ⇐τ→↬⇐τ {e = e}              (UASubsume e⇒τ′ τ~τ′ su)
      with ⟨ ě , e↬⇒ě ⟩ ← ⇒τ→↬⇒τ e⇒τ′     = ⟨ ⊢∙ ě [ τ~τ′ ∙ USu→MSu su e↬⇒ě ] , MKASubsume e↬⇒ě τ~τ′ su ⟩

  -- marking synthesizes the same type as synthesis
  ⇒-↬-≡ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {τ′ : Typ} {ě : Γ ⊢⇒ τ′}
         → Γ ⊢ e ⇒ τ
         → Γ ⊢ e ↬⇒ ě
         → τ ≡ τ′
  ⇒-↬-≡ USHole MKSHole
       = refl
  ⇒-↬-≡ (USVar ∋x) (MKSVar ∋x′)
       = ∋→τ-≡ ∋x ∋x′
  ⇒-↬-≡ (USVar {τ = τ} ∋x) (MKSFree ∌y)
       = ⊥-elim (∌y ⟨ τ , ∋x ⟩)
  ⇒-↬-≡ (USLam e⇒τ) (MKSLam e↬⇒ě)
    rewrite ⇒-↬-≡ e⇒τ e↬⇒ě
       = refl
  ⇒-↬-≡ (USAp e⇒τ τ▸ e₁⇐τ₁) (MKSAp1 e↬⇒ě τ▸′ e₂↬⇐ě₂)
    with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
    with refl ← ▸-→-unicity τ▸ τ▸′
       = refl
  ⇒-↬-≡ (USAp {τ₁ = τ₁} {τ₂ = τ₂} e⇒τ τ▸ e₁⇐τ₁) (MKSAp2 e↬⇒ě τ!▸ e₂↬⇐ě₂)
    with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
       = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ⇒-↬-≡ (USLet e₁⇒τ₁ e₂⇒τ₂) (MKSLet e₁↬⇒ě₁ e₂↬⇒ě₂)
    with refl ← ⇒-↬-≡ e₁⇒τ₁ e₁↬⇒ě₁
    with refl ← ⇒-↬-≡ e₂⇒τ₂ e₂↬⇒ě₂
       = refl
  ⇒-↬-≡ USNum MKSNum
       = refl
  ⇒-↬-≡ (USPlus e₁⇐num e₂⇐num) (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
       = refl
  ⇒-↬-≡ USTrue MKSTrue
       = refl
  ⇒-↬-≡ USFalse MKSFalse
       = refl
  ⇒-↬-≡ (USIf e₁⇐bool e₂⇒τ₁ e₃⇒τ₂ τ₁⊔τ₂) (MKSIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂′)
    with refl ← ⇒-↬-≡ e₂⇒τ₁ e₂↬⇒ě₂
    with refl ← ⇒-↬-≡ e₃⇒τ₂ e₃↬⇒ě₃
    with refl ← ⊔-unicity τ₁⊔τ₂ τ₁⊔τ₂′
       = refl
  ⇒-↬-≡ (USIf e₁⇐bool e₂⇒τ₁ e₃⇒τ₂ τ₁⊔τ₂) (MKSInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂)
    with refl ← ⇒-↬-≡ e₂⇒τ₁ e₂↬⇒ě₂
    with refl ← ⇒-↬-≡ e₃⇒τ₂ e₃↬⇒ě₃
       = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
  ⇒-↬-≡ (USPair e₁⇒τ₁ e₂⇒τ₂) (MKSPair e₁↬⇒ě₁ e₂↬⇒ě₂)
    with refl ← ⇒-↬-≡ e₁⇒τ₁ e₁↬⇒ě₁
    with refl ← ⇒-↬-≡ e₂⇒τ₂ e₂↬⇒ě₂
       = refl
  ⇒-↬-≡ (USProjL e⇒τ τ▸) (MKSProjL1 e↬⇒ě τ▸′)
    with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
    with refl ← ▸-×-unicity τ▸ τ▸′
       = refl
  ⇒-↬-≡ (USProjL {τ₁ = τ₁} {τ₂ = τ₂} e⇒τ τ▸) (MKSProjL2 e↬⇒ě τ!▸)
    with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
       = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
  ⇒-↬-≡ (USProjR e⇒τ τ▸) (MKSProjR1 e↬⇒ě τ▸′)
    with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
    with refl ← ▸-×-unicity τ▸ τ▸′
       = refl
  ⇒-↬-≡ (USProjR {τ₁ = τ₁} {τ₂ = τ₂} e⇒τ τ▸) (MKSProjR2 e↬⇒ě τ!▸)
    with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
       = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)

  mutual
    -- marking well-typed terms produces no marks
    ⇒τ→markless : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇒ τ}
                → Γ ⊢ e ⇒ τ
                → Γ ⊢ e ↬⇒ ě
                → Markless⇒ ě
    ⇒τ→markless USHole MKSHole
         = MLSHole
    ⇒τ→markless (USVar ∋x) (MKSVar ∋x′)
         = MLSVar
    ⇒τ→markless (USVar ∋x) (MKSFree ∌y)
         = ⊥-elim (∌y ⟨ unknown , ∋x ⟩)
    ⇒τ→markless (USLam e⇒τ) (MKSLam e↬⇒ě)
         = MLSLam (⇒τ→markless e⇒τ e↬⇒ě)
    ⇒τ→markless (USAp e₁⇒τ τ▸ e₂⇐τ₁) (MKSAp1 e₁↬⇒ě₁ τ▸′  e₂↬⇐ě₂)
      with refl ← ⇒-↬-≡ e₁⇒τ e₁↬⇒ě₁
      with refl ← ▸-→-unicity τ▸ τ▸′
         = MLSAp (⇒τ→markless e₁⇒τ e₁↬⇒ě₁) (⇐τ→markless e₂⇐τ₁ e₂↬⇐ě₂)
    ⇒τ→markless (USAp {τ₁ = τ₁} e₁⇒τ τ▸ e₂⇐τ₁) (MKSAp2 e₁↬⇒ě₁ τ!▸′ e₂↬⇐ě₂)
      with refl ← ⇒-↬-≡ e₁⇒τ e₁↬⇒ě₁
         = ⊥-elim (τ!▸′ ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)
    ⇒τ→markless (USLet e₁⇒τ₁ e₂⇒τ₂) (MKSLet e₁↬⇒ě₁ e₂↬⇒ě₂)
      with refl ← ⇒-↬-≡ e₁⇒τ₁ e₁↬⇒ě₁
      with refl ← ⇒-↬-≡ e₂⇒τ₂ e₂↬⇒ě₂
         = MLSLet (⇒τ→markless e₁⇒τ₁ e₁↬⇒ě₁) (⇒τ→markless e₂⇒τ₂ e₂↬⇒ě₂)
    ⇒τ→markless USNum MKSNum
         = MLSNum
    ⇒τ→markless (USPlus e₁⇐num e₂⇐num) (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂)
         = MLSPlus (⇐τ→markless e₁⇐num e₁↬⇐ě₁) (⇐τ→markless e₂⇐num e₂↬⇐ě₂)
    ⇒τ→markless USTrue MKSTrue
         = MLSTrue
    ⇒τ→markless USFalse MKSFalse
         = MLSFalse
    ⇒τ→markless (USIf e₁⇐bool e₂⇒τ₁ e₃⇒τ₂ τ₁⊔τ₂) (MKSIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₃)
      with refl ← ⇒-↬-≡ e₂⇒τ₁ e₂↬⇒ě₂
      with refl ← ⇒-↬-≡ e₃⇒τ₂ e₃↬⇒ě₃
         = MLSIf (⇐τ→markless e₁⇐bool e₁↬⇐ě₁) (⇒τ→markless e₂⇒τ₁ e₂↬⇒ě₂) (⇒τ→markless e₃⇒τ₂ e₃↬⇒ě₃)
    ⇒τ→markless (USIf e₁⇐bool e₂⇒τ₁ e₃⇒τ₂ τ₁⊔τ₂) (MKSInconsistentBranches e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁~̸τ₂)
      with refl ← ⇒-↬-≡ e₂⇒τ₁ e₂↬⇒ě₂
      with refl ← ⇒-↬-≡ e₃⇒τ₂ e₃↬⇒ě₃
         = ⊥-elim (τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂))
    ⇒τ→markless (USPair e₁⇒τ₁ e₂⇒τ₂) (MKSPair e₁↬⇒ě₁ e₂↬⇒ě₂)
         = MLSPair (⇒τ→markless e₁⇒τ₁ e₁↬⇒ě₁) (⇒τ→markless e₂⇒τ₂ e₂↬⇒ě₂)
    ⇒τ→markless (USProjL e⇒τ τ▸) (MKSProjL1 e↬⇒ě τ▸′)
      with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
         = MLSProjL (⇒τ→markless e⇒τ e↬⇒ě)
    ⇒τ→markless (USProjL {τ₂ = τ₂} e⇒τ τ▸) (MKSProjL2 e↬⇒ě τ!▸)
      with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
         = ⊥-elim (τ!▸ ⟨ unknown , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ⇒τ→markless (USProjR e⇒τ τ▸) (MKSProjR1 e↬⇒ě τ▸′)
      with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
         = MLSProjR (⇒τ→markless e⇒τ e↬⇒ě)
    ⇒τ→markless (USProjR {τ₁ = τ₁} e⇒τ τ▸) (MKSProjR2 e↬⇒ě τ!▸)
      with refl ← ⇒-↬-≡ e⇒τ e↬⇒ě
         = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ unknown , τ▸ ⟩ ⟩)

    ⇐τ→markless : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇐ τ}
                → Γ ⊢ e ⇐ τ
                → Γ ⊢ e ↬⇐ ě
                → Markless⇐ ě
    ⇐τ→markless (UALam τ₃▸ τ~τ₁ e⇐τ) (MKALam1 τ₃▸′ τ~τ₁′ e↬⇐ě)
      with refl ← ▸-→-unicity τ₃▸ τ₃▸′
         = MLALam (⇐τ→markless e⇐τ e↬⇐ě)
    ⇐τ→markless (UALam {τ₁ = τ₁} {τ₂ = τ₂} τ₃▸ τ~τ₁ e⇐τ) (MKALam2 τ₃!▸ e↬⇐ě)
         = ⊥-elim (τ₃!▸ ⟨ τ₁ , ⟨ τ₂ , τ₃▸ ⟩ ⟩)
    ⇐τ→markless (UALam τ₃▸ τ~τ₁ e⇐τ) (MKALam3 τ₃▸′ τ~̸τ₁ e↬⇐ě)
      with refl ← ▸-→-unicity τ₃▸ τ₃▸′
         = ⊥-elim (τ~̸τ₁ τ~τ₁)
    ⇐τ→markless (UALet e₁⇒τ₁ e₂⇐τ₂) (MKALet e₁↬⇒ě₁ e₂↬⇐ě₂)
      with refl ← ⇒-↬-≡ e₁⇒τ₁ e₁↬⇒ě₁
         = MLALet (⇒τ→markless e₁⇒τ₁ e₁↬⇒ě₁) (⇐τ→markless e₂⇐τ₂ e₂↬⇐ě₂)
    ⇐τ→markless (UAIf e₁⇐bool e₂⇐τ₁ e₃⇐τ₂) (MKAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃)
         = MLAIf (⇐τ→markless e₁⇐bool e₁↬⇐ě₁) (⇐τ→markless e₂⇐τ₁ e₂↬⇐ě₂) (⇐τ→markless e₃⇐τ₂ e₃↬⇐ě₃)
    ⇐τ→markless (UAPair τ▸ e₁⇐τ₁ e₂⇐τ₂) (MKAPair1 e₁↬⇐ě₁ e₂↬⇐ě₂ τ▸′)
      with refl ← ▸-×-unicity τ▸ τ▸′
         = MLAPair (⇐τ→markless e₁⇐τ₁ e₁↬⇐ě₁) (⇐τ→markless e₂⇐τ₂ e₂↬⇐ě₂)
    ⇐τ→markless (UAPair {τ₁ = τ₁} {τ₂ = τ₂} τ▸ e₁⇐τ₁ e₂⇐τ₂) (MKAPair2 e₁↬⇐ě₁ e₂↬⇐ě₂ τ!▸)
         = ⊥-elim (τ!▸ ⟨ τ₁ , ⟨ τ₂ , τ▸ ⟩ ⟩)
    ⇐τ→markless (UASubsume e⇒τ′ τ~τ′ su) (MKAInconsistentTypes e↬⇒ě τ~̸τ′ su′)
      with refl ← ⇒-↬-≡ e⇒τ′ e↬⇒ě
         = ⊥-elim (τ~̸τ′ τ~τ′)
    ⇐τ→markless (UASubsume e⇒τ′ τ~τ′ su) (MKASubsume e↬⇒ě τ~τ′′ su′)
      with refl ← ⇒-↬-≡ e⇒τ′ e↬⇒ě
         = MLASubsume (⇒τ→markless e⇒τ′ e↬⇒ě)

  mutual
    -- synthetically marking an expression into a markless expression and a type implies the original synthesizes that type
    ↬⇒τ-markless→⇒τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇒ τ}
                    → Γ ⊢ e ↬⇒ ě
                    → Markless⇒ ě
                    → Γ ⊢ e ⇒ τ
    ↬⇒τ-markless→⇒τ MKSHole less = USHole
    ↬⇒τ-markless→⇒τ (MKSVar ∋x) less = USVar ∋x
    ↬⇒τ-markless→⇒τ (MKSLam e↬⇒ě) (MLSLam less)
      with e⇒τ ← ↬⇒τ-markless→⇒τ e↬⇒ě less
         = USLam e⇒τ
    ↬⇒τ-markless→⇒τ (MKSAp1 e₁↬⇒ě₁ τ▸ e₂↬⇐ě₂) (MLSAp less₁ less₂)
      with e₁⇒τ  ← ↬⇒τ-markless→⇒τ e₁↬⇒ě₁ less₁
         | e₂⇐τ₁ ← ↬⇐τ-markless→⇐τ e₂↬⇐ě₂ less₂
         = USAp e₁⇒τ τ▸ e₂⇐τ₁
    ↬⇒τ-markless→⇒τ (MKSLet e₁↬⇒ě₁ e₂↬⇒ě₂) (MLSLet less₁ less₂)
      with e₁⇒τ₁ ← ↬⇒τ-markless→⇒τ e₁↬⇒ě₁ less₁
         | e₂⇒τ₂ ← ↬⇒τ-markless→⇒τ e₂↬⇒ě₂ less₂
         = USLet e₁⇒τ₁ e₂⇒τ₂
    ↬⇒τ-markless→⇒τ MKSNum MLSNum = USNum
    ↬⇒τ-markless→⇒τ (MKSPlus e₁↬⇐ě₁ e₂↬⇐ě₂) (MLSPlus less₁ less₂)
      with e₁⇐τ₁ ← ↬⇐τ-markless→⇐τ e₁↬⇐ě₁ less₁
         | e₂⇐τ₂ ← ↬⇐τ-markless→⇐τ e₂↬⇐ě₂ less₂
         = USPlus e₁⇐τ₁ e₂⇐τ₂
    ↬⇒τ-markless→⇒τ MKSTrue MLSTrue = USTrue
    ↬⇒τ-markless→⇒τ MKSFalse MLSFalse = USFalse
    ↬⇒τ-markless→⇒τ (MKSIf e₁↬⇐ě₁ e₂↬⇒ě₂ e₃↬⇒ě₃ τ₁⊔τ₂) (MLSIf less₁ less₂ less₃)
      with e₁⇐τ₁ ← ↬⇐τ-markless→⇐τ e₁↬⇐ě₁ less₁
         | e₂⇒τ₂ ← ↬⇒τ-markless→⇒τ e₂↬⇒ě₂ less₂
         | e₃⇒τ₃ ← ↬⇒τ-markless→⇒τ e₃↬⇒ě₃ less₃
         = USIf e₁⇐τ₁ e₂⇒τ₂ e₃⇒τ₃ τ₁⊔τ₂
    ↬⇒τ-markless→⇒τ (MKSPair e₁↬⇒ě₁ e₂↬⇒ě₂) (MLSPair less₁ less₂)
      with e₁⇒τ₁ ← ↬⇒τ-markless→⇒τ e₁↬⇒ě₁ less₁
         | e₂⇒τ₂ ← ↬⇒τ-markless→⇒τ e₂↬⇒ě₂ less₂
         = USPair e₁⇒τ₁ e₂⇒τ₂
    ↬⇒τ-markless→⇒τ (MKSProjL1 e↬⇒ě τ▸) (MLSProjL less)
      with e⇒τ ← ↬⇒τ-markless→⇒τ e↬⇒ě less
         = USProjL e⇒τ τ▸
    ↬⇒τ-markless→⇒τ (MKSProjR1 e↬⇒ě τ▸) (MLSProjR less)
      with e⇒τ ← ↬⇒τ-markless→⇒τ e↬⇒ě less
         = USProjR e⇒τ τ▸

    -- analytically marking an expression into a markless expression against a type implies the original analyzes against type
    ↬⇐τ-markless→⇐τ : ∀ {Γ : Ctx} {e : UExp} {τ : Typ} {ě : Γ ⊢⇐ τ}
                    → Γ ⊢ e ↬⇐ ě
                    → Markless⇐ ě
                    → Γ ⊢ e ⇐ τ
    ↬⇐τ-markless→⇐τ (MKALam1 τ₃▸ τ~τ₁ e↬⇐ě) (MLALam less)
      with e⇐τ₂ ← ↬⇐τ-markless→⇐τ e↬⇐ě less
         = UALam τ₃▸ τ~τ₁ e⇐τ₂
    ↬⇐τ-markless→⇐τ (MKALet e₁↬⇒ě₁ e₂↬⇐ě₂) (MLALet less₁ less₂)
      with e₁⇒τ₁ ← ↬⇒τ-markless→⇒τ e₁↬⇒ě₁ less₁
         | e₂⇐τ₂ ← ↬⇐τ-markless→⇐τ e₂↬⇐ě₂ less₂
         = UALet e₁⇒τ₁ e₂⇐τ₂
    ↬⇐τ-markless→⇐τ (MKAIf e₁↬⇐ě₁ e₂↬⇐ě₂ e₃↬⇐ě₃) (MLAIf less₁ less₂ less₃)
      with e₁⇐τ₁ ← ↬⇐τ-markless→⇐τ e₁↬⇐ě₁ less₁
         | e₂⇐τ₂ ← ↬⇐τ-markless→⇐τ e₂↬⇐ě₂ less₂
         | e₃⇐τ₃ ← ↬⇐τ-markless→⇐τ e₃↬⇐ě₃ less₃
         = UAIf e₁⇐τ₁ e₂⇐τ₂ e₃⇐τ₃
    ↬⇐τ-markless→⇐τ (MKAPair1 e₁↬⇐ě₁ e₂↬⇐ě₂ τ▸) (MLAPair less₁ less₂)
      with e₁⇐τ₁ ← ↬⇐τ-markless→⇐τ e₁↬⇐ě₁ less₁
         | e₂⇐τ₂ ← ↬⇐τ-markless→⇐τ e₂↬⇐ě₂ less₂
         = UAPair τ▸ e₁⇐τ₁ e₂⇐τ₂
    ↬⇐τ-markless→⇐τ (MKASubsume e↬⇒ě τ~τ′ su) (MLASubsume less)
      with e⇒τ ← ↬⇒τ-markless→⇒τ e↬⇒ě less
         = UASubsume e⇒τ τ~τ′ su

  mutual
    -- ill-typed expressions are marked into non-markless expressions
    ¬⇒τ→¬markless : ∀ {Γ : Ctx} {e : UExp} {τ′ : Typ} {ě : Γ ⊢⇒ τ′}
                  → ¬ (Σ[ τ ∈ Typ ] Γ ⊢ e ⇒ τ)
                  → Γ ⊢ e ↬⇒ ě
                  → ¬ (Markless⇒ ě)
    ¬⇒τ→¬markless {τ′ = τ′} ¬e⇒τ e↬⇒ě less = ¬e⇒τ ⟨ τ′ , ↬⇒τ-markless→⇒τ e↬⇒ě less ⟩

    ¬⇐τ→¬markless : ∀ {Γ : Ctx} {e : UExp} {τ′ : Typ} {ě : Γ ⊢⇐ τ′}
                  → ¬ (Σ[ τ ∈ Typ ] Γ ⊢ e ⇐ τ)
                  → Γ ⊢ e ↬⇐ ě
                  → ¬ (Markless⇐ ě)
    ¬⇐τ→¬markless {τ′ = τ′} ¬e⇐τ e↬⇐ě less = ¬e⇐τ ⟨ τ′ , ↬⇐τ-markless→⇐τ e↬⇐ě less ⟩
