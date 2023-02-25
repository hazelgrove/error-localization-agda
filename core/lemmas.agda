open import prelude

open import core.typ
open import core.ctx
open import core.uexp
open import core.mexp
open import core.erasure

module core.lemmas where
  -- synthesis totality
  ⊢⇐-⊢⇒ : ∀ {Γ τ} → (ě : Γ ⊢⇐ τ) → ∃[ τ′ ] Σ[ ě′ ∈ Γ ⊢⇒ τ′ ] ě ⇐□ ≡ ě′ ⇒□
  ⊢⇐-⊢⇒ ⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ]
    with ⟨ τ′ , ⟨ ě′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě rewrite eq
       = ⟨ τ -→ τ′ , ⟨ ⊢λ x ∶ τ ∙ ě′ , refl ⟩ ⟩
  ⊢⇐-⊢⇒ ⊢⸨λ x ∶ τ ∙ ě ⸩[ τ′!▸ ]
    with ⟨ τ′ , ⟨ ě′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě rewrite eq
       = ⟨ τ -→ τ′ , ⟨ ⊢λ x ∶ τ ∙ ě′ , refl ⟩ ⟩
  ⊢⇐-⊢⇒ ⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ]
    with ⟨ τ′ , ⟨ ě′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě rewrite eq
       = ⟨ τ -→ τ′ , ⟨ ⊢λ x ∶ τ ∙ ě′ , refl ⟩ ⟩
  ⊢⇐-⊢⇒ (⊢ x ← ě₁ ∙ ě₂)
    with ⟨ τ , ⟨ ě₂′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě₂ rewrite eq
       = ⟨ τ , ⟨ ⊢ x ← ě₁ ∙ ě₂′ , refl ⟩ ⟩
  ⊢⇐-⊢⇒ (⊢ ě₁ ∙ ě₂ ∙ ě₃)
    with ⟨ τ₁ , ⟨ ě₂′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě₂ rewrite eq
    with ⟨ τ₂ , ⟨ ě₃′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě₃ rewrite eq
    with τ₁ ⊔? τ₂
  ...  | yes ⟨ τ , τ₁⊔τ₂ ⟩ = ⟨ τ , ⟨ ⊢ ě₁ ∙ ě₂′ ∙ ě₃′ [ τ₁⊔τ₂ ] , refl ⟩ ⟩
  ...  | no ¬τ₁⊔τ₂         = ⟨ unknown , ⟨ ⊢⦉ ě₁ ∙ ě₂′ ∙ ě₃′ ⦊[ ¬⊔→~̸ ¬τ₁⊔τ₂ ] , refl ⟩ ⟩
  ⊢⇐-⊢⇒ (⊢⸨_⸩[_∙_] {τ′ = τ′} ě τ~̸τ′ su) = ⟨ τ′ , ⟨ ě , refl ⟩ ⟩
  ⊢⇐-⊢⇒ (⊢∙_[_∙_]  {τ′ = τ′} ě τ~τ′ su) = ⟨ τ′ , ⟨ ě , refl ⟩ ⟩

  -- analysis totality
  private
    ⊢⇒-⊢⇐-subsume : ∀ {Γ τ τ′} → (ě : Γ ⊢⇒ τ) → (su : MSubsumable ě) → Σ[ ě′ ∈ Γ ⊢⇐ τ′ ] ě ⇒□ ≡ ě′ ⇐□
    ⊢⇒-⊢⇐-subsume {τ = τ} {τ′ = τ′} ě su
      with τ′ ~? τ 
    ...  | yes τ′~τ = ⟨ ⊢∙ ě [ τ′~τ ∙ su ] , refl ⟩
    ...  | no  τ′~̸τ = ⟨ ⊢⸨ ě ⸩[ τ′~̸τ ∙ su ] , refl ⟩

  ⊢⇒-⊢⇐ : ∀ {Γ τ τ′} → (ě : Γ ⊢⇒ τ) → Σ[ ě′ ∈ Γ ⊢⇐ τ′ ] ě ⇒□ ≡ ě′ ⇐□
  ⊢⇒-⊢⇐ (⊢⦇-⦈^ u)                       = ⟨ ⊢∙ ⊢⦇-⦈^ u [ ~-unknown₂ ∙ MSuHole ] , refl ⟩
  ⊢⇒-⊢⇐ ě@(⊢ ∋x)                        = ⊢⇒-⊢⇐-subsume ě MSuVar
  ⊢⇒-⊢⇐ {τ′ = τ′} (⊢λ x ∶ τ ∙ ě)
    with τ′ ▸?
  ...  | no  τ′!▸
           with ⟨ ě′ , eq ⟩ ← ⊢⇒-⊢⇐ ě rewrite eq
              = ⟨ ⊢⸨λ x ∶ τ ∙ ě′ ⸩[ τ′!▸ ] , refl ⟩
  ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩
           with τ ~? τ₁
  ...         | yes τ~τ₁
                  with ⟨ ě′ , eq ⟩ ← ⊢⇒-⊢⇐ ě rewrite eq
                     = ⟨ ⊢λ x ∶ τ ∙ ě′ [ τ′▸ ∙ τ~τ₁ ] , refl ⟩
  ...         | no  τ~̸τ₁
                  with ⟨ ě′ , eq ⟩ ← ⊢⇒-⊢⇐ ě rewrite eq
                     = ⟨ ⊢λ x ∶⸨ τ ⸩∙ ě′ [ τ′▸ ∙ τ~̸τ₁ ] , refl ⟩
  ⊢⇒-⊢⇐ ě@(⊢ ě₁ ∙ ě₂ [ τ▸ ])                  = ⊢⇒-⊢⇐-subsume ě MSuAp1
  ⊢⇒-⊢⇐ ě@(⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ])               = ⊢⇒-⊢⇐-subsume ě MSuAp2
  ⊢⇒-⊢⇐ (⊢ x ← ě₁ ∙ ě₂)
    with ⟨ ě₂′ , eq ⟩ ← ⊢⇒-⊢⇐ ě₂ rewrite eq   = ⟨ ⊢ x ← ě₁ ∙ ě₂′ , refl ⟩
  ⊢⇒-⊢⇐ ě@(⊢ℕ n)                              = ⊢⇒-⊢⇐-subsume ě MSuNum
  ⊢⇒-⊢⇐ ě@(⊢ ě₁ + ě₂)                         = ⊢⇒-⊢⇐-subsume ě MSuPlus
  ⊢⇒-⊢⇐ ě@(⊢tt)                               = ⊢⇒-⊢⇐-subsume ě MSuTrue
  ⊢⇒-⊢⇐ ě@(⊢ff)                               = ⊢⇒-⊢⇐-subsume ě MSuFalse
  ⊢⇒-⊢⇐ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ]
    with ⟨ ě₂′ , eq₂ ⟩ ← ⊢⇒-⊢⇐ ě₂ rewrite eq₂
    with ⟨ ě₃′ , eq₃ ⟩ ← ⊢⇒-⊢⇐ ě₃ rewrite eq₃ = ⟨ ⊢ ě₁ ∙ ě₂′ ∙ ě₃′ , refl ⟩
  ⊢⇒-⊢⇐ ě@(⊢⟦ ∌y ⟧)                           = ⊢⇒-⊢⇐-subsume ě MSuUnbound
  ⊢⇒-⊢⇐ ě@(⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ])        = ⊢⇒-⊢⇐-subsume ě MSuInconsistentBranches
