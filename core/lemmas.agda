open import prelude

open import core.typ
open import core.ctx
open import core.uexp
open import core.mexp
open import core.erasure

module core.lemmas where
  -- membership type equality
  ∋→τ-≡ : ∀ {Γ x τ₁ τ₂}
        → (Γ ∋ x ∶ τ₁)
        → (Γ ∋ x ∶ τ₂)
        → τ₁ ≡ τ₂
  ∋→τ-≡ Z         Z         = refl
  ∋→τ-≡ Z         (S x≢x _) = ⊥-elim (x≢x refl)
  ∋→τ-≡ (S x≢x _) Z         = ⊥-elim (x≢x refl)
  ∋→τ-≡ (S _ ∋x)  (S _ ∋x′) = ∋→τ-≡ ∋x ∋x′

  -- membership derivation equality
  ∋-≡ : ∀ {Γ x τ}
      → (∋x : Γ ∋ x ∶ τ)
      → (∋x′ : Γ ∋ x ∶ τ)
      → ∋x ≡ ∋x′
  ∋-≡ Z           Z         = refl
  ∋-≡ Z           (S x≢x _) = ⊥-elim (x≢x refl)
  ∋-≡ (S x≢x _)   Z         = ⊥-elim (x≢x refl)
  ∋-≡ (S x≢x′ ∋x) (S x≢x′′ ∋x′)
    rewrite ¬-≡ x≢x′ x≢x′′
          | ∋-≡ ∋x ∋x′ = refl

  -- non-membership derivation equality
  ∌-≡ : ∀ {Γ y}
      → (∌y : Γ ∌ y)
      → (∌y′ : Γ ∌ y)
      → ∌y ≡ ∌y′
  ∌-≡ ∌y ∌y′ = assimilation ∌y ∌y′

  -- unmarked synthesis unicity
  ⇒-unicity : ∀ {Γ : Ctx} {e : UExp} {τ₁ τ₂ : Typ}
            → Γ ⊢ e ⇒ τ₁
            → Γ ⊢ e ⇒ τ₂
            → τ₁ ≡ τ₂
  ⇒-unicity USHole                 USHole                   = refl
  ⇒-unicity (USVar ∋x)             (USVar ∋x′)              = ∋→τ-≡ ∋x ∋x′
  ⇒-unicity (USLam e⇒τ₁)           (USLam e⇒τ₂)
    rewrite ⇒-unicity e⇒τ₁ e⇒τ₂                             = refl
  ⇒-unicity (USAp e₁⇒τ₁ τ▸ e₂⇐τ₂)  (USAp e₁⇒τ₁′ τ▸′ e₂⇐τ₂′)
    rewrite ⇒-unicity e₁⇒τ₁ e₁⇒τ₁′
    with refl ← ▸-→-unicity τ▸ τ▸′                          = refl
  ⇒-unicity (USLet e₁⇒τ₁ e₂⇒τ₂)    (USLet e₁⇒τ₁′ e₂⇒τ₂′)
    rewrite ⇒-unicity e₁⇒τ₁ e₁⇒τ₁′
    rewrite ⇒-unicity e₂⇒τ₂ e₂⇒τ₂′                          = refl
  ⇒-unicity USNum                  USNum                    = refl
  ⇒-unicity (USPlus e₁⇐num e₂⇐num) (USPlus e₁⇐num′ e₂⇐num′) = refl
  ⇒-unicity USTrue                 USTrue                   = refl
  ⇒-unicity USFalse                USFalse                  = refl
  ⇒-unicity (USIf e₁⇐bool e₂⇒τ₁ e₃⇒τ₂ τ₁⊔τ₂) (USIf e₁⇐bool′ e₂⇒τ₁′ e₃⇒τ₂′ τ₁⊔τ₂′)
    rewrite ⇒-unicity e₂⇒τ₁ e₂⇒τ₁′
          | ⇒-unicity e₃⇒τ₂ e₃⇒τ₂′
          | ⊔-unicity τ₁⊔τ₂ τ₁⊔τ₂′                          = refl
  ⇒-unicity (USPair e₁⇒τ₁ e₂⇒τ₂)   (USPair e₁⇒τ₁′ e₂⇒τ₂′)
    rewrite ⇒-unicity e₁⇒τ₁ e₁⇒τ₁′
          | ⇒-unicity e₂⇒τ₂ e₂⇒τ₂′                          = refl
  ⇒-unicity (USProjL e⇒τ τ▸)       (USProjL e⇒τ′ τ▸′)
    rewrite ⇒-unicity e⇒τ e⇒τ′
    with refl ← ▸-×-unicity τ▸ τ▸′                          = refl
  ⇒-unicity (USProjR e⇒τ τ▸)       (USProjR e⇒τ′ τ▸′)
    rewrite ⇒-unicity e⇒τ e⇒τ′
    with refl ← ▸-×-unicity τ▸ τ▸′                          = refl

  -- an expression that synthesizes a type may be analyzed against a consistent type
  -- note that this NOT true with a lub (where the unknown type is the top of the imprecision partial order) definition
  ⇒-~-⇐ : ∀ {Γ : Ctx} {e : UExp} {τ τ′ : Typ} → Γ ⊢ e ⇒ τ → τ′ ~ τ → Γ ⊢ e ⇐ τ′
  ⇒-~-⇐ USHole τ′~τ = UASubsume USHole ~-unknown₂ USuHole
  ⇒-~-⇐ (USVar ∋x) τ′~τ = UASubsume (USVar ∋x) τ′~τ USuVar
  ⇒-~-⇐ (USLam e⇒τ₂) τ′~τ
    with ⟨ τ₁′ , ⟨ τ₂′ , τ′▸ ⟩ ⟩ ← ~→▸-→ τ′~τ
    with TCArr τ₁″~τ₁′ τ₂″~τ₂′ ← ~-▸-→→~ τ′~τ τ′▸
    with e⇐τ₂′ ← ⇒-~-⇐ e⇒τ₂ (~-sym τ₂″~τ₂′)
       = UALam τ′▸ τ₁″~τ₁′ e⇐τ₂′
  ⇒-~-⇐ (USAp e₁⇒τ τ▸ e₂⇐τ₁) τ′~τ₂ = UASubsume (USAp e₁⇒τ τ▸ e₂⇐τ₁) τ′~τ₂ USuAp
  ⇒-~-⇐ (USLet e₁⇒τ₁ e₂⇒τ₂) τ′~τ₂ = UALet e₁⇒τ₁ (⇒-~-⇐ e₂⇒τ₂ τ′~τ₂)
  ⇒-~-⇐ USNum τ′~num = UASubsume USNum τ′~num USuNum
  ⇒-~-⇐ (USPlus e₁⇐num e₂⇐num) τ′~num = UASubsume (USPlus e₁⇐num e₂⇐num) τ′~num USuPlus
  ⇒-~-⇐ USTrue τ′~bool = UASubsume USTrue τ′~bool USuTrue
  ⇒-~-⇐ USFalse τ′~bool = UASubsume USFalse τ′~bool USuFalse
  ⇒-~-⇐ (USIf e₁⇐bool e₂⇒τ₁ e₃⇒τ₂ τ₁⊔τ₂) τ′~τ
    with ⟨ τ₁~τ′ , τ₂~τ′ ⟩ ← ⊔⇒-~→~ τ₁⊔τ₂ (~-sym τ′~τ)
    with e₂⇐τ₁′ ← ⇒-~-⇐ e₂⇒τ₁ (~-sym τ₁~τ′)
       | e₃⇐τ₂′ ← ⇒-~-⇐ e₃⇒τ₂ (~-sym τ₂~τ′)
       = UAIf e₁⇐bool e₂⇐τ₁′ e₃⇐τ₂′
  ⇒-~-⇐ (USPair e₁⇒τ₁ e₂⇒τ₂) τ′~τ
    with ⟨ τ₁′ , ⟨ τ₂′ , τ′▸ ⟩ ⟩ ← ~→▸-× τ′~τ
    with TCProd τ₁~τ₁′ τ₂~τ₂′ ← ~-▸-×→~ τ′~τ τ′▸
    with e₁⇐τ₁′ ← ⇒-~-⇐ e₁⇒τ₁ (~-sym τ₁~τ₁′)
       | e₂⇐τ₂′ ← ⇒-~-⇐ e₂⇒τ₂ (~-sym τ₂~τ₂′)
       = UAPair τ′▸ e₁⇐τ₁′ e₂⇐τ₂′
  ⇒-~-⇐ (USProjL e⇒τ τ▸) τ′~τ = UASubsume (USProjL e⇒τ τ▸) τ′~τ USuProjL
  ⇒-~-⇐ (USProjR e⇒τ τ▸) τ′~τ = UASubsume (USProjR e⇒τ τ▸) τ′~τ USuProjR

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
  ⊢⇐-⊢⇒ ⊢⟨ ě₁ , ě₂ ⟩[ τ▸ ]
    with ⟨ τ₁ , ⟨ ě₁′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě₁ rewrite eq
    with ⟨ τ₂ , ⟨ ě₂′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě₂ rewrite eq
       = ⟨ τ₁ -× τ₂ , ⟨ ⊢⟨ ě₁′ , ě₂′ ⟩ , refl ⟩ ⟩
  ⊢⇐-⊢⇒ ⊢⸨⟨ ě₁ , ě₂ ⟩⸩[ τ!▸ ]
    with ⟨ τ₁ , ⟨ ě₁′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě₁ rewrite eq
    with ⟨ τ₂ , ⟨ ě₂′ , eq ⟩ ⟩ ← ⊢⇐-⊢⇒ ě₂ rewrite eq
       = ⟨ τ₁ -× τ₂ , ⟨ ⊢⟨ ě₁′ , ě₂′ ⟩ , refl ⟩ ⟩
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
    with τ′ ▸-→?
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
    with ⟨ ě₂′ , eq ⟩ ← ⊢⇒-⊢⇐ ě₂ rewrite eq
    with ⟨ ě₃′ , eq ⟩ ← ⊢⇒-⊢⇐ ě₃ rewrite eq = ⟨ ⊢ ě₁ ∙ ě₂′ ∙ ě₃′ , refl ⟩
  ⊢⇒-⊢⇐ {τ′ = τ′} ⊢⟨ ě₁ , ě₂ ⟩
    with τ′ ▸-×?
  ...  | yes ⟨ τ₁ , ⟨ τ₂ , τ′▸ ⟩ ⟩
           with ⟨ ě₁′ , eq ⟩ ← ⊢⇒-⊢⇐ ě₁ rewrite eq
           with ⟨ ě₂′ , eq ⟩ ← ⊢⇒-⊢⇐ ě₂ rewrite eq
              = ⟨ ⊢⟨ ě₁′ , ě₂′ ⟩[ τ′▸ ] , refl ⟩
  ...  | no  τ′!▸
           with ⟨ ě₁′ , eq ⟩ ← ⊢⇒-⊢⇐ ě₁ rewrite eq
           with ⟨ ě₂′ , eq ⟩ ← ⊢⇒-⊢⇐ ě₂ rewrite eq
              = ⟨ ⊢⸨⟨ ě₁′ , ě₂′ ⟩⸩[ τ′!▸ ] , refl ⟩
  ⊢⇒-⊢⇐ ě@(⊢π₁ _ [ τ▸ ]) = ⊢⇒-⊢⇐-subsume ě MSuProjL1
  ⊢⇒-⊢⇐ ě@(⊢π₁⸨ _ ⸩[ τ!▸ ]) = ⊢⇒-⊢⇐-subsume ě MSuProjL2
  ⊢⇒-⊢⇐ ě@(⊢π₂ _ [ τ▸ ]) = ⊢⇒-⊢⇐-subsume ě MSuProjR1
  ⊢⇒-⊢⇐ ě@(⊢π₂⸨ _ ⸩[ τ!▸ ]) = ⊢⇒-⊢⇐-subsume ě MSuProjR2
  ⊢⇒-⊢⇐ ě@(⊢⟦ ∌y ⟧)                           = ⊢⇒-⊢⇐-subsume ě MSuFree
  ⊢⇒-⊢⇐ ě@(⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ])        = ⊢⇒-⊢⇐-subsume ě MSuInconsistentBranches
