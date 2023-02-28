open import prelude
open import core

module marking.marking where
  infix 4 _⊢_↬⇒_
  infix 4 _⊢_↬⇐_

  -- mark insertion
  mutual
    -- synthesis
    data _⊢_↬⇒_ : {τ : Typ} (Γ : Ctx) → (e : UExp) → (Γ ⊢⇒ τ) → Set where
      ISHole : ∀ {Γ u}
        → Γ ⊢ ‵⦇-⦈^ u ↬⇒ ⊢⦇-⦈^ u

      ISVar : ∀ {Γ x τ}
        → (∋x : Γ ∋ x ∶ τ)
        → Γ ⊢ ‵ x ↬⇒ ⊢ ∋x

      ISUnbound : ∀ {Γ y}
        → (∌y : Γ ∌ y)
        → Γ ⊢ ‵ y ↬⇒ ⊢⟦ ∌y ⟧

      ISLam : ∀ {Γ x τ e τ₁}
        → {ě : Γ , x ∶ τ ⊢⇒ τ₁}
        → (e↬⇒ě : Γ , x ∶ τ ⊢ e ↬⇒ ě)
        → Γ ⊢ ‵λ x ∶ τ ∙ e ↬⇒ ⊢λ x ∶ τ ∙ ě

      ISAp1 : ∀ {Γ e₁ e₂ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ τ₁}
        → (e₁↬⇒ě₁ : Γ ⊢ e₁ ↬⇒ ě₁)
        → (τ▸ : τ ▸ τ₁ -→ τ₂)
        → (e₂↬⇐ě₂ : Γ ⊢ e₂ ↬⇐ ě₂)
        → Γ ⊢ ‵ e₁ ∙ e₂ ↬⇒ ⊢ ě₁ ∙ ě₂ [ τ▸ ]

      ISAp2 : ∀ {Γ e₁ e₂ τ}
        → {ě₁ : Γ ⊢⇒ τ}
        → {ě₂ : Γ ⊢⇐ unknown}
        → (e₁↬⇒ě₁ : Γ ⊢ e₁ ↬⇒ ě₁)
        → (τ!▸ : τ !▸-→)
        → (e₂↬⇐ě₂ : Γ ⊢ e₂ ↬⇐ ě₂)
        → Γ ⊢ ‵ e₁ ∙ e₂ ↬⇒ ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]

      ISLet : ∀ {Γ x e₁ e₂ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇒ τ₂}
        → (e₁↬⇒ě₁ : Γ ⊢ e₁ ↬⇒ ě₁)
        → (e₂↬⇒ě₂ : Γ , x ∶ τ₁ ⊢ e₂ ↬⇒ ě₂)
        → Γ ⊢ ‵ x ← e₁ ∙ e₂ ↬⇒ ⊢ x ← ě₁ ∙ ě₂

      ISNum : ∀ {Γ n}
        → Γ ⊢ ‵ℕ n ↬⇒ ⊢ℕ n

      ISPlus : ∀ {Γ e₁ e₂}
        → {ě₁ : Γ ⊢⇐ num}
        → {ě₂ : Γ ⊢⇐ num}
        → (e₁↬⇐ě₁ : Γ ⊢ e₁ ↬⇐ ě₁)
        → (e₂↬⇐ě₂ : Γ ⊢ e₂ ↬⇐ ě₂)
        → Γ ⊢ ‵ e₁ + e₂ ↬⇒ ⊢ ě₁ + ě₂

      ISTrue : ∀ {Γ}
        → Γ ⊢ ‵tt ↬⇒ ⊢tt

      ISFalse : ∀ {Γ}
        → Γ ⊢ ‵ff ↬⇒ ⊢ff

      ISIf : ∀ {Γ e₁ e₂ e₃ τ₁ τ₂ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁} 
        → {ě₃ : Γ ⊢⇒ τ₂} 
        → (e₁↬⇐ě₁ : Γ ⊢ e₁ ↬⇐ ě₁)
        → (e₂↬⇐ě₂ : Γ ⊢ e₂ ↬⇒ ě₂)
        → (e₃↬⇐ě₃ : Γ ⊢ e₃ ↬⇒ ě₃)
        → (τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ)
        → Γ ⊢ ‵ e₁ ∙ e₂ ∙ e₃ ↬⇒ ⊢ ě₁ ∙ ě₂ ∙ ě₃ [ τ₁⊔τ₂ ]

      ISInconsistentBranches : ∀ {Γ e₁ e₂ e₃ τ₁  τ₂}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇒ τ₁} 
        → {ě₃ : Γ ⊢⇒ τ₂} 
        → (e₁↬⇐ě₁ : Γ ⊢ e₁ ↬⇐ ě₁)
        → (e₂↬⇐ě₂ : Γ ⊢ e₂ ↬⇒ ě₂)
        → (e₃↬⇐ě₃ : Γ ⊢ e₃ ↬⇒ ě₃)
        → (τ₁~̸τ₂ : τ₁ ~̸ τ₂)
        → Γ ⊢ ‵ e₁ ∙ e₂ ∙ e₃ ↬⇒ ⊢⦉ ě₁ ∙ ě₂ ∙ ě₃ ⦊[ τ₁~̸τ₂ ]

      ISPair : ∀ {Γ e₁ e₂ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ ⊢⇒ τ₂}
        → (e₁↬⇒ě₁ : Γ ⊢ e₁ ↬⇒ ě₁)
        → (e₂↬⇒ě₂ : Γ ⊢ e₂ ↬⇒ ě₂)
        → Γ ⊢ ‵⟨ e₁ , e₂ ⟩ ↬⇒ ⊢⟨ ě₁ , ě₂ ⟩

      ISProjL1 : ∀ {Γ e τ τ₁ τ₂}
        → {ě : Γ ⊢⇒ τ}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ▸ : τ ▸ τ₁ -× τ₂)
        → Γ ⊢ ‵π₁ e ↬⇒ ⊢π₁ ě [ τ▸ ]

      ISProjL2 : ∀ {Γ e τ}
        → {ě : Γ ⊢⇒ τ}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ!▸ : τ !▸-×)
        → Γ ⊢ ‵π₁ e ↬⇒ ⊢π₁⸨ ě ⸩[ τ!▸ ]

      ISProjR1 : ∀ {Γ e τ τ₁ τ₂}
        → {ě : Γ ⊢⇒ τ}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ▸ : τ ▸ τ₁ -× τ₂)
        → Γ ⊢ ‵π₂ e ↬⇒ ⊢π₂ ě [ τ▸ ]

      ISProjR2 : ∀ {Γ e τ}
        → {ě : Γ ⊢⇒ τ}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ!▸ : τ !▸-×)
        → Γ ⊢ ‵π₂ e ↬⇒ ⊢π₂⸨ ě ⸩[ τ!▸ ]

    USu→MSu : ∀ {e : UExp} {Γ : Ctx} {τ : Typ} {ě : Γ ⊢⇒ τ} → USubsumable e → Γ ⊢ e ↬⇒ ě → MSubsumable ě
    USu→MSu {ě = ⊢⦇-⦈^ u}             USuHole  _ = MSuHole
    USu→MSu {ě = ⊢_ {x = x} ∋x}       USuVar   _ = MSuVar
    USu→MSu {ě = ⊢⟦ x ⟧}              USuVar   _ = MSuUnbound
    USu→MSu {ě = ⊢ ě₁ ∙ ě₂ [ τ▸ ]}    USuAp    _ = MSuAp1
    USu→MSu {ě = ⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]} USuAp    _ = MSuAp2
    USu→MSu {ě = ⊢ℕ n}                USuNum   _ = MSuNum
    USu→MSu {ě = ⊢ ě₁ + ě₂}           USuPlus  _ = MSuPlus
    USu→MSu {ě = ⊢tt}                 USuTrue  _ = MSuTrue
    USu→MSu {ě = ⊢ff}                 USuFalse _ = MSuFalse
    USu→MSu {ě = ⊢π₁ ě [ τ▸ ]}        USuProjL _ = MSuProjL1
    USu→MSu {ě = ⊢π₁⸨ ě ⸩[ τ!▸ ]}     USuProjL _ = MSuProjL2
    USu→MSu {ě = ⊢π₁ ě [ τ▸ ]}        USuProjR _ = MSuProjL1
    USu→MSu {ě = ⊢π₁⸨ ě ⸩[ τ!▸ ]}     USuProjR _ = MSuProjL2
    USu→MSu {ě = ⊢π₂ ě [ τ▸ ]}        USuProjR _ = MSuProjR1
    USu→MSu {ě = ⊢π₂⸨ ě ⸩[ τ!▸ ]}     USuProjR _ = MSuProjR2

    -- analysis
    data _⊢_↬⇐_ : {τ : Typ} (Γ : Ctx) → (e : UExp) → (Γ ⊢⇐ τ) → Set where
      IALam1 : ∀ {Γ x τ e τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~τ₁ : τ ~ τ₁)
        → Γ , x ∶ τ ⊢ e ↬⇐ ě
        → Γ ⊢ (‵λ x ∶ τ ∙ e) ↬⇐ (⊢λ x ∶ τ ∙ ě [ τ₃▸ ∙ τ~τ₁ ])

      IALam2 : ∀ {Γ x τ e τ′}
        → {ě : Γ , x ∶ τ ⊢⇐ unknown}
        → (τ′!▸ : τ′ !▸-→)
        → Γ , x ∶ τ ⊢ e ↬⇐ ě
        → Γ ⊢ (‵λ x ∶ τ ∙ e) ↬⇐ (⊢⸨λ x ∶ τ ∙ ě ⸩[ τ′!▸ ])

      IALam3 : ∀ {Γ x τ e τ₁ τ₂ τ₃}
        → {ě : Γ , x ∶ τ ⊢⇐ τ₂}
        → (τ₃▸ : τ₃ ▸ τ₁ -→ τ₂)
        → (τ~̸τ₁ : τ ~̸ τ₁)
        → Γ , x ∶ τ ⊢ e ↬⇐ ě
        → Γ ⊢ (‵λ x ∶ τ ∙ e) ↬⇐ (⊢λ x ∶⸨ τ ⸩∙ ě [ τ₃▸ ∙ τ~̸τ₁ ])

      IALet : ∀ {Γ x e₁ e₂ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇒ τ₁}
        → {ě₂ : Γ , x ∶ τ₁ ⊢⇐ τ₂}
        → (e₁↬⇒ě₁ : Γ ⊢ e₁ ↬⇒ ě₁)
        → (e₂↬⇐ě₂ : Γ , x ∶ τ₁ ⊢ e₂ ↬⇐ ě₂)
        → Γ ⊢ ‵ x ← e₁ ∙ e₂ ↬⇐ ⊢ x ← ě₁ ∙ ě₂ 

      IAIf : ∀ {Γ e₁ e₂ e₃ τ}
        → {ě₁ : Γ ⊢⇐ bool}
        → {ě₂ : Γ ⊢⇐ τ} 
        → {ě₃ : Γ ⊢⇐ τ} 
        → Γ ⊢ e₁ ↬⇐ ě₁
        → Γ ⊢ e₂ ↬⇐ ě₂
        → Γ ⊢ e₃ ↬⇐ ě₃
        → Γ ⊢ ‵ e₁ ∙ e₂ ∙ e₃ ↬⇐ ⊢ ě₁ ∙ ě₂ ∙ ě₃

      IAPair1 : ∀ {Γ e₁ e₂ τ τ₁ τ₂}
        → {ě₁ : Γ ⊢⇐ τ₁}
        → {ě₂ : Γ ⊢⇐ τ₂}
        → (e₁↬⇐ě₁ : Γ ⊢ e₁ ↬⇐ ě₁)
        → (e₂↬⇐ě₂ : Γ ⊢ e₂ ↬⇐ ě₂)
        → (τ▸ : τ ▸ τ₁ -× τ₂)
        → Γ ⊢ ‵⟨ e₁ , e₂ ⟩ ↬⇐ ⊢⟨ ě₁ , ě₂ ⟩[ τ▸ ]

      IAPair2 : ∀ {Γ e₁ e₂ τ}
        → {ě₁ : Γ ⊢⇐ unknown} 
        → {ě₂ : Γ ⊢⇐ unknown}
        → (e₁↬⇐ě₁ : Γ ⊢ e₁ ↬⇐ ě₁)
        → (e₂↬⇐ě₂ : Γ ⊢ e₂ ↬⇐ ě₂)
        → (τ!▸ : τ !▸-×)
        → Γ ⊢ ‵⟨ e₁ , e₂ ⟩ ↬⇐ ⊢⸨⟨ ě₁ , ě₂ ⟩⸩[ τ!▸ ]

      IAInconsistentTypes : ∀ {Γ e τ τ′}
        → {ě : Γ ⊢⇒ τ′}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ~̸τ′ : τ ~̸ τ′)
        → (s : USubsumable e)
        → Γ ⊢ e ↬⇐ ⊢⸨ ě ⸩[ τ~̸τ′ ∙ USu→MSu s e↬⇒ě ]

      IASubsume : ∀ {Γ e τ τ′}
        → {ě : Γ ⊢⇒ τ′}
        → (e↬⇒ě : Γ ⊢ e ↬⇒ ě)
        → (τ~τ′ : τ ~ τ′)
        → (s : USubsumable e)
        → Γ ⊢ e ↬⇐ ⊢∙ ě [ τ~τ′ ∙ USu→MSu s e↬⇒ě ]
