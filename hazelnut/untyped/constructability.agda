open import prelude
open import core

open import hazelnut.action
open import hazelnut.untyped.zexp
open import hazelnut.untyped.action
open import hazelnut.untyped.erasure

module hazelnut.untyped.constructability where
  -- constructability of types
  constructability-τ : (τ : Typ) → ∃[ ᾱ ] ▹ unknown ◃ + ᾱ +τ>* ▹ τ ◃
  constructability-τ num     = ⟨ ∣[ construct tnum ]  , ATITyp ATConNum ATIRefl  ⟩
  constructability-τ bool    = ⟨ ∣[ construct tbool ] , ATITyp ATConBool ATIRefl ⟩
  constructability-τ unknown = ⟨ []                   , ATIRefl                  ⟩
  constructability-τ (τ₁ -→ τ₂)
    with ⟨ ᾱ₁ , +>*τ₁ ⟩ ← constructability-τ τ₁
       | ⟨ ᾱ₂ , +>*τ₂ ⟩ ← constructability-τ τ₂
       = ⟨ ᾱ₁ ++ construct tarrow₁ ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +τ>*-++ +>*τ₁ (ATITyp ATConArrow1 (+τ>*-++ (ziplem-tarr2 +>*τ₂) (ATITyp ATMArrParent2 ATIRefl))) ⟩
  constructability-τ (τ₁ -× τ₂)
    with ⟨ ᾱ₁ , +>*τ₁ ⟩ ← constructability-τ τ₁
       | ⟨ ᾱ₂ , +>*τ₂ ⟩ ← constructability-τ τ₂
       = ⟨ ᾱ₁ ++ construct tprod₁ ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +τ>*-++ +>*τ₁ (ATITyp ATConProd1 (+τ>*-++ (ziplem-tprod2 +>*τ₂) (ATITyp ATMProdParent2 ATIRefl))) ⟩

  uz : Hole
  uz = 0

  -- constructability of expressions
  constructability-e : ∀ {u} → (e : UExp) → ∃[ ᾱ ] ‵▹ ‵⦇-⦈^ u ◃ + ᾱ +e>* ‵▹ e ◃
  constructability-e (‵⦇-⦈^ u) = ⟨ ∣[ del _ ]             , AEIExp AEDel AEIRefl    ⟩
  constructability-e (‵ x)     = ⟨ ∣[ construct (var x) ] , AEIExp AEConVar AEIRefl ⟩
  constructability-e (‵λ x ∶ τ ∙ e)
    with ⟨ ᾱ₁ , +>*e ⟩ ← constructability-e e
       | ⟨ ᾱ₂ , +>*τ ⟩ ← constructability-τ τ
       = ⟨ ᾱ₁ ++ construct (lam x) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e
             (AEIExp AEConLam
               (+e>*-++ (ziplem-lam1 +>*τ)
                 (AEIExp AEMLamParent1 AEIRefl))) ⟩
  constructability-e (‵ e₁ ∙ e₂)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       = ⟨ ᾱ₁ ++ construct (ap₁ uz) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (AEIExp AEConAp1
               (+e>*-++ (ziplem-ap2 +>*e₂)
                 (AEIExp AEMApParent2 AEIRefl))) ⟩
  constructability-e (‵ x ← e₁ ∙ e₂)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       = ⟨ ᾱ₁ ++ construct (let₁ x uz) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (AEIExp AEConLet1
               (+e>*-++ (ziplem-let2 +>*e₂)
                 (AEIExp AEMLetParent2 AEIRefl))) ⟩
  constructability-e (‵ℕ n) = ⟨ ∣[ construct (num n) ] , AEIExp AEConNum AEIRefl ⟩
  constructability-e (‵ e₁ + e₂)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       = ⟨ ᾱ₁ ++ construct (plus₁ uz) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (AEIExp AEConPlus1
               (+e>*-++ (ziplem-plus2 +>*e₂)
                 (AEIExp AEMPlusParent2 AEIRefl))) ⟩
  constructability-e ‵tt = ⟨ ∣[ construct tt ] , AEIExp AEConTrue AEIRefl ⟩
  constructability-e ‵ff = ⟨ ∣[ construct ff ] , AEIExp AEConFalse AEIRefl ⟩
  constructability-e (‵ e₁ ∙ e₂ ∙ e₃)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       | ⟨ ᾱ₃ , +>*e₃ ⟩ ← constructability-e e₃
       = ⟨ ᾱ₁ ++ construct (if₁ uz uz) ∷ ᾱ₂ ++ move parent ∷ move (child 3) ∷ ᾱ₃ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (AEIExp AEConIf1
               (+e>*-++ (ziplem-if2 +>*e₂)
                 (AEIExp AEMIfParent2
                   (AEIExp AEMIfChild3
                     (+e>*-++ (ziplem-if3 +>*e₃)
                       (AEIExp AEMIfParent3 AEIRefl)))))) ⟩
  constructability-e (‵⟨ e₁ , e₂ ⟩)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       = ⟨ ᾱ₁ ++ construct (pair₁ uz) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (AEIExp AEConPair1
               (+e>*-++ (ziplem-pair2 +>*e₂)
                 (AEIExp AEMPairParent2 AEIRefl))) ⟩
  constructability-e (‵π₁ e)
    with ⟨ ᾱ , +>*e ⟩ ← constructability-e e
       = ⟨ ᾱ ++ ∣[ construct projl ] ,
           +e>*-++ +>*e
             (AEIExp AEConProjL AEIRefl) ⟩
  constructability-e (‵π₂ e)
    with ⟨ ᾱ , +>*e ⟩ ← constructability-e e
       = ⟨ ᾱ ++ ∣[ construct projr ] ,
           +e>*-++ +>*e
             (AEIExp AEConProjR AEIRefl) ⟩
