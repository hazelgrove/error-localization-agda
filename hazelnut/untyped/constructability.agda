open import prelude
open import core

open import hazelnut.action
open import hazelnut.untyped.zexp
open import hazelnut.untyped.action
open import hazelnut.untyped.erasure

module hazelnut.untyped.constructability where
  -- constructability of types
  constructability-τ : (τ : Typ) → ∃[ ᾱ ] ▹ unknown ◃ + ᾱ +τ>* ▹ τ ◃
  constructability-τ num = ⟨ ∣[ construct tnum ] , TITyp TConNum TIRefl ⟩
  constructability-τ bool = ⟨ ∣[ construct tbool ] , TITyp TConBool TIRefl ⟩
  constructability-τ unknown = ⟨ [] , TIRefl ⟩
  constructability-τ (τ₁ -→ τ₂)
    with ⟨ ᾱ₁ , +>*τ₁ ⟩ ← constructability-τ τ₁
       | ⟨ ᾱ₂ , +>*τ₂ ⟩ ← constructability-τ τ₂
       = ⟨ ᾱ₁ ++ construct tarrow₁ ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +τ>*-++ +>*τ₁ (TITyp TConArrow1 (+τ>*-++ (ziplem-tarr2 +>*τ₂) (TITyp TMArrParent2 TIRefl))) ⟩
  constructability-τ (τ₁ -× τ₂)
    with ⟨ ᾱ₁ , +>*τ₁ ⟩ ← constructability-τ τ₁
       | ⟨ ᾱ₂ , +>*τ₂ ⟩ ← constructability-τ τ₂
       = ⟨ ᾱ₁ ++ construct tprod₁ ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +τ>*-++ +>*τ₁ (TITyp TConProd1 (+τ>*-++ (ziplem-tprod2 +>*τ₂) (TITyp TMProdParent2 TIRefl))) ⟩

  uz : Hole
  uz = 0

  -- constructability of expressions
  constructability-e : ∀ {u} → (e : UExp) → ∃[ ᾱ ] ‵▹ ‵⦇-⦈^ u ◃ + ᾱ +e>* ‵▹ e ◃
  constructability-e (‵⦇-⦈^ u) = ⟨ ∣[ del _ ] , EIExp EDel EIRefl ⟩
  constructability-e (‵ x) = ⟨ ∣[ construct (var x) ] , EIExp EConVar EIRefl ⟩
  constructability-e (‵λ x ∶ τ ∙ e)
    with ⟨ ᾱ₁ , +>*e ⟩ ← constructability-e e
       | ⟨ ᾱ₂ , +>*τ ⟩ ← constructability-τ τ
       = ⟨ ᾱ₁ ++ construct (lam x) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e
             (EIExp EConLam
               (+e>*-++ (ziplem-lam1 +>*τ)
                 (EIExp EMLamParent1 EIRefl))) ⟩
  constructability-e (‵ e₁ ∙ e₂)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       = ⟨ ᾱ₁ ++ construct (ap₁ uz) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (EIExp EConAp1
               (+e>*-++ (ziplem-ap2 +>*e₂)
                 (EIExp EMApParent2 EIRefl))) ⟩
  constructability-e (‵ x ← e₁ ∙ e₂)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       = ⟨ ᾱ₁ ++ construct (let₁ x uz) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (EIExp EConLet1
               (+e>*-++ (ziplem-let2 +>*e₂)
                 (EIExp EMLetParent2 EIRefl))) ⟩
  constructability-e (‵ℕ n) = ⟨ ∣[ construct (num n) ] , EIExp EConNum EIRefl ⟩
  constructability-e (‵ e₁ + e₂)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       = ⟨ ᾱ₁ ++ construct (plus₁ uz) ∷ ᾱ₂ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (EIExp EConPlus1
               (+e>*-++ (ziplem-plus2 +>*e₂)
                 (EIExp EMPlusParent2 EIRefl))) ⟩
  constructability-e ‵tt = ⟨ ∣[ construct tt ] , EIExp EConTrue EIRefl ⟩
  constructability-e ‵ff = ⟨ ∣[ construct ff ] , EIExp EConFalse EIRefl ⟩
  constructability-e (‵ e₁ ∙ e₂ ∙ e₃)
    with ⟨ ᾱ₁ , +>*e₁ ⟩ ← constructability-e e₁
       | ⟨ ᾱ₂ , +>*e₂ ⟩ ← constructability-e e₂
       | ⟨ ᾱ₃ , +>*e₃ ⟩ ← constructability-e e₃
       = ⟨ ᾱ₁ ++ construct (if₁ uz uz) ∷ ᾱ₂ ++ move parent ∷ move (child 3) ∷ ᾱ₃ ++ ∣[ move parent ] ,
           +e>*-++ +>*e₁
             (EIExp EConIf1
               (+e>*-++ (ziplem-if2 +>*e₂)
                 (EIExp EMIfParent2
                   (EIExp EMIfChild3
                     (+e>*-++ (ziplem-if3 +>*e₃)
                       (EIExp EMIfParent3 EIRefl)))))) ⟩
