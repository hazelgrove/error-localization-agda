open import prelude
open import core

open import hazelnut.action
open import hazelnut.untyped.zexp
open import hazelnut.untyped.action
open import hazelnut.untyped.erasure

module hazelnut.untyped.determinism where
  determinism-τ : ∀ {τ^ τ^′ τ^″ α} → τ^ + α +τ> τ^′ → τ^ + α +τ> τ^″ → τ^′ ≡ τ^″
  determinism-τ TMArrChild1        TMArrChild1  = refl
  determinism-τ TMArrChild2        TMArrChild2  = refl
  determinism-τ TMArrParent1       TMArrParent1 = refl
  determinism-τ TMArrParent2       TMArrParent2 = refl
  determinism-τ TMArrParent2       (TZipArr2 ())
  determinism-τ TDel               TDel         = refl
  determinism-τ TConArrow1         TConArrow1   = refl
  determinism-τ TConArrow2         TConArrow2   = refl
  determinism-τ TConNum            TConNum      = refl
  determinism-τ TConBool           TConBool     = refl
  determinism-τ (TZipArr1 τ^+>τ^′) (TZipArr1 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″       = refl
  determinism-τ (TZipArr2 τ^+>τ^′) (TZipArr2 τ^+>τ^″)
    rewrite determinism-τ τ^+>τ^′ τ^+>τ^″       = refl

  determinism*-τ : ∀ {τ^ τ^′ τ^″ ᾱ} → τ^ + ᾱ +τ>* τ^′ → τ^ + ᾱ +τ>* τ^″ → τ^′ ≡ τ^″
  determinism*-τ TIRefl                     TIRefl = refl
  determinism*-τ (TITyp τ₁^+>τ₂^ τ₂^+>*τ₃^) (TITyp τ₁^+>τ₂^′ τ₂^+>*τ₃^′)
    rewrite determinism-τ τ₁^+>τ₂^ τ₁^+>τ₂^′
    rewrite determinism*-τ τ₂^+>*τ₃^ τ₂^+>*τ₃^′    = refl

  -- determinism-e : ∀ {ê ê′ ê″ α} → ê + α +e> ê′ → ê + α +e> ê″ → ê′ ≡ ê″
  -- determinism-e EMLamChild1 EMLamChild1 = {! !}
  -- determinism-e EMLamChild2 EMLamChild2 = {! !}
  -- determinism-e EMLamParent1 EMLamParent1 = {! !}
  -- determinism-e EMLamParent2 EMLamParent2 = {! !}
  -- determinism-e EMApChild1 EMApChild1 = {! !}
  -- determinism-e EMApChild2 EMApChild2 = {! !}
  -- determinism-e EMApParent1 EMApParent1 = {! !}
  -- determinism-e EMApParent2 EMApParent2 = {! !}
  -- determinism-e EMLetChild1 EMLetChild1 = {! !}
  -- determinism-e EMLetChild2 EMLetChild2 = {! !}
  -- determinism-e EMLetParent1 EMLetParent1 = {! !}
  -- determinism-e EMLetParent2 EMLetParent2 = {! !}
  -- determinism-e EMPlusChild1 EMPlusChild1 = {! !}
  -- determinism-e EMPlusChild2 EMPlusChild2 = {! !}
  -- determinism-e EMPlusParent1 EMPlusParent1 = {! !}
  -- determinism-e EMPlusParent2 EMPlusParent2 = {! !}
  -- determinism-e EMIfChild1 EMIfChild1 = {! !}
  -- determinism-e EMIfChild2 EMIfChild2 = {! !}
  -- determinism-e EMIfChild3 EMIfChild3 = {! !}
  -- determinism-e EMIfParent1 EMIfParent1 = {! !}
  -- determinism-e EMIfParent2 EMIfParent2 = {! !}
  -- determinism-e EMIfParent3 EMIfParent3 = {! !}
  -- determinism-e EDel EDel = {! !}
  -- determinism-e EConVar EConVar = {! !}
  -- determinism-e EConLam EConLam = {! !}
  -- determinism-e EConAp1 EConAp1 = {! !}
  -- determinism-e EConAp2 EConAp2 = {! !}
  -- determinism-e EConLet1 EConLet1 = {! !}
  -- determinism-e EConLet2 EConLet2 = {! !}
  -- determinism-e EConNum EConNum = {! !}
  -- determinism-e EConPlus1 EConPlus1 = {! !}
  -- determinism-e EConPlus2 EConPlus2 = {! !}
  -- determinism-e EConTrue EConTrue = {! !}
  -- determinism-e EConFalse EConFalse = {! !}
  -- determinism-e EConIf1 EConIf1 = {! !}
  -- determinism-e EConIf2 EConIf2 = {! !}
  -- determinism-e EConIf3 EConIf3 = {! !}
  -- determinism-e (EZipLam1 τ^+>τ^′) y = {! !}
  -- determinism-e (EZipLam2 x) y = {! !}
  -- determinism-e (EZipAp1 x) y = {! !}
  -- determinism-e (EZipAp2 x) y = {! !}
  -- determinism-e (EZipLet1 x) y = {! !}
  -- determinism-e (EZipLet2 x) y = {! !}
  -- determinism-e (EZipPlus1 x) y = {! !}
  -- determinism-e (EZipPlus2 x) y = {! !}
  -- determinism-e (EZipIf1 x) y = {! !}
  -- determinism-e (EZipIf2 x) y = {! !}
  -- determinism-e (EZipIf3 x) y = {! !}
