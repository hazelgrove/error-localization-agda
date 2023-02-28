open import prelude
open import core

open import hazelnut.action
open import hazelnut.untyped.zexp
open import hazelnut.untyped.action
open import hazelnut.untyped.erasure

module hazelnut.untyped.mei where
  -- movement erasure invariance
  movement-erasure-invariance-τ : ∀ {τ^ τ^′ δ} → τ^ + move δ +τ> τ^′ → τ^ ◇τ ≡ τ^′ ◇τ
  movement-erasure-invariance-τ TMArrChild1       = refl
  movement-erasure-invariance-τ TMArrChild2       = refl
  movement-erasure-invariance-τ TMArrParent1      = refl
  movement-erasure-invariance-τ TMArrParent2      = refl
  movement-erasure-invariance-τ (TZipArr1 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl
  movement-erasure-invariance-τ (TZipArr2 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl
  movement-erasure-invariance-τ TMProdChild1       = refl
  movement-erasure-invariance-τ TMProdChild2       = refl
  movement-erasure-invariance-τ TMProdParent1      = refl
  movement-erasure-invariance-τ TMProdParent2      = refl
  movement-erasure-invariance-τ (TZipProd1 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl
  movement-erasure-invariance-τ (TZipProd2 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl

  movement-erasure-invariance-e : ∀ {ê ê′ δ} → ê + move δ +e> ê′ → ê ◇ ≡ ê′ ◇
  movement-erasure-invariance-e EMLamChild1       = refl
  movement-erasure-invariance-e EMLamChild2       = refl
  movement-erasure-invariance-e EMLamParent1      = refl
  movement-erasure-invariance-e EMLamParent2      = refl
  movement-erasure-invariance-e EMApChild1        = refl
  movement-erasure-invariance-e EMApChild2        = refl
  movement-erasure-invariance-e EMApParent1       = refl
  movement-erasure-invariance-e EMApParent2       = refl
  movement-erasure-invariance-e EMLetChild1       = refl
  movement-erasure-invariance-e EMLetChild2       = refl
  movement-erasure-invariance-e EMLetParent1      = refl
  movement-erasure-invariance-e EMLetParent2      = refl
  movement-erasure-invariance-e EMPlusChild1      = refl
  movement-erasure-invariance-e EMPlusChild2      = refl
  movement-erasure-invariance-e EMPlusParent1     = refl
  movement-erasure-invariance-e EMPlusParent2     = refl
  movement-erasure-invariance-e EMIfChild1        = refl
  movement-erasure-invariance-e EMIfChild2        = refl
  movement-erasure-invariance-e EMIfChild3        = refl
  movement-erasure-invariance-e EMIfParent1       = refl
  movement-erasure-invariance-e EMIfParent2       = refl
  movement-erasure-invariance-e EMIfParent3       = refl
  movement-erasure-invariance-e EMPairChild1      = refl
  movement-erasure-invariance-e EMPairChild2      = refl
  movement-erasure-invariance-e EMPairParent1     = refl
  movement-erasure-invariance-e EMPairParent2     = refl
  movement-erasure-invariance-e EMProjLChild      = refl
  movement-erasure-invariance-e EMProjLParent     = refl
  movement-erasure-invariance-e EMProjRChild      = refl
  movement-erasure-invariance-e EMProjRParent     = refl
  movement-erasure-invariance-e (EZipLam1 τ^+>τ^′)
    rewrite movement-erasure-invariance-τ τ^+>τ^′ = refl
  movement-erasure-invariance-e (EZipLam2 ê+>ê′)
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipAp1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipAp2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipLet1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipLet2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipPlus1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipPlus2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipIf1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipIf2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipIf3 ê+>ê′)
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipPair1 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipPair2 ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipProjL ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
  movement-erasure-invariance-e (EZipProjR ê+>ê′) 
    rewrite movement-erasure-invariance-e ê+>ê′   = refl
