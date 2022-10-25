open import prelude

-- types
module typ where
  data Typ : Set where
    num     : Typ
    bool    : Typ
    unknown : Typ
    _-→_    : Typ → Typ → Typ

  infixr 25  _-→_

  -- base types
  data _base : (τ : Typ) → Set where
    BNum  : num base
    BBool : bool base

  -- consistency
  data _~_ : (τ₁ τ₂ : Typ) → Set where
    TCRefl     : {τ : Typ} → τ ~ τ
    TCUnknown1 : {τ : Typ} → τ ~ unknown
    TCUnknown2 : {τ : Typ} → unknown ~ τ
    TCArr      : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                → τ₁ ~ τ₁′
                → τ₂ ~ τ₂′
                → τ₁ -→ τ₂ ~ τ₁′ -→ τ₂′

  -- inconsistency
  data _~̸_ : (τ₁ τ₂ : Typ) → Set where
    TICBaseArr1 : {τ τ₁ τ₂ : Typ}
                 → τ base
                 → τ ~̸ τ₁ -→ τ₂
    TICBaseArr2 : {τ τ₁ τ₂ : Typ}
                 → τ base
                 → τ₁ -→ τ₂ ~̸ τ
    TICArr1     : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                 → τ₁ ~̸ τ₁′
                 → τ₁ -→ τ₂ ~̸ τ₁′ -→ τ₂′
    TICArr2     : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                 → τ₂ ~̸ τ₂′
                 → τ₁ -→ τ₂ ~̸ τ₁′ -→ τ₂′

  -- matched arrow
  data _▸_-→_ : (τ τ₁ τ₂ : Typ) → Set where
    TMAHole : unknown ▸ unknown -→ unknown
    TMAArr  : {τ₁ τ₂ : Typ} → τ₁ -→ τ₂ ▸ τ₁ -→ τ₂

  _!▸ : Typ → Set
  τ !▸ = ∀ {τ₁ τ₂} → (τ ▸ τ₁ -→ τ₂) → ⊥

  -- lub join
  data _⊔_⇒_ : (τ₁ τ₂ τ : Typ) → Set where
    TJUnknown1 : {τ : Typ} → τ ⊔ unknown ⇒ unknown
    TJUnknown2 : {τ : Typ} → unknown ⊔ τ ⇒ unknown
    TJNum      : num ⊔ num ⇒ num
    TJBool     : bool ⊔ bool ⇒ bool
    TJArr      : {τ₁ τ₂ τ₁′ τ₂′ τ₁″ τ₂″ : Typ}
                → τ₁ ⊔ τ₁′ ⇒ τ₁″
                → τ₂ ⊔ τ₂′ ⇒ τ₂″
                → τ₁ -→ τ₂ ⊔ τ₁′ -→ τ₂′ ⇒ τ₁″ -→ τ₂″

  -→≡ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₁ ≡ τ₁′ → τ₂ ≡ τ₂′ → τ₁ -→ τ₂ ≡ τ₁′ -→ τ₂′
  -→≡ refl refl = refl

  -→≢₁ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₁ ≢ τ₁′ → τ₁ -→ τ₂ ≢ τ₁′ -→ τ₂′
  -→≢₁ τ₁≢τ₁′ refl = τ₁≢τ₁′ refl

  -→≢₂ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₂ ≢ τ₂′ → τ₁ -→ τ₂ ≢ τ₁′ -→ τ₂′
  -→≢₂ τ₂≢τ₂′ refl = τ₂≢τ₂′ refl

  -- decidable equality
  _≡Typ?_ : (τ : Typ) → (τ′ : Typ) → Dec (τ ≡ τ′)
  num        ≡Typ? num          = yes refl
  num        ≡Typ? bool         = no (λ ())
  num        ≡Typ? unknown      = no (λ ())
  num        ≡Typ? (_ -→ _)     = no (λ ())
  bool       ≡Typ? num          = no (λ ())
  bool       ≡Typ? bool         = yes refl
  bool       ≡Typ? unknown      = no (λ ())
  bool       ≡Typ? (_ -→ _)     = no (λ ())
  unknown    ≡Typ? num          = no (λ ())
  unknown    ≡Typ? bool         = no (λ ())
  unknown    ≡Typ? unknown      = yes refl
  unknown    ≡Typ? (_ -→ _)     = no (λ ())
  (_ -→ _)   ≡Typ? num          = no (λ ())
  (_ -→ _)   ≡Typ? bool         = no (λ ())
  (_ -→ _)   ≡Typ? unknown      = no (λ ())
  (τ₁ -→ τ₂) ≡Typ? (τ₁′ -→ τ₂′) with τ₁ ≡Typ? τ₁′ | τ₂ ≡Typ? τ₂′
  ... | yes τ₁≡τ₁′ | yes τ₂≡τ₂′ = yes (-→≡ τ₁≡τ₁′ τ₂≡τ₂′)
  ... | _          | no τ₂≢τ₂′  = no (-→≢₂ τ₂≢τ₂′)
  ... | no τ₁≢τ₁′  | _          = no (-→≢₁ τ₁≢τ₁′)

  -- apartness of consistency and inconsistency
  ~→¬~̸ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ¬ (τ₁ ~̸ τ₂)
  ~→¬~̸ TCRefl                (TICArr1 τ₁~̸τ₁)  = ~→¬~̸ TCRefl τ₁~̸τ₁
  ~→¬~̸ TCRefl                (TICArr2 τ₂~̸τ₂)  = ~→¬~̸ TCRefl τ₂~̸τ₂
  ~→¬~̸ TCUnknown1            (TICBaseArr2 ())
  ~→¬~̸ TCUnknown2            (TICBaseArr1 ())
  ~→¬~̸ (TCArr τ₁~τ₁′ τ₂~τ₂′) (TICArr1 τ₁~̸τ₁′) = ~→¬~̸ τ₁~τ₁′ τ₁~̸τ₁′
  ~→¬~̸ (TCArr τ₁~τ₁′ τ₂~τ₂′) (TICArr2 τ₁~̸τ₁′) = ~→¬~̸ τ₂~τ₂′ τ₁~̸τ₁′

  ~̸→¬~ : ∀ {τ₁ τ₂} → τ₁ ~̸ τ₂ → ¬ (τ₁ ~ τ₂)
  ~̸→¬~ (TICBaseArr1 BNum)  ()
  ~̸→¬~ (TICBaseArr1 BBool) ()
  ~̸→¬~ (TICBaseArr2 BNum)  ()
  ~̸→¬~ (TICBaseArr2 BBool) ()
  ~̸→¬~ (TICArr1 τ₁~̸τ₁)   TCRefl          = ~̸→¬~ τ₁~̸τ₁ TCRefl
  ~̸→¬~ (TICArr1 τ₁~̸τ₁′) (TCArr τ₁~τ₁′ _) = ~̸→¬~ τ₁~̸τ₁′ τ₁~τ₁′
  ~̸→¬~ (TICArr2 τ₂~̸τ₂)   TCRefl          = ~̸→¬~ τ₂~̸τ₂ TCRefl
  ~̸→¬~ (TICArr2 τ₂~̸τ₂′) (TCArr _ τ₂~τ₂′) = ~̸→¬~ τ₂~̸τ₂′ τ₂~τ₂′

  -- consistency is symmetric
  ~-sym : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → τ₂ ~ τ₁
  ~-sym TCRefl                = TCRefl
  ~-sym TCUnknown1            = TCUnknown2
  ~-sym TCUnknown2            = TCUnknown1
  ~-sym (TCArr τ₁~τ₁′ τ₂~τ₂′) = TCArr (~-sym τ₁~τ₁′) (~-sym τ₂~τ₂′)

  -- inconsistency is symmetric
  ~̸-sym : ∀ {τ₁ τ₂} → τ₁ ~̸ τ₂ → τ₂ ~̸ τ₁
  ~̸-sym (TICBaseArr1 b)  = TICBaseArr2 b
  ~̸-sym (TICBaseArr2 b)  = TICBaseArr1 b
  ~̸-sym (TICArr1 τ₁~̸τ₁′) = TICArr1 (~̸-sym τ₁~̸τ₁′)
  ~̸-sym (TICArr2 τ₂~̸τ₂′) = TICArr2 (~̸-sym τ₂~̸τ₂′)

  -- join is symmetric
  ⊔-sym : ∀ {τ₁ τ₂ τ} → τ₁ ⊔ τ₂ ⇒ τ → τ₂ ⊔ τ₁ ⇒ τ
  ⊔-sym TJUnknown1          = TJUnknown2
  ⊔-sym TJUnknown2          = TJUnknown1
  ⊔-sym TJNum               = TJNum
  ⊔-sym TJBool              = TJBool
  ⊔-sym (TJArr ⊔⇒τ₁″ ⊔⇒τ₂″) = TJArr (⊔-sym ⊔⇒τ₁″) (⊔-sym ⊔⇒τ₂″)

  -- join is a function
  ⊔-unicity : ∀ {τ₁ τ₂ τ τ′} → τ₁ ⊔ τ₂ ⇒ τ → τ₁ ⊔ τ₂ ⇒ τ′ → τ ≡ τ′ 
  ⊔-unicity TJUnknown1 TJUnknown1                         = refl
  ⊔-unicity TJUnknown1 TJUnknown2                         = refl
  ⊔-unicity TJUnknown2 TJUnknown1                         = refl
  ⊔-unicity TJUnknown2 TJUnknown2                         = refl
  ⊔-unicity TJNum TJNum                                   = refl
  ⊔-unicity TJBool TJBool                                 = refl
  ⊔-unicity (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) (TJArr τ₁⊔τ₁′′ τ₂⊔τ₂′′) = -→≡ (⊔-unicity τ₁⊔τ₁′ τ₁⊔τ₁′′) (⊔-unicity τ₂⊔τ₂′ τ₂⊔τ₂′′)

  -- join existence means that types are consistent
  ⊔→~ : ∀ {τ τ₁ τ₂} → τ₁ ⊔ τ₂ ⇒ τ → τ₁ ~ τ₂
  ⊔→~ TJUnknown1            = TCUnknown1
  ⊔→~ TJUnknown2            = TCUnknown2
  ⊔→~ TJNum                 = TCRefl
  ⊔→~ TJBool                = TCRefl
  ⊔→~ (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) = TCArr (⊔→~ τ₁⊔τ₁′) (⊔→~ τ₂⊔τ₂′)

  -- consistent types have a join
  ~→⊔ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ∃[ τ ] τ₁ ⊔ τ₂ ⇒ τ
  ~→⊔ {num}      TCRefl                                            = ⟨ num , TJNum ⟩
  ~→⊔ {bool}     TCRefl                                            = ⟨ bool , TJBool ⟩
  ~→⊔ {unknown}  TCRefl                                            = ⟨ unknown , TJUnknown1 ⟩
  ~→⊔ {τ₁ -→ τ₂} TCRefl     with ~→⊔ {τ₁} TCRefl | ~→⊔ {τ₂} TCRefl
  ...                          | ⟨ τ₁′ , ⊔⇒τ₁′ ⟩ | ⟨ τ₂′ , ⊔⇒τ₂′ ⟩ = ⟨ τ₁′ -→ τ₂′ , TJArr ⊔⇒τ₁′ ⊔⇒τ₂′ ⟩
  ~→⊔ TCUnknown1                                                   = ⟨ unknown , TJUnknown1 ⟩
  ~→⊔ TCUnknown2                                                   = ⟨ unknown , TJUnknown2 ⟩
  ~→⊔ (TCArr τ₁~τ₁′ τ₂~τ₂′) with ~→⊔ τ₁~τ₁′ | ~→⊔ τ₂~τ₂′
  ...                          | ⟨ τ₁″ , ⊔⇒τ₁″ ⟩ | ⟨ τ₂″ , ⊔⇒τ₂″ ⟩ = ⟨ τ₁″ -→ τ₂″ , TJArr ⊔⇒τ₁″ ⊔⇒τ₂″ ⟩

  -- join existence means that types are not inconsistent
  ⊔→¬~̸ : ∀ {τ τ₁ τ₂} → τ₁ ⊔ τ₂ ⇒ τ → ¬ (τ₁ ~̸ τ₂)
  ⊔→¬~̸ ⊔⇒τ τ₁~̸τ₂ with ⊔→~ ⊔⇒τ
  ...               | τ₁~τ₂ = ~→¬~̸ τ₁~τ₂ τ₁~̸τ₂
