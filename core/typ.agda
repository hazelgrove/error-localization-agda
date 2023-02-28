open import prelude

-- types
module core.typ where
  data Typ : Set where
    num     : Typ
    bool    : Typ
    unknown : Typ
    _-→_    : Typ → Typ → Typ
    _-×_     : Typ → Typ → Typ

  infixr 25  _-→_
  infixr 24  _-×_

  module equality where
    -- arrow type equality
    -→-≡ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ ≡ τ₁′) → (τ₂ ≡ τ₂′) → τ₁ -→ τ₂ ≡ τ₁′ -→ τ₂′
    -→-≡ refl refl = refl

    -- inverted arrow type equality
    -→-inj : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ -→ τ₂ ≡ τ₁′ -→ τ₂′) → τ₁ ≡ τ₁′ × τ₂ ≡ τ₂′
    -→-inj refl = ⟨ refl , refl ⟩

    -- arrow type inequalities
    -→-≢₁ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ ≢ τ₁′) → τ₁ -→ τ₂ ≢ τ₁′ -→ τ₂′
    -→-≢₁ τ₁≢τ₁′ refl = τ₁≢τ₁′ refl

    -→-≢₂ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₂ ≢ τ₂′) → τ₁ -→ τ₂ ≢ τ₁′ -→ τ₂′
    -→-≢₂ τ₂≢τ₂′ refl = τ₂≢τ₂′ refl

    -- product type equality
    -×-≡ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ ≡ τ₁′) → (τ₂ ≡ τ₂′) → τ₁ -× τ₂ ≡ τ₁′ -× τ₂′
    -×-≡ refl refl = refl

    -- inverted product type equality
    -×-inj : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ -× τ₂ ≡ τ₁′ -× τ₂′) → τ₁ ≡ τ₁′ × τ₂ ≡ τ₂′
    -×-inj refl = ⟨ refl , refl ⟩

    -- product type inequalities
    -×-≢₁ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₁ ≢ τ₁′) → τ₁ -× τ₂ ≢ τ₁′ -× τ₂′
    -×-≢₁ τ₁≢τ₁′ refl = τ₁≢τ₁′ refl

    -×-≢₂ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → (τ₂ ≢ τ₂′) → τ₁ -× τ₂ ≢ τ₁′ -× τ₂′
    -×-≢₂ τ₂≢τ₂′ refl = τ₂≢τ₂′ refl

    -- decidable equality
    _≡τ?_ : (τ : Typ) → (τ′ : Typ) → Dec (τ ≡ τ′)
    num        ≡τ? num      = yes refl
    num        ≡τ? bool     = no (λ ())
    num        ≡τ? unknown  = no (λ ())
    num        ≡τ? (_ -→ _) = no (λ ())
    num        ≡τ? (_ -× _) = no (λ ())
    bool       ≡τ? num      = no (λ ())
    bool       ≡τ? bool     = yes refl
    bool       ≡τ? unknown  = no (λ ())
    bool       ≡τ? (_ -→ _) = no (λ ())
    bool       ≡τ? (_ -× _) = no (λ ())
    unknown    ≡τ? num      = no (λ ())
    unknown    ≡τ? bool     = no (λ ())
    unknown    ≡τ? unknown  = yes refl
    unknown    ≡τ? (_ -→ _) = no (λ ())
    unknown    ≡τ? (_ -× _) = no (λ ())
    (_ -→ _)   ≡τ? num      = no (λ ())
    (_ -→ _)   ≡τ? bool     = no (λ ())
    (_ -→ _)   ≡τ? unknown  = no (λ ())
    (τ₁ -→ τ₂) ≡τ? (τ₁′ -→ τ₂′) with τ₁ ≡τ? τ₁′ | τ₂ ≡τ? τ₂′
    ...                           | yes refl    | yes refl  = yes refl
    ...                           | _           | no τ₂≢τ₂′ = no  (-→-≢₂ τ₂≢τ₂′)
    ...                           | no τ₁≢τ₁′   | _         = no  (-→-≢₁ τ₁≢τ₁′)
    (_ -→ _)   ≡τ? (_ -× _) = no (λ ())
    (_ -× _)   ≡τ? num      = no (λ ())
    (_ -× _)   ≡τ? bool     = no (λ ())
    (_ -× _)   ≡τ? unknown  = no (λ ())
    (_ -× _)   ≡τ? (_ -→ _) = no (λ ())
    (τ₁ -× τ₂) ≡τ? (τ₁′ -× τ₂′) with τ₁ ≡τ? τ₁′ | τ₂ ≡τ? τ₂′
    ...                           | yes refl    | yes refl  = yes refl
    ...                           | _           | no τ₂≢τ₂′ = no  (-×-≢₂ τ₂≢τ₂′)
    ...                           | no τ₁≢τ₁′   | _         = no  (-×-≢₁ τ₁≢τ₁′)

  module base where
    -- base types
    data _base : (τ : Typ) → Set where
      BNum  : num base
      BBool : bool base

    -- decidable base
    _base? : (τ : Typ) → Dec (τ base)
    num      base? = yes BNum
    bool     base? = yes BBool
    unknown  base? = no (λ ())
    (_ -→ _) base? = no (λ ())
    (_ -× _) base? = no (λ ())

    -- base judgment equality
    base-≡ : ∀ {τ} → (b₁ : τ base) → (b₂ : τ base) → b₁ ≡ b₂
    base-≡ BNum BNum = refl
    base-≡ BBool BBool = refl

  module consistency where
    open base

    -- consistency
    data _~_ : (τ₁ τ₂ : Typ) → Set where
      TCUnknown     : unknown ~ unknown
      TCBase        : {τ : Typ} → (b : τ base) → τ ~ τ
      TCUnknownBase : {τ : Typ} → (b : τ base) → unknown ~ τ
      TCBaseUnknown : {τ : Typ} → (b : τ base) → τ ~ unknown
      TCArr         : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                     → (τ₁~τ₁′ : τ₁ ~ τ₁′)
                     → (τ₂~τ₂′ : τ₂ ~ τ₂′)
                     → τ₁ -→ τ₂ ~ τ₁′ -→ τ₂′
      TCUnknownArr  : {τ₁ τ₂ : Typ}
                     → unknown ~ τ₁ -→ τ₂
      TCArrUnknown  : {τ₁ τ₂ : Typ}
                     → τ₁ -→ τ₂ ~ unknown
      TCProd        : {τ₁ τ₂ τ₁′ τ₂′ : Typ}
                     → (τ₁~τ₁′ : τ₁ ~ τ₁′)
                     → (τ₂~τ₂′ : τ₂ ~ τ₂′)
                     → τ₁ -× τ₂ ~ τ₁′ -× τ₂′
      TCUnknownProd  : {τ₁ τ₂ : Typ}
                     → unknown ~ τ₁ -× τ₂
      TCProdUnknown  : {τ₁ τ₂ : Typ}
                     → τ₁ -× τ₂ ~ unknown

    -- inconsistency
    _~̸_ : (τ₁ : Typ) → (τ₂ : Typ) → Set
    τ₁ ~̸ τ₂ = ¬ (τ₁ ~ τ₂)

    -- consistency reflexivity
    ~-refl : ∀ {τ} → τ ~ τ
    ~-refl {num}      = TCBase BNum
    ~-refl {bool}     = TCBase BBool
    ~-refl {unknown}  = TCUnknown
    ~-refl {τ₁ -→ τ₂} = TCArr ~-refl ~-refl
    ~-refl {τ₁ -× τ₂} = TCProd ~-refl ~-refl

    -- consistency symmetry
    ~-sym : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → τ₂ ~ τ₁
    ~-sym TCUnknown              = TCUnknown
    ~-sym (TCBase b)             = TCBase b
    ~-sym (TCUnknownBase b)      = TCBaseUnknown b
    ~-sym (TCBaseUnknown b)      = TCUnknownBase b
    ~-sym TCUnknownArr           = TCArrUnknown
    ~-sym TCArrUnknown           = TCUnknownArr
    ~-sym (TCArr τ₁~τ₁′ τ₂~τ₂′)  = TCArr (~-sym τ₁~τ₁′) (~-sym τ₂~τ₂′)
    ~-sym (TCProd τ₁~τ₁′ τ₂~τ₂′) = TCProd (~-sym τ₁~τ₁′) (~-sym τ₂~τ₂′)
    ~-sym TCUnknownProd          = TCProdUnknown
    ~-sym TCProdUnknown          = TCUnknownProd

    -- consistency with unknown type
    ~-unknown₁ : ∀ {τ} → unknown ~ τ
    ~-unknown₁ {num}     = TCUnknownBase BNum
    ~-unknown₁ {bool}    = TCUnknownBase BBool
    ~-unknown₁ {unknown} = TCUnknown
    ~-unknown₁ {_ -→ _}  = TCUnknownArr
    ~-unknown₁ {_ -× _}  = TCUnknownProd

    ~-unknown₂ : ∀ {τ} → τ ~ unknown
    ~-unknown₂ {num}     = TCBaseUnknown BNum
    ~-unknown₂ {bool}    = TCBaseUnknown BBool
    ~-unknown₂ {unknown} = TCUnknown
    ~-unknown₂ {_ -→ _}  = TCArrUnknown
    ~-unknown₂ {_ -× _}  = TCProdUnknown

    -- consistency derivation equality
    ~-≡ : ∀ {τ₁ τ₂} → (τ₁~τ₂ : τ₁ ~ τ₂) → (τ₁~τ₂′ : τ₁ ~ τ₂) → τ₁~τ₂ ≡ τ₁~τ₂′
    ~-≡ TCUnknown             TCUnknown               = refl
    ~-≡ (TCBase b)            (TCBase b′)
      rewrite base-≡ b b′                             = refl
    ~-≡ (TCUnknownBase b)     (TCUnknownBase b′)
      rewrite base-≡ b b′                             = refl
    ~-≡ (TCBaseUnknown b)     (TCBaseUnknown b′)
      rewrite base-≡ b b′                             = refl
    ~-≡ (TCArr τ₁~τ₁′ τ₂~τ₂′) (TCArr τ₁~τ₁′′ τ₂~τ₂′′)
      rewrite ~-≡ τ₁~τ₁′ τ₁~τ₁′′ | ~-≡ τ₂~τ₂′ τ₂~τ₂′′ = refl
    ~-≡ TCUnknownArr          TCUnknownArr            = refl
    ~-≡ TCArrUnknown          TCArrUnknown            = refl
    ~-≡ (TCProd τ₁~τ₁′ τ₂~τ₂′) (TCProd τ₁~τ₁′′ τ₂~τ₂′′)
      rewrite ~-≡ τ₁~τ₁′ τ₁~τ₁′′ | ~-≡ τ₂~τ₂′ τ₂~τ₂′′ = refl
    ~-≡ TCUnknownProd          TCUnknownProd          = refl
    ~-≡ TCProdUnknown          TCProdUnknown          = refl

    -- inconsistency derivation equality
    ~̸-≡ : ∀ {τ₁ τ₂} → (τ₁~̸τ₂ : τ₁ ~̸ τ₂) → (τ₁~̸τ₂′ : τ₁ ~̸ τ₂) → τ₁~̸τ₂ ≡ τ₁~̸τ₂′
    ~̸-≡ τ₁~̸τ₂ τ₁~̸τ₂′ rewrite ¬-≡ τ₁~̸τ₂ τ₁~̸τ₂′ = refl

    -- arrow type inconsistencies
    -→-~̸₁ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₁ ~̸ τ₁′ → τ₁ -→ τ₂ ~̸ τ₁′ -→ τ₂′
    -→-~̸₁ τ₁~̸τ₁′ = λ { (TCBase ()) ; (TCArr τ₁~τ₁′ _) → τ₁~̸τ₁′ τ₁~τ₁′ }

    -→-~̸₂ : ∀ {τ₁ τ₂ τ₁′ τ₂′} → τ₂ ~̸ τ₂′ → τ₁ -→ τ₂ ~̸ τ₁′ -→ τ₂′
    -→-~̸₂ τ₂~̸τ₂′ = λ { (TCBase ()) ; (TCArr _ τ₂~τ₂′) → τ₂~̸τ₂′ τ₂~τ₂′ }

    -- decidable consistency
    _~?_ : (τ : Typ) → (τ′ : Typ) → Dec (τ ~ τ′)
    unknown    ~? num      = yes (TCUnknownBase BNum)
    unknown    ~? bool     = yes (TCUnknownBase BBool)
    unknown    ~? unknown  = yes TCUnknown
    unknown    ~? (_ -→ _) = yes TCUnknownArr
    unknown    ~? (_ -× _) = yes TCUnknownProd
    num        ~? num      = yes (TCBase BNum)
    num        ~? bool     = no  (λ ())
    num        ~? unknown  = yes (TCBaseUnknown BNum)
    num        ~? (_ -→ _) = no  (λ ())
    num        ~? (_ -× _) = no  (λ ())
    bool       ~? num      = no  (λ ())
    bool       ~? bool     = yes (TCBase BBool)
    bool       ~? unknown  = yes (TCBaseUnknown BBool)
    bool       ~? (_ -→ _) = no  (λ ())
    bool       ~? (_ -× _) = no  (λ ())
    (_ -→ _)   ~? num      = no  (λ ())
    (_ -→ _)   ~? bool     = no  (λ ())
    (_ -→ _)   ~? unknown  = yes TCArrUnknown
    (τ₁ -→ τ₂) ~? (τ₁′ -→ τ₂′) with τ₁ ~? τ₁′  | τ₂ ~? τ₂′
    ...                           | yes τ₁~τ₁′ | yes τ₂~τ₂′ = yes (TCArr τ₁~τ₁′ τ₂~τ₂′)
    ...                           | _          | no ¬τ₂~τ₂′ = no λ { (TCBase ()) ; (TCArr _ τ₂~τ₂′) → ¬τ₂~τ₂′ τ₂~τ₂′ }
    ...                           | no ¬τ₁~τ₁′ | _          = no λ { (TCBase ()) ; (TCArr τ₁~τ₁′ _) → ¬τ₁~τ₁′ τ₁~τ₁′ }
    (_ -→ _)   ~? (_ -× _) = no  (λ ())
    (_ -× _)   ~? num      = no  (λ ())
    (_ -× _)   ~? bool     = no  (λ ())
    (_ -× _)   ~? unknown  = yes TCProdUnknown
    (_ -× _)   ~? (_ -→ _) = no  (λ ())
    (τ₁ -× τ₂) ~? (τ₁′ -× τ₂′) with τ₁ ~? τ₁′  | τ₂ ~? τ₂′
    ...                           | yes τ₁~τ₁′ | yes τ₂~τ₂′ = yes (TCProd τ₁~τ₁′ τ₂~τ₂′)
    ...                           | _          | no ¬τ₂~τ₂′ = no λ { (TCBase ()) ; (TCProd _ τ₂~τ₂′) → ¬τ₂~τ₂′ τ₂~τ₂′ }
    ...                           | no ¬τ₁~τ₁′ | _          = no λ { (TCBase ()) ; (TCProd τ₁~τ₁′ _) → ¬τ₁~τ₁′ τ₁~τ₁′ }

  module matched where
    open equality
    open consistency

    -- matched arrow
    data _▸_-→_ : (τ τ₁ τ₂ : Typ) → Set where
      TMAHole : unknown ▸ unknown -→ unknown
      TMAArr  : {τ₁ τ₂ : Typ} → τ₁ -→ τ₂ ▸ τ₁ -→ τ₂

    -- no matched
    _!▸-→ : Typ → Set
    τ !▸-→ = ¬ (∃[ τ₁ ] ∃[ τ₂ ] τ ▸ τ₁ -→ τ₂)

    -- decidable matched arrow
    _▸-→? : (τ : Typ) → Dec (∃[ τ₁ ] ∃[ τ₂ ] τ ▸ τ₁ -→ τ₂)
    num        ▸-→? = no (λ ())
    bool       ▸-→? = no (λ ())
    unknown    ▸-→? = yes ⟨ unknown , ⟨ unknown , TMAHole ⟩ ⟩
    (τ₁ -→ τ₂) ▸-→? = yes ⟨ τ₁      , ⟨ τ₂      , TMAArr  ⟩ ⟩
    (τ₁ -× τ₂) ▸-→? = no (λ ())

    -- matched arrow derivation equality
    ▸-→-≡ : ∀ {τ τ₁ τ₂} → (τ▸ : τ ▸ τ₁ -→ τ₂) → (τ▸′ : τ ▸ τ₁ -→ τ₂) → τ▸ ≡ τ▸′
    ▸-→-≡ TMAHole TMAHole = refl
    ▸-→-≡ TMAArr  TMAArr  = refl

    -- matched arrow unicity
    ▸-→-unicity : ∀ {τ τ₁ τ₂ τ₃ τ₄} → (τ ▸ τ₁ -→ τ₂) → (τ ▸ τ₃ -→ τ₄) → τ₁ -→ τ₂ ≡ τ₃ -→ τ₄
    ▸-→-unicity TMAHole TMAHole = refl
    ▸-→-unicity TMAArr  TMAArr  = refl

    -- no matched arrow derivation equality
    !▸-→-≡ : ∀ {τ} → (τ!▸ : τ !▸-→) → (τ!▸′ : τ !▸-→) → τ!▸ ≡ τ!▸′
    !▸-→-≡ τ!▸ τ!▸′ = ¬-≡ τ!▸ τ!▸′

    -- only consistent types arrow match
    ▸-→→~ : ∀ {τ τ₁ τ₂} → τ ▸ τ₁ -→ τ₂ → τ ~ τ₁ -→ τ₂
    ▸-→→~ TMAHole = TCUnknownArr
    ▸-→→~ TMAArr  = ~-refl

    ▸-→-~̸₁ : ∀ {τ τ₁ τ₂ τ₁′} → τ ▸ τ₁ -→ τ₂ → τ₁′ ~̸ τ₁ → τ ~̸ τ₁′ -→ τ₂
    ▸-→-~̸₁ TMAArr  τ₁′~̸τ₁ (TCArr τ₁~τ₁′ _) = τ₁′~̸τ₁ (~-sym τ₁~τ₁′)
    ▸-→-~̸₁ TMAHole τ₁′~̸τ₁ TCUnknownArr     = τ₁′~̸τ₁ ~-unknown₂

    ▸-→-~̸₂ : ∀ {τ τ₁ τ₂ τ₂′} → τ ▸ τ₁ -→ τ₂ → τ₂′ ~̸ τ₂ → τ ~̸ τ₁ -→ τ₂′
    ▸-→-~̸₂ TMAHole τ₂′~̸τ₂ TCUnknownArr     = τ₂′~̸τ₂ ~-unknown₂
    ▸-→-~̸₂ TMAArr  τ₂′~̸τ₂ (TCArr _ τ₂~τ₂′) = τ₂′~̸τ₂ (~-sym τ₂~τ₂′)

  module join where
    open base
    open equality
    open consistency

    -- lub join
    data _⊔_⇒_ : (τ₁ τ₂ τ : Typ) → Set where
      TJBase        : {τ : Typ} → (b : τ base) → τ ⊔ τ ⇒ τ
      TJUnknown     : unknown ⊔ unknown ⇒ unknown
      TJUnknownBase : {τ : Typ} → (b : τ base) → unknown ⊔ τ ⇒ unknown
      TJBaseUnknown : {τ : Typ} → (b : τ base) → τ ⊔ unknown ⇒ unknown
      TJArr         : {τ₁ τ₂ τ₁′ τ₂′ τ₁″ τ₂″ : Typ}
                     → (τ₁⊔τ₁′ : τ₁ ⊔ τ₁′ ⇒ τ₁″)
                     → (τ₂⊔τ₂′ : τ₂ ⊔ τ₂′ ⇒ τ₂″)
                     → τ₁ -→ τ₂ ⊔ τ₁′ -→ τ₂′ ⇒ τ₁″ -→ τ₂″
      TJUnknownArr  : {τ₁ τ₂ : Typ}
                     → unknown ⊔ τ₁ -→ τ₂ ⇒ unknown
      TJArrUnknown  : {τ₁ τ₂ : Typ}
                     → τ₁ -→ τ₂ ⊔ unknown ⇒ unknown
      TJProd        : {τ₁ τ₂ τ₁′ τ₂′ τ₁″ τ₂″ : Typ}
                     → (τ₁⊔τ₁′ : τ₁ ⊔ τ₁′ ⇒ τ₁″)
                     → (τ₂⊔τ₂′ : τ₂ ⊔ τ₂′ ⇒ τ₂″)
                     → τ₁ -× τ₂ ⊔ τ₁′ -× τ₂′ ⇒ τ₁″ -× τ₂″
      TJUnknownProd : {τ₁ τ₂ : Typ}
                     → unknown ⊔ τ₁ -× τ₂ ⇒ unknown
      TJProdUnknown : {τ₁ τ₂ : Typ}
                     → τ₁ -× τ₂ ⊔ unknown ⇒ unknown

    -- decidable join
    _⊔?_ : (τ₁ : Typ) → (τ₂ : Typ) → Dec (∃[ τ ] τ₁ ⊔ τ₂ ⇒ τ)
    num        ⊔? num          = yes ⟨ num , TJBase BNum ⟩
    num        ⊔? bool         = no λ()
    num        ⊔? unknown      = yes ⟨ unknown , TJBaseUnknown BNum ⟩
    num        ⊔? (_ -→ _)     = no λ()
    num        ⊔? (_ -× _)     = no λ()
    bool       ⊔? num          = no λ()
    bool       ⊔? bool         = yes ⟨ bool , TJBase BBool ⟩
    bool       ⊔? unknown      = yes ⟨ unknown , TJBaseUnknown BBool ⟩
    bool       ⊔? (_ -→ _)     = no λ()
    bool       ⊔? (_ -× _)     = no λ()
    unknown    ⊔? num          = yes ⟨ unknown , TJUnknownBase BNum ⟩
    unknown    ⊔? bool         = yes ⟨ unknown , TJUnknownBase BBool ⟩
    unknown    ⊔? unknown      = yes ⟨ unknown , TJUnknown ⟩
    unknown    ⊔? (_ -→ _)     = yes ⟨ unknown , TJUnknownArr ⟩
    unknown    ⊔? (_ -× _)     = yes ⟨ unknown , TJUnknownProd ⟩
    (τ₁ -→ τ₂) ⊔? num          = no λ()
    (τ₁ -→ τ₂) ⊔? bool         = no λ()
    (τ₁ -→ τ₂) ⊔? unknown      = yes ⟨ unknown , TJArrUnknown ⟩
    (τ₁ -→ τ₂) ⊔? (τ₁′ -→ τ₂′)
      with τ₁ ⊔? τ₁′          | τ₂ ⊔? τ₂′
    ...  | yes ⟨ τ , τ₁⊔τ₁′ ⟩ | yes ⟨ τ′ , τ₂⊔τ₂′′ ⟩ = yes ⟨ τ -→ τ′ , TJArr τ₁⊔τ₁′ τ₂⊔τ₂′′ ⟩
    ...  | _                  | no ¬τ₂⊔τ₂′           = no λ { ⟨ .(_ -→ _) , TJArr {τ₂″ = τ₂″} τ₁⊔τ₁′″ τ₂⊔τ₂′″ ⟩ → ¬τ₂⊔τ₂′ ⟨ τ₂″ , τ₂⊔τ₂′″ ⟩ }
    ...  | no ¬τ₁⊔τ₁′         | _                    = no λ { ⟨ .(_ -→ _) , TJArr {τ₁″ = τ₁″} τ₁⊔τ₁′″ τ₂⊔τ₂′″ ⟩ → ¬τ₁⊔τ₁′ ⟨ τ₁″ , τ₁⊔τ₁′″ ⟩ }
    (τ₁ -→ τ₂) ⊔? (τ₁′ -× τ₂′) = no λ()
    (τ₁ -× τ₂) ⊔? num          = no λ()
    (τ₁ -× τ₂) ⊔? bool         = no λ()
    (τ₁ -× τ₂) ⊔? unknown      = yes ⟨ unknown , TJProdUnknown ⟩
    (τ₁ -× τ₂) ⊔? (τ₁′ -→ τ₂′) = no λ()
    (τ₁ -× τ₂) ⊔? (τ₁′ -× τ₂′)
      with τ₁ ⊔? τ₁′          | τ₂ ⊔? τ₂′
    ...  | yes ⟨ τ , τ₁⊔τ₁′ ⟩ | yes ⟨ τ′ , τ₂⊔τ₂′′ ⟩ = yes ⟨ τ -× τ′ , TJProd τ₁⊔τ₁′ τ₂⊔τ₂′′ ⟩
    ...  | _                  | no ¬τ₂⊔τ₂′           = no λ { ⟨ .(_ -× _) , TJProd {τ₂″ = τ₂″} τ₁⊔τ₁′″ τ₂⊔τ₂′″ ⟩ → ¬τ₂⊔τ₂′ ⟨ τ₂″ , τ₂⊔τ₂′″ ⟩ }
    ...  | no ¬τ₁⊔τ₁′         | _                    = no λ { ⟨ .(_ -× _) , TJProd {τ₁″ = τ₁″} τ₁⊔τ₁′″ τ₂⊔τ₂′″ ⟩ → ¬τ₁⊔τ₁′ ⟨ τ₁″ , τ₁⊔τ₁′″ ⟩ }

    -- join of same type
    ⊔-refl : ∀ {τ} → τ ⊔ τ ⇒ τ
    ⊔-refl {num}     = TJBase BNum
    ⊔-refl {bool}    = TJBase BBool
    ⊔-refl {unknown} = TJUnknown
    ⊔-refl {τ₁ -→ τ₂}
      with τ₁⊔τ₁ ← ⊔-refl {τ₁} | τ₂⊔τ₂ ← ⊔-refl {τ₂} = TJArr τ₁⊔τ₁ τ₂⊔τ₂
    ⊔-refl {τ₁ -× τ₂}
      with τ₁⊔τ₁ ← ⊔-refl {τ₁} | τ₂⊔τ₂ ← ⊔-refl {τ₂} = TJProd τ₁⊔τ₁ τ₂⊔τ₂

    -- join is symmetric
    ⊔-sym : ∀ {τ₁ τ₂ τ} → τ₁ ⊔ τ₂ ⇒ τ → τ₂ ⊔ τ₁ ⇒ τ
    ⊔-sym (TJBase b)           = TJBase b
    ⊔-sym TJUnknown            = TJUnknown
    ⊔-sym (TJUnknownBase b)    = TJBaseUnknown b
    ⊔-sym (TJBaseUnknown b)    = TJUnknownBase b
    ⊔-sym TJUnknownArr         = TJArrUnknown
    ⊔-sym TJArrUnknown         = TJUnknownArr
    ⊔-sym (TJArr ⊔⇒τ₁″ ⊔⇒τ₂″)  = TJArr (⊔-sym ⊔⇒τ₁″) (⊔-sym ⊔⇒τ₂″)
    ⊔-sym TJUnknownProd        = TJProdUnknown
    ⊔-sym TJProdUnknown        = TJUnknownProd
    ⊔-sym (TJProd ⊔⇒τ₁″ ⊔⇒τ₂″) = TJProd (⊔-sym ⊔⇒τ₁″) (⊔-sym ⊔⇒τ₂″)

    -- join with unknown
    ⊔-unknown₁ : ∀ {τ} → unknown ⊔ τ ⇒ unknown
    ⊔-unknown₁ {num}     = TJUnknownBase BNum
    ⊔-unknown₁ {bool}    = TJUnknownBase BBool
    ⊔-unknown₁ {unknown} = TJUnknown
    ⊔-unknown₁ {_ -→ _}  = TJUnknownArr
    ⊔-unknown₁ {_ -× _}  = TJUnknownProd

    ⊔-unknown₂ : ∀ {τ} → τ ⊔ unknown ⇒ unknown
    ⊔-unknown₂ {num}     = TJBaseUnknown BNum
    ⊔-unknown₂ {bool}    = TJBaseUnknown BBool
    ⊔-unknown₂ {unknown} = TJUnknown
    ⊔-unknown₂ {_ -→ _}  = TJArrUnknown
    ⊔-unknown₂ {_ -× _}  = TJProdUnknown

    -- join unicity
    ⊔-unicity : ∀ {τ₁ τ₂ τ τ′} → τ₁ ⊔ τ₂ ⇒ τ → τ₁ ⊔ τ₂ ⇒ τ′ → τ ≡ τ′ 
    ⊔-unicity (TJBase _)            (TJBase _)                = refl
    ⊔-unicity TJUnknown             TJUnknown                 = refl
    ⊔-unicity (TJUnknownBase _)     (TJUnknownBase _)         = refl
    ⊔-unicity (TJBaseUnknown _)     (TJBaseUnknown _)         = refl
    ⊔-unicity TJUnknownArr          TJUnknownArr              = refl
    ⊔-unicity TJArrUnknown          TJArrUnknown              = refl
    ⊔-unicity (TJArr _ _)           (TJBase ())
    ⊔-unicity (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) (TJArr τ₁⊔τ₁′′ τ₂⊔τ₂′′)   = -→-≡ (⊔-unicity τ₁⊔τ₁′ τ₁⊔τ₁′′) (⊔-unicity τ₂⊔τ₂′ τ₂⊔τ₂′′)
    ⊔-unicity TJUnknownProd          TJUnknownProd            = refl
    ⊔-unicity TJProdUnknown          TJProdUnknown            = refl
    ⊔-unicity (TJProd _ _)           (TJBase ())
    ⊔-unicity (TJProd τ₁⊔τ₁′ τ₂⊔τ₂′) (TJProd τ₁⊔τ₁′′ τ₂⊔τ₂′′) = -×-≡ (⊔-unicity τ₁⊔τ₁′ τ₁⊔τ₁′′) (⊔-unicity τ₂⊔τ₂′ τ₂⊔τ₂′′)

    -- join derivation equality
    ⊔-≡ : ∀ {τ₁ τ₂ τ} → (τ₁⊔τ₂ : τ₁ ⊔ τ₂ ⇒ τ) → (τ₁⊔τ₂′ : τ₁ ⊔ τ₂ ⇒ τ) → τ₁⊔τ₂ ≡ τ₁⊔τ₂′
    ⊔-≡ (TJBase b) (TJBase b′) 
      rewrite base-≡ b b′           = refl
    ⊔-≡ TJUnknown TJUnknown         = refl
    ⊔-≡ (TJUnknownBase b) (TJUnknownBase b′)
      rewrite base-≡ b b′           = refl
    ⊔-≡ (TJBaseUnknown b) (TJBaseUnknown b′)
      rewrite base-≡ b b′           = refl
    ⊔-≡ (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′) (TJArr τ₁⊔τ₁′′ τ₂⊔τ₂′′)
      rewrite ⊔-≡ τ₁⊔τ₁′ τ₁⊔τ₁′′
            | ⊔-≡ τ₂⊔τ₂′ τ₂⊔τ₂′′    = refl
    ⊔-≡ TJUnknownArr TJUnknownArr   = refl
    ⊔-≡ TJArrUnknown TJArrUnknown   = refl
    ⊔-≡ (TJProd τ₁⊔τ₁′ τ₂⊔τ₂′) (TJProd τ₁⊔τ₁′′ τ₂⊔τ₂′′)
      rewrite ⊔-≡ τ₁⊔τ₁′ τ₁⊔τ₁′′
            | ⊔-≡ τ₂⊔τ₂′ τ₂⊔τ₂′′    = refl
    ⊔-≡ TJUnknownProd TJUnknownProd = refl
    ⊔-≡ TJProdUnknown TJProdUnknown = refl

    -- join existence means that types are consistent
    ⊔→~ : ∀ {τ τ₁ τ₂} → τ₁ ⊔ τ₂ ⇒ τ → τ₁ ~ τ₂
    ⊔→~ (TJBase b)             = TCBase b
    ⊔→~ TJUnknown              = TCUnknown
    ⊔→~ (TJUnknownBase b)      = TCUnknownBase b
    ⊔→~ (TJBaseUnknown b)      = TCBaseUnknown b
    ⊔→~ TJUnknownArr           = TCUnknownArr
    ⊔→~ TJArrUnknown           = TCArrUnknown
    ⊔→~ (TJArr τ₁⊔τ₁′ τ₂⊔τ₂′)  = TCArr (⊔→~ τ₁⊔τ₁′) (⊔→~ τ₂⊔τ₂′)
    ⊔→~ TJUnknownProd          = TCUnknownProd
    ⊔→~ TJProdUnknown          = TCProdUnknown
    ⊔→~ (TJProd τ₁⊔τ₁′ τ₂⊔τ₂′) = TCProd (⊔→~ τ₁⊔τ₁′) (⊔→~ τ₂⊔τ₂′)

    -- consistent types have a join
    ~→⊔ : ∀ {τ₁ τ₂} → τ₁ ~ τ₂ → ∃[ τ ] τ₁ ⊔ τ₂ ⇒ τ
    ~→⊔     TCUnknown         = ⟨ unknown , TJUnknown       ⟩
    ~→⊔ {τ} (TCBase b)        = ⟨ τ       , TJBase b        ⟩
    ~→⊔     (TCUnknownBase b) = ⟨ unknown , TJUnknownBase b ⟩
    ~→⊔     (TCBaseUnknown b) = ⟨ unknown , TJBaseUnknown b ⟩
    ~→⊔     TCUnknownArr      = ⟨ unknown , TJUnknownArr    ⟩
    ~→⊔     TCArrUnknown      = ⟨ unknown , TJArrUnknown    ⟩
    ~→⊔     (TCArr τ₁~τ₁′ τ₂~τ₂′)
      with ⟨ τ₁″ , ⊔⇒τ₁″ ⟩ ← ~→⊔ τ₁~τ₁′
         | ⟨ τ₂″ , ⊔⇒τ₂″ ⟩ ← ~→⊔ τ₂~τ₂′ = ⟨ τ₁″ -→ τ₂″ , TJArr ⊔⇒τ₁″ ⊔⇒τ₂″ ⟩
    ~→⊔     TCUnknownProd     = ⟨ unknown , TJUnknownProd    ⟩
    ~→⊔     TCProdUnknown     = ⟨ unknown , TJProdUnknown    ⟩
    ~→⊔     (TCProd τ₁~τ₁′ τ₂~τ₂′)
      with ⟨ τ₁″ , ⊔⇒τ₁″ ⟩ ← ~→⊔ τ₁~τ₁′
         | ⟨ τ₂″ , ⊔⇒τ₂″ ⟩ ← ~→⊔ τ₂~τ₂′ = ⟨ τ₁″ -× τ₂″ , TJProd ⊔⇒τ₁″ ⊔⇒τ₂″ ⟩

    -- join nonexistence means types are inconsistent
    ¬⊔→~̸ : ∀ {τ₁ τ₂} → ¬ (∃[ τ ] τ₁ ⊔ τ₂ ⇒ τ) → τ₁ ~̸ τ₂
    ¬⊔→~̸ ¬τ₁⊔τ₂ = λ { τ₁~τ₂ → ¬τ₁⊔τ₂ (~→⊔ τ₁~τ₂) }

    -- inconsistent types have no join
    ~̸→¬⊔ : ∀ {τ₁ τ₂} → τ₁ ~̸ τ₂ → ¬ (∃[ τ ] τ₁ ⊔ τ₂ ⇒ τ)
    ~̸→¬⊔ τ₁~̸τ₂ = λ { ⟨ τ , τ₁⊔τ₂ ⟩ → τ₁~̸τ₂ (⊔→~ τ₁⊔τ₂) }

  open equality public
  open base public
  open consistency public
  open matched public
  open join public
