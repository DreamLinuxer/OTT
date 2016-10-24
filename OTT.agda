module OTT where

data Empty : Set where

record Unit : Set where

data Bool : Set where
  tt : Bool
  ff : Bool

Π : (S : Set) (T : S → Set) → Set
Π S T = (x : S) → T x

record Σ (S : Set) (T : S → Set) : Set where
  field
    fst : S
    snd : T fst

data W (S : Set) (T : S → Set) : Set where
  _◃_ : (x : S) → (T x → W S T) → W S T

mutual
  data set : Set where
    𝟘 : set
    𝟙 : set
    𝟚 : set
    Π' : (S : set) → (⟦ S ⟧ → set) → set
    Σ' : (S : set) → (⟦ S ⟧ → set) → set
    W' : (S : set) → (⟦ S ⟧ → set) → set

  ⟦_⟧ : set → Set
  ⟦ 𝟘 ⟧ = Empty
  ⟦ 𝟙 ⟧ = Unit
  ⟦ 𝟚 ⟧ = Bool
  ⟦ Π' S T ⟧ = (x : ⟦ S ⟧) → ⟦ T x ⟧
  ⟦ Σ' S T ⟧ = Σ ⟦ S ⟧ (λ x → ⟦ T x ⟧)
  ⟦ W' S T ⟧ = W ⟦ S ⟧ (λ x → ⟦ T x ⟧)

infixr 20 _⟶_
_⟶_ : set → set → set
S ⟶ T = Π' S (λ _ → T)

infixr 20 _,_
_,_ : set → set → set
S , T = Σ' S (λ _ → T)

_!_ : Empty → (P : Set) → P
() ! P

If_Then_Else_ : (b : Bool) → set → set → set
If tt Then T Else F = T
If ff Then T Else F = F

if_/_then_else_ : (b : Bool) (P : Bool → set) → ⟦ P tt ⟧ → ⟦ P ff ⟧ → ⟦ P b ⟧
if tt / P then t else f = t
if ff / P then t else f = f

rec_/_w_ : {S : Set} {T : S → Set} (x : W S T) (P : W S T → set)
            → ((s : S) (f : T s → W S T) → ((t : T s) → ⟦ P (f t) ⟧) → ⟦ P (s ◃ f) ⟧)
            → ⟦ P x ⟧
rec s ◃ f / P w p = p s f (λ t → rec f t / P w p)

Tr : (b : Bool) → set
Tr b = If b Then 𝟙 Else 𝟘

Nat : set
Nat = W' 𝟚 Tr

zero : ⟦ Nat ⟧
zero = ff ◃ (λ z → z ! ⟦ Nat ⟧)

suc : ⟦ Nat ⟧ → ⟦ Nat ⟧
suc n = tt ◃ (λ _ → n)

one : ⟦ Nat ⟧
one = suc zero

plus : ⟦ Nat ⟧ → ⟦ Nat ⟧ → ⟦ Nat ⟧
plus x y = rec x / (λ _ → Nat) w
               (λ b → if b / (λ b → ((Tr b) ⟶ Nat)
                                  ⟶ ((Tr b) ⟶ Nat)
                                  ⟶ Nat)
                      then (λ f h → suc (h (record {})))
                      else (λ f h → y))

Branch : (b : Bool) → set
Branch b = If b Then 𝟚 Else 𝟘

Tree : set
Tree = W' 𝟚 Branch

leaf : ⟦ Tree ⟧
leaf = ff ◃ (λ z → z ! ⟦ Tree ⟧)

node : ⟦ Tree ⟧ → ⟦ Tree ⟧ → ⟦ Tree ⟧
node l r = tt ◃ (λ {tt → l ; ff → r})

count : ⟦ Tree ⟧ → ⟦ Nat ⟧
count t = rec t / (λ _ → Nat) w
              (λ b → if b / (λ b → ((Branch b) ⟶ Tree)
                                ⟶ ((Branch b) ⟶ Nat)
                                ⟶ Nat)
                     then (λ f h → plus (h ff) (h tt))
                     else (λ f h → one))

four : ⟦ Nat ⟧
four = count (node (node leaf leaf) (node leaf leaf))

mutual
  data prop : Set where
    ⊥ : prop
    ⊤ : prop
    _∧_ : prop → prop → prop
    Π_·_ : (S : set) → (⟦ S ⟧ → prop) → prop

  ⌈_⌉ : prop → set
  ⌈ ⊥ ⌉ = 𝟘
  ⌈ ⊤ ⌉ = 𝟙
  ⌈ P ∧ Q ⌉ = ⌈ P ⌉ , ⌈ Q ⌉
  ⌈ Π S · P ⌉ = Π' S (λ s → ⌈ P s ⌉)

_⇒_ : prop → prop → prop
P ⇒ Q = Π ⌈ P ⌉ · (λ _ → Q)

mutual
  _==_ : set → set → prop
  𝟘 == 𝟘 = ⊤
  𝟙 == 𝟙 = ⊤
  𝟚 == 𝟚 = ⊤
  Π' S₀ T₀ == Π' S₁ T₁ = (S₁ == S₀) ∧ (Π S₁ · (λ x₁ → Π S₀ · (λ x₀ → (x₁ ∶ S₁ == x₀ ∶ S₀) ⇒ (T₀ x₀ == T₁ x₁))))
  Σ' S₀ T₀ == Σ' S₁ T₁ = (S₀ == S₁) ∧ (Π S₀ · (λ x₀ → Π S₁ · (λ x₁ → (x₀ ∶ S₀ == x₁ ∶ S₁) ⇒ (T₀ x₀ == T₁ x₁))))
  W' S₀ T₀ == W' S₁ T₁ = (S₀ == S₁) ∧ (Π S₀ · (λ x₀ → Π S₁ · (λ x₁ → (x₀ ∶ S₀ == x₁ ∶ S₁) ⇒ (T₀ x₀ == T₁ x₁))))
  S == T = ⊥

  eq : (S : set) → ⟦ S ⟧ → (T : set) → ⟦ T ⟧ → prop
  eq 𝟘 s 𝟘 t = ⊤
  eq 𝟙 s 𝟙 t = ⊤
  eq 𝟚 tt 𝟚 tt = ⊤
  eq 𝟚 tt 𝟚 ff = ⊥
  eq 𝟚 ff 𝟚 tt = ⊥
  eq 𝟚 ff 𝟚 ff = ⊤
  eq (Π' S x) s T t = {!!}
  eq (Σ' S x) s T t = {!!}
  eq (W' S x) s T t = {!!}
  eq S s T t = {!!}

  syntax eq S s T t  = s ∶ S == t ∶ T

  coe : {S T : set} → ⟦ S ⟧ → (Q : ⟦ ⌈ S == T ⌉ ⟧) → ⟦ T ⟧
  coe {𝟘} {𝟘} z Q = z
  coe {𝟙} {𝟙} u Q = u
  coe {𝟚} {𝟚} b Q = b
  coe {Π' S₀ T₀} {Π' S₁ T₁} s Q = {!!}
  coe {Σ' S₀ T₀} {Σ' S₁ T₁} s Q = {!!}
  coe {W' S₀ T₀} {W' S₁ T₁} s Q = {!!}
  coe {S} {T} s Q = {!Q ! T!}

  syntax coe s Q = s [ Q ⟩

  ⟨_∥_⟩ : {S T : set} → (s : ⟦ S ⟧) (Q : ⟦ ⌈ S == T ⌉ ⟧) → ⟦ ⌈ s ∶ S == s [ Q ⟩ ∶ T ⌉ ⟧
  ⟨ s ∥ Q ⟩ = {!!}
