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

_⟼_ : set → set → set
S ⟼ T = Π' S (λ _ → T)

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

plus : ⟦ Nat ⟧ → ⟦ Nat ⟧ → ⟦ Nat ⟧
plus x y = rec x / (λ _ → Nat) w
               (λ b → if b / (λ b → Π' (Π' (Tr b) (λ _ → Nat))
                                       (λ _ → Π' (Π' (Tr b) (λ _ → Nat))
                                                 (λ _ → Nat)))
                      then (λ f h → suc (h (record {})))
                      else (λ f h → y))

