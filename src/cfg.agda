module cfg where

open import jarsec using (Parser ; run-parser ; partial-parse ; _>>=_ ; _>>_ ; _<*>_)

open import Data.Bool
open import Data.List hiding (lookup)
open import Data.Vec renaming ([_] to V[_] ; _++_ to _vv_) hiding (_>>=_)
open import Data.Fin hiding (_+_)
open import Data.Char
open import Agda.Builtin.Char renaming ( primCharEquality to charEq )
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Maybe
open import Data.Sum hiding (map)
open import Data.String hiding (length ; _++_) renaming (primStringToList to 𝕊→𝕃 ; primStringFromList to 𝕃→𝕊)
open import Data.Product hiding (map)
open import Agda.Builtin.Unit

postulate
  𝕃⇄𝕊 : ∀ (cs : List Char) → (𝕊→𝕃 (𝕃→𝕊 cs)) ≡ cs

_at_ : ∀ {n} {A : Set} → Vec A n → Fin n → A
(x ∷ xs) at zero = x
(x ∷ xs) at suc i = xs at i

A : Set
A = Char

data Cfg : ℕ → Set where
  emp : ∀ {n} → Cfg n
  eps : ∀ {n} → Cfg n
  lit : ∀ {n} → A → Cfg n
  var : ∀ {n} → Fin n → Cfg n
  seq : ∀ {n} → Cfg n → Cfg n → Cfg n
  alt : ∀ {n} → Cfg n → Cfg n → Cfg n
  many : ∀ {n} → Cfg n → Cfg n
  fix : ∀ {n} → Cfg (suc n) → Cfg n

Env : ℕ → Set
Env n = Vec (Cfg n) n

_⊖_ : ∀ (n : ℕ) → Fin n → ℕ
(suc n) ⊖ zero = n
(suc n) ⊖ suc i = suc (n ⊖ i)

_⊕_ : ℕ → ℕ → ℕ
zero ⊕ n = n
suc m ⊕ n = m ⊕ suc n

introd-var : ∀ {n : ℕ} (i : Fin n) → Fin (n ⊖ i) → Fin n
introd-var zero x = suc x
introd-var (suc i) zero = zero

introd-var (suc i) (suc x) = suc (introd-var i x)

introd : ∀ {n : ℕ} (i : Fin n) → Cfg (n ⊖ i) → Cfg n
introd i emp = emp
introd i eps = eps
introd i (lit l) = lit l
introd i (var x) = var (introd-var i x)
introd i (seq e₁ e₂) = seq (introd i e₁) (introd i e₂)
introd i (alt e₁ e₂) = alt (introd i e₁) (introd i e₂)
introd i (many e) = many (introd i e)
introd i (fix e) = fix (introd (suc i) e)

-- used in subst
introd-var-N : ∀ {n : ℕ} (m : ℕ) → Fin n → Fin (m ⊕ n)
introd-var-N zero x = x
introd-var-N (suc m) x = introd-var-N m (introd-var zero x)

-- used in subst
intro : ∀ {n : ℕ} → Cfg n → Cfg (suc n)
intro = introd zero

subst-var : ∀ {n : ℕ} (m : ℕ) (x : Fin n) → Cfg (m ⊕ (n ⊖ x)) → Fin n → Cfg (m ⊕ (n ⊖ x))
subst-var m zero v zero = v
subst-var m zero v (suc y) = var (introd-var-N m y)
subst-var m (suc x) v zero = var (introd-var-N m zero)
subst-var m (suc x) v (suc y) = subst-var (suc m) x v y

subst : ∀ {n : ℕ} (x : Fin n) → Cfg (n ⊖ x) → Cfg n → Cfg (n ⊖ x)
subst y v emp = emp
subst y v eps = eps
subst y v (lit l) = lit l
subst y v (var x) = subst-var zero y v x
subst y v (seq e₁ e₂) = seq (subst y v e₁) (subst y v e₂)
subst y v (alt e₁ e₂) = alt (subst y v e₁) (subst y v e₂)
subst y v (many e) = many (subst y v e)
subst y v (fix e) = fix (subst (suc y) (intro v) e)

sub : ∀ {n : ℕ} → Cfg n → Cfg (suc n) → Cfg n
sub = subst zero

data _∈[_] : List A → Cfg 0 → Set where
  eps : [] ∈[ eps ]

  lit : ∀ (c : A) → [ c ] ∈[ lit c ]

  seq : ∀ {s₁ s₂ : List A} {cfg₁ cfg₂ : Cfg 0}
    → s₁ ∈[ cfg₁ ]
    → s₂ ∈[ cfg₂ ]
    → (s₁ ++ s₂) ∈[ seq cfg₁ cfg₂ ]

  alt₁ : {s : List A} {cfg₁ cfg₂ : Cfg 0}
    → s ∈[ cfg₁ ]
    → s ∈[ alt cfg₁ cfg₂ ]

  alt₂ : {s : List A} {cfg₁ cfg₂ : Cfg 0}
    → s ∈[ cfg₂ ]
    → s ∈[ alt cfg₁ cfg₂ ]

  many0 : {cfg : Cfg 0}
    → [] ∈[ many cfg ]

  many+ : {s₁ s₂ : List A} {cfg : Cfg 0}
    → s₁ ∈[ cfg ]
    → s₂ ∈[ many cfg ]
    → (s₁ ++ s₂) ∈[ many cfg ]

  unroll : {s : List A}
    → {cfg : Cfg 1}
    → s ∈[ sub (fix cfg) cfg ]
    → s ∈[ fix cfg ]

abstract
  instance
    block : ⊤
    block = tt
  unblock : block ≡ tt
  unblock = refl

delayed : ∀ {A : Set} → ⊤ → A  → A
delayed tt x = x

delay : ∀ {A : Set} → A → A
delay = delayed block


{-# TERMINATING #-}
interp : Cfg 0 → Parser (List A)
interp emp = Parser.mk-parser (λ _ → [])
interp eps = Parser.mk-parser (λ str → [ ([] , str) ])
interp (lit c) = do
  c′ ← jarsec.satisfy (charEq c)
  jarsec.unit [ c′ ]
interp (var ())
interp (seq cfg₁ cfg₂) = do
  x ← (interp cfg₁)
  y ← (interp cfg₂)
  jarsec.unit (x ++ y)
interp (alt cfg₁ cfg₂) = jarsec.combine (interp cfg₁) (interp cfg₂)
interp (many cfg) = interp (alt eps (seq cfg (delay (many cfg))))
interp (fix cfg) = interp (sub (fix cfg) cfg)

a : Fin 2
a = zero
b : Fin 2
b = (suc zero)

xX-or-ε : Cfg 0
xX-or-ε = fix (alt (seq (lit 'x') (var zero)) eps)

-- _ : interp xX-or-ε ≡ {!   !}
-- _ = refl

_ : (𝕊→𝕃 "xx") ∈[ fix {n = 0} (alt (seq (lit 'x') (var zero)) (eps)) ]
_ = unroll (alt₁ (seq (lit 'x') (unroll (alt₁ (seq (lit 'x') (unroll (alt₂ eps)))))))

_ : (𝕊→𝕃 "xx") ∈[ xX-or-ε ]
_ =
  unroll
  (alt₁ (seq (lit 'x') (
    unroll
    (alt₁ (seq (lit 'x') (
      unroll
      (alt₂ eps)))))))

_ : ( 'a' ∷ 'a' ∷ []) ∈[ many (lit 'a') ]
_ = many+ (lit 'a') (many+ (lit 'a') many0)
