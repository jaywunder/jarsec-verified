module jarsec where

open import Algebra
open import Data.Bool
open import Data.Char
-- open import Data.Empty
-- open import Data.Fin
open import Data.List
open import Data.Maybe hiding (map)
open import Data.Nat
open import Data.Nat.Base
open import Data.Nat.Show
-- open import Data.Integer
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.String hiding (length)
open import Function
-- open import Data.Sum
-- open import Data.Unit
-- open import Data.Vec
open import Category.Functor
open import Relation.Binary
open import Data.Char.Base
open import Agda.Builtin.Char
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

record Parser (A : Set) : Set where
  constructor mk-parser
  field
    parse : List Char → (List (A × (List Char)))
open Parser public

item : Parser Char
item = mk-parser λ where
  [] → []
  (c ∷ cs) → (c , cs) ∷ []

bind : ∀ { A B : Set } → Parser A → (A → Parser B) → Parser B
bind {A} p f = mk-parser $ λ cs →
  let rs : List (A × List Char)
      rs = parse p cs
  in concatMap (λ where (x , cs′) → parse (f x) cs′) rs

_>>=_ : ∀ { A B : Set } → Parser A → (A → Parser B) → Parser B
p >>= f = bind p f

_>>_ : ∀ { A B : Set } → Parser A → Parser B → Parser B
pA >> pB = pA >>= λ _ → pB

unit : ∀ { A : Set } → A → Parser A
unit a = mk-parser (λ str → ( a , str ) ∷ [])

unit* : ∀ { A : Set } → List A → Parser A
unit* xs = mk-parser (λ str → foldl (λ sum x → (x , str) ∷ sum) [] xs)

fmap : ∀ { A B : Set } → (A → B) → Parser A → Parser B
fmap f p = do
  a ← p
  unit (f a)

_<$>_ : ∀ { A B : Set } → (A → B) → Parser A → Parser B
f <$> p = fmap f p

_<*>_ : ∀ {A B : Set } → Parser A → Parser B → Parser ( A × B )
aP <*> bP = do
  a ← aP
  b ← bP
  unit (a , b)


combine : { A : Set } → Parser A → Parser A → Parser A
combine p q = mk-parser (λ cs → (parse p cs) Data.List.++ (parse q cs))

failure : { A : Set } → Parser A
failure = mk-parser (λ cs → [])

option : { A : Set } → Parser A → Parser A → Parser A
option p q = mk-parser $ λ where
  cs → case (parse p cs) of λ where
    [] → parse q cs
    result → result


{-# TERMINATING #-}
mutual
  many* : { A : Set } → Parser A → Parser (List A)
  many* v = option (many+ v) (unit [])

  many+ : { A : Set } → Parser A → Parser (List A)
  many+ v = fmap (λ { (a , list) → a ∷ list }) (v <*> (many* v))

satisfy : (Char -> Bool) -> Parser Char
satisfy f = do
  c ← item
  case (f c) of λ where
    true → unit c
    false → failure

oneOf : List Char → Parser Char
oneOf options = satisfy (flip elem options)
  where
  elem : Char → List Char → Bool
  elem a [] = false
  elem a (x ∷ xs) = case primCharEquality a x of λ where
    true → true
    false → elem a xs

module _ { A : Set } where
  {-# TERMINATING #-}
  chainl1 : Parser A → Parser (A → A → A) → Parser A
  chainl1 p op = do
    a ← p
    rest a
    where
      rest : A → Parser A
      rest a = option (do
        f ← op
        b ← p
        rest (f a b)) (unit a)

chainl : { A : Set } → Parser A → Parser (A → A → A) → A → Parser A
chainl p op a = option (chainl1 p op) (unit a)

char : Char → Parser Char
char c = satisfy (primCharEquality c)

digit : Parser Char
digit = satisfy isDigit

-- TODO: Remove
∣_-_∣ : ℕ → ℕ → ℕ
∣ zero  - y     ∣ = y
∣ x     - zero  ∣ = x
∣ suc x - suc y ∣ = ∣ x - y ∣

natural : Parser ℕ
natural = natFromList <$> ((map primCharToNat) <$> (many+ digit))
  where
  natFromList : List ℕ → ℕ
  natFromList [] = zero
  natFromList (n ∷ ns) =
    let len = length ns
    in (∣ n - 48 ∣ + (10 * len)) + (natFromList ns)

string : String → Parser String
string str = primStringFromList <$> (string-chars (primStringToList str))
  where
  string-chars : List Char → Parser (List Char)
  string-chars [] = unit []
  string-chars (c ∷ cs) = do
    char c
    string-chars cs
    unit (c ∷ cs)

spaces : Parser String
spaces = fmap primStringFromList (many* (oneOf (primStringToList " \n\r")))

token : { A : Set } → Parser A → Parser A
token p = do
  a ← p
  spaces
  unit a

reserved : String → Parser String
reserved str = token (string str)

parens : { A : Set } → Parser A → Parser A
parens m = do
  (reserved "(")
  n ← m
  (reserved ")")
  unit n

--------------------------------------------------------------------------------

data Expr : Set where
  Invalid : Expr
  -- Var     : Char → Expr
  Lit : ℕ → Expr
  Add : Expr → Expr → Expr
  Mul : Expr → Expr → Expr
  -- Add Sub : Expr → Expr → Expr
  -- Mul Div : Expr → Expr → Expr

eval : Expr → ℕ
eval Invalid = 0
eval (Lit n) = n
eval (Add a b) = eval a + eval b
eval (Mul a b) = eval a * eval b

eval′ : Maybe Expr → ℕ
eval′ (just x) = eval x
eval′ nothing = 0

module _ where
  {-# TERMINATING #-}
  expr : Parser Expr
  {-# TERMINATING #-}
  term : Parser Expr
  {-# TERMINATING #-}
  factor : Parser Expr

  infixOp : {A : Set} → String → (A → A → A) → Parser (A → A → A)
  mulop : Parser (Expr → Expr → Expr)
  addop : Parser (Expr → Expr → Expr)

  number : Parser Expr

  expr = chainl1 term addop

  term = chainl1 factor mulop

  factor = option number (parens expr)

  infixOp x f = reserved x >> unit f

  mulop = infixOp "*" Mul

  addop = infixOp "+" Add

  number = do
    n ← natural
    unit (Lit n)

runParser : { A : Set } → Parser A → String → Maybe A
runParser p str = case (parse p (primStringToList str)) of λ where
  [] → nothing
  (res ∷ xs) → just (proj₁ res)

partial-parse :  { A : Set } → Parser A → String → Maybe (List (A × List Char))
partial-parse p str with parse p (primStringToList str)
partial-parse p str | [] = nothing
partial-parse p str | xs = just xs

run-parser : { A : Set } → Parser A → String → Maybe (List A)
run-parser p str = case (parse p (primStringToList str)) of λ where
  [] → nothing
  xs → just (foldl (λ sum x → (proj₁ x) ∷ sum) [] xs)

run : String → Maybe Expr
run = runParser expr

do-everything : String → ℕ
do-everything str = eval′ $ run str
