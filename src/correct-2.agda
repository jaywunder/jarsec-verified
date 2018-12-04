module correct-2 where
open import cfg
open import jarsec using (Parser ; run-parser ; partial-parse ; _>>=_ ; _>>_ ; _<*>_)

open import Data.Bool
open import Data.List hiding (lookup)
-- open import Data.Vec renaming ([_] to V[_] ; _++_ to _vv_) hiding (_>>=_)
open import Data.Fin hiding (_+_)
open import Data.Char
open import Agda.Builtin.Char renaming ( primCharEquality to charEq )
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Unary
open import Data.Maybe hiding (Any ; All)
open import Data.Sum hiding (map)
open import Data.String hiding (length ; _++_) renaming (primStringToList to 𝕊→𝕃 ; primStringFromList to 𝕃→𝕊)
open import Data.Product hiding (map)
open import Agda.Builtin.Unit
-- open import Data.List.Any
open import Data.List.All

postulate
  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  head-from-≡ : ∀ {A : Set} {x y : A} {xs ys : List A} → (x List.∷ xs) ≡ (y ∷ ys) → x ≡ y
  tail-from-≡ : ∀ {A : Set} {x y : A} {xs ys : List A} → (x List.∷ xs) ≡ (y ∷ ys) → xs ≡ ys

  charEq-T : ∀ x c → (charEq x c) ≡ true → x ≡ c
  charEq-F : ∀ x c → (charEq x c) ≡ false → x ≢ c


all++ : ∀ {p} {A : Set} {P : Pred A p} {xs ys : List A} → All P xs → All P ys → All P (xs ++ ys)
all++ [] [] = []
all++ [] (py ∷ all₂) = py ∷ (all++ [] all₂)
all++ (px ∷ all₁) all₂ = px ∷ (all++ all₁ all₂)

-- all++ : ∀ {p} {A : Set} {P : Pred A p} (xs ys : List A) → All P xs → All P ys → All P (xs ++ ys)
-- all++ [] [] [] [] = []
-- all++ [] (y ∷ ys) [] (py ∷ all₂) = py ∷ all++ [] ys [] all₂
-- all++ (x ∷ xs) ys (px ∷ all₁) all₂ = px ∷ (all++ xs ys all₁ all₂)

weaken-to-alt : ∀ {r} {cfg₁ cfg₂ : Cfg 0} → ( r ∈[ cfg₁ ] ) ⊎ ( r ∈[ cfg₂ ] ) → r ∈[ alt cfg₁ cfg₂ ]
weaken-to-alt (inj₁ e) = alt₁ e
weaken-to-alt (inj₂ e) = alt₂ e

correct : let Result = List Char × List Char in
  ∀ (cfg : Cfg 0) (cs : List Char)
  → let rs = jarsec.parse (interp cfg) cs in
    All (λ r → ((proj₁ r) ∈[ cfg ]) × (proj₁ r) ++ (proj₂ r) ≡ cs) rs

correct emp cs = []
correct eps cs = (eps , refl) ∷ []
correct (lit x) [] = []
correct (lit x) (c ∷ cs) with charEq x c | charEq-T x c | charEq-F x c
... | true | b | d rewrite b refl = (lit c , refl) ∷ []
... | false | b | d = []
correct (var ()) cs
correct (seq cfg₁ cfg₂) cs with (Parser.parse (interp cfg₁ >>= (λ x → interp cfg₂ >>= (λ y → Parser.mk-parser (λ str → (x ++ y , str) ∷ [])))) cs)
... | rs = {! (correct cfg₁ cs)  !}

correct (alt cfg₁ cfg₂) cs with (Parser.parse (interp (seq cfg₁ cfg₂)) cs)
... | rs =
  let all₁ = correct cfg₁ cs
      all₂ = correct cfg₂ cs

      weak-all₁ : All (λ r → proj₁ r ∈[ alt cfg₁ cfg₂ ] × proj₁ r ++ proj₂ r ≡ cs) (Parser.parse (interp cfg₁) cs)
      weak-all₁ = Data.List.All.map
        (λ r → ((weaken-to-alt {cfg₁ = cfg₁} {cfg₂ = cfg₂} (inj₁ (proj₁ r))) , (proj₂ r)))
        all₁

      weak-all₂ : All (λ r → proj₁ r ∈[ alt cfg₁ cfg₂ ] × proj₁ r ++ proj₂ r ≡ cs) (Parser.parse (interp cfg₂) cs)
      weak-all₂ = Data.List.All.map
        (λ r → (weaken-to-alt {cfg₁ = cfg₁} {cfg₂ = cfg₂} (inj₂ (proj₁ r))) , (proj₂ r))
        all₂
        
  in all++ weak-all₁ weak-all₂

correct (many cfg) cs = {!   !}
correct (fix cfg) cs = {! correct (fix cfg) cs  !}
















-- correct (alt cfg₁ cfg₂) cs with (Parser.parse (jarsec.combine (interp cfg₁) (interp cfg₂)) cs)
-- ... | rs =
--   let all₁ = correct cfg₁ cs
--       all₂ = correct cfg₂ cs
--   in {! Data.List.All.map ? all₁  !}
--   where
--   rinduction : List (List Char × List Char) → _
--   rinduction [] = []
--   rinduction (r ∷ rs) =
--     let all₁ = correct cfg₁ cs
--         all₂ = correct cfg₂ cs
--     in Data.List.All.lookup all₁ {!    !}
-- -- correct (alt cfg₁ cfg₂) cs | [] = let all₁ = correct cfg₁ cs ; all₂ = correct cfg₂ cs in []
-- -- correct (alt cfg₁ cfg₂) cs | r ∷ rs =
-- --   let all₁ = correct cfg₁ cs
-- --       all₂ = correct cfg₂ cs
-- --   in ({! Data.List.All.lookup  !} , {!   !}) ∷ {! correct (alt cfg₁ cfg₂) cs  !}
