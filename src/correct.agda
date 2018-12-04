module correct where
open import cfg
open import jarsec using (Parser ; parse ; run-parser ; partial-parse ; _>>=_ ; _>>_ ; _<*>_)

open import Data.Bool
open import Data.List hiding (lookup)
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
open import Data.List.All
open import Level

postulate
  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  head-from-≡ : ∀ {A : Set} {x y : A} {xs ys : List A} → (x List.∷ xs) ≡ (y ∷ ys) → x ≡ y
  tail-from-≡ : ∀ {A : Set} {x y : A} {xs ys : List A} → (x List.∷ xs) ≡ (y ∷ ys) → xs ≡ ys

  charEq-T : ∀ x c → (charEq x c) ≡ true → x ≡ c
  charEq-F : ∀ x c → (charEq x c) ≡ false → x ≢ c

correct : ∀ (cfg : Cfg 0) (cs : List Char)
  → let rs = jarsec.parse (interp cfg) cs in
    All (λ r → ((proj₁ r) ∈[ cfg ]) × (proj₁ r) ++ (proj₂ r) ≡ cs) rs

correct emp cs = []
correct eps cs = (eps , refl) ∷ []
correct (lit x) [] = []
correct (lit x) (c ∷ cs) with charEq x c | charEq-T x c | charEq-F x c
... | true | b | d rewrite b refl = (lit c , refl) ∷ []
... | false | b | d = []
correct (var ()) cs
correct (seq cfg₁ cfg₂) cs =
  let all₁ = correct cfg₁ cs
      -- HAVE: All (λ r → (proj₁ r ∈[ cfg₁ ]) × proj₁ r ++ proj₂ r ≡ cs)
      --   (Parser.parse (interp cfg₁) cs)
      all₂ = correct cfg₂
  in {!   !}
  -- GOAL: All
  --   (λ r → (proj₁ r ∈[ seq cfg₁ cfg₂ ]) × proj₁ r ++ proj₂ r ≡ cs)
  --   (Parser.parse
  --    (interp cfg₁ >>=
  --     (λ x →
  --        interp cfg₂ >>=
  --        (λ y → Parser.mk-parser (λ str → (x ++ y , str) ∷ []))))
  --    cs)
  where
    -- all>>= :
    --   let L = List Char
    --       P : Pred (L × L) Level.zero
    --       P = (λ r → (proj₁ r ∈[ cfg₁ ]) × proj₁ r ++ proj₂ r ≡ cs)
    --       Q : Pred (L × L) Level.zero
    --       Q = (λ r → (proj₁ r ∈[ seq cfg₁ cfg₂ ]) × proj₁ r ++ proj₂ r ≡ cs)
    --   in ∀ {cs}
    --   → (p₁ p₂ : Parser L)
    --   → All P (jarsec.parse p₁ cs)
    --   → (λ cs′ → All P (jarsec.parse p₂ cs′))
    --   → All Q
    --     (Parser.parse
    --       (p₁ >>= (λ x →
    --         p₂ >>= (λ y →
    --           Parser.mk-parser (λ str → (x ++ y , str) ∷ []))))
    --       cs)
    -- all>>= p₁ p₂ e₁ e₂ with (Parser.parse
    --                           (p₁ >>= (λ x →
    --                             p₂ >>= (λ y →
    --                               Parser.mk-parser (λ str → (x ++ y , str) ∷ []))))
    --                           cs)
    -- all>>= p₁ p₂ e₁ e₂ | [] = {! []  !}
    -- all>>= p₁ p₂ e₁ e₂ | r ∷ rs = {!   !}

    strengthen-to-seq :
      let L = List Char
          -- P₁ : Pred (L × L) Level.zero
          -- P₁ = (λ r → ((proj₁ r) ∈[ cfg₁ ]) × proj₁ r ++ proj₂ r ≡ cs)
          -- P₂ : Pred (L × L) Level.zero
          -- P₂ = (λ r → ((proj₁ r) ∈[ cfg₂ ]) × proj₁ r ++ proj₂ r ≡ cs)
          Q : Pred (L × L) Level.zero
          Q = (λ r → ((proj₁ r) ∈[ seq cfg₁ cfg₂ ]) × proj₁ r ++ proj₂ r ≡ cs)
      in All Q (Parser.parse
        ((interp cfg₁) >>= (λ x →
          (interp cfg₂) >>= (λ y →
            Parser.mk-parser (λ str → (x ++ y , str) ∷ []))))
        cs)
    strengthen-to-seq with parse (interp cfg₁) cs | correct cfg₁ cs
    strengthen-to-seq | [] | [] = []
    strengthen-to-seq | r₁ ∷ rs₁  | a₁ ∷ all₁ with parse (interp cfg₁) (proj₂ r₁) | correct cfg₂ (proj₂ r₁)
    strengthen-to-seq | r₁ ∷ rs₁  | a₁ ∷ all₁ | rs₂ | all₂
      = {! all₂  !}
    -- strengthen-to-seq | r₁ ∷ rs₁  | a₁ ∷ all₁ | [] | []
    --   = {! all₁  !}
    -- strengthen-to-seq | r₁ ∷ rs₁  | a₁ ∷ all₁ | r₂ ∷ rs₂  | a₂ ∷ all₂
    --   = {! all₁  !}
      -- GOAL : All
        -- (λ r → proj₁ r ∈[ seq cfg₁ cfg₂ ] × proj₁ r ++ proj₂ r ≡ cs)
        -- (foldr _++_ []
        --  (Data.List.map (λ x → (proj₁ r₁ ++ proj₁ x , proj₂ x) ∷ [])
        --   (Parser.parse (interp cfg₂) (proj₂ r₁)))
        --  ++
        --  foldr _++_ []
        --  (Data.List.map
        --   (λ x →
        --      foldr _++_ []
        --      (Data.List.map (λ x₁ → (proj₁ x ++ proj₁ x₁ , proj₂ x₁) ∷ [])
        --       (Parser.parse (interp cfg₂) (proj₂ x))))
        --   rs₁))

    -- GIVEN >>= >>= ++ shape, return a seq cfg₁ cfg₂

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

  where
    all++ : ∀ {p} {A : Set} {P : Pred A p} {xs ys : List A}
      → All P xs → All P ys → All P (xs ++ ys)
    all++ [] [] = []
    all++ [] (py ∷ all₂) = py ∷ (all++ [] all₂)
    all++ (px ∷ all₁) all₂ = px ∷ (all++ all₁ all₂)

    weaken-to-alt : ∀ {r} {cfg₁ cfg₂ : Cfg 0}
      → (r ∈[ cfg₁ ]) ⊎ (r ∈[ cfg₂ ]) → r ∈[ alt cfg₁ cfg₂ ]
    weaken-to-alt (inj₁ e) = alt₁ e
    weaken-to-alt (inj₂ e) = alt₂ e

correct (many cfg) cs = {!   !} -- rewrite unblock
correct (fix cfg) cs = {!   !}
















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
