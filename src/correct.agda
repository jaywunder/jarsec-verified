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

  ++-runit : ∀ {A : Set} (m : List A) → m ++ [] ≡ m
  ++-assoc : ∀ {A : Set} (m n p : List A) → (m ++ n) ++ p ≡ m ++ (n ++ p)

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
correct (seq cfg₁ cfg₂) cs with (parse (interp cfg₁) cs) | correct cfg₁ cs
correct (seq cfg₁ cfg₂) cs | [] | [] = []
correct (seq cfg₁ cfg₂) cs | r₁ ∷ rs₁ | a₁ ∷ all₁ with parse (interp cfg₂) (proj₂ r₁) | correct cfg₂ (proj₂ r₁)
correct (seq cfg₁ cfg₂) cs | r₁ ∷ rs₁ | a₁ ∷ all₁ | [] | [] = {!   !}
correct (seq cfg₁ cfg₂) cs | r₁ ∷ rs₁ | a₁ ∷ all₁ | r₂ ∷ rs₂ | a₂ ∷ all₂
  = strengthen-to-seq r₁ a₁ r₂ a₂ ∷ correct-seq₁ cfg₁ cfg₂ cs r₁ rs₁ a₁ all₁ rs₂ all₂
  where
  Result : Set
  Result = List Char × List Char
  strengthen-to-seq :
    ∀ (r₁ : Result)
    → (a₁ : proj₁ r₁ ∈[ cfg₁ ] × proj₁ r₁ ++ proj₂ r₁ ≡ cs)
    → (r₂ : Result)
    → (a₂ : proj₁ r₂ ∈[ cfg₂ ] × proj₁ r₂ ++ proj₂ r₂ ≡ proj₂ r₁)
    → (proj₁ r₁ ++ proj₁ r₂) ∈[ seq cfg₁ cfg₂ ] × (proj₁ r₁ ++ proj₁ r₂) ++ proj₂ r₂ ≡ cs
  strengthen-to-seq r₁ a₁ r₂ a₂
    rewrite ++-assoc (proj₁ r₁)  (proj₁ r₂) (proj₂ r₂)
    | proj₂ a₂
    | proj₂ a₁
    = (seq (proj₁ a₁) (proj₁ a₂)) , refl

  correct-seq₂ :
    ∀ (cfg₁ cfg₂ : Cfg 0) (cs : List Char)
    → (r₁ : Result)
    → (rs₁ : List Result)
    → (a₁ : Σ (proj₁ r₁ ∈[ cfg₁ ]) (λ x → proj₁ r₁ ++ proj₂ r₁ ≡ cs))
    → (all₁ : All (λ r → Σ (proj₁ r ∈[ cfg₁ ]) (λ x → proj₁ r ++ proj₂ r ≡ cs)) rs₁)
    → All (λ r → (proj₁ r ∈[ seq cfg₁ cfg₂ ]) × proj₁ r ++ proj₂ r ≡ cs)
      (concatMap
       (λ x →
          concatMap (λ x₁ → (proj₁ x ++ proj₁ x₁ , proj₂ x₁) ∷ [])
          (parse (interp cfg₂) (proj₂ x)))
       rs₁)
  correct-seq₂ cfg₁ cfg₂ cs r₁ [] a₁ [] = []
  correct-seq₂ cfg₁ cfg₂ cs r₁ (x ∷ rs₁) a₁ (px ∷ all₁) = {!   !}

  correct-seq₁ :
    ∀ (cfg₁ cfg₂ : Cfg 0) (cs : List Char)
    → (r₁ : Result)
    → (rs₁ : List Result)
    → (a₁ : Σ (proj₁ r₁ ∈[ cfg₁ ]) (λ x → proj₁ r₁ ++ proj₂ r₁ ≡ cs))
    → (all₁ : All (λ r → Σ (proj₁ r ∈[ cfg₁ ]) (λ x → proj₁ r ++ proj₂ r ≡ cs)) rs₁)
    → (rs₂ : List Result)
    → (all₂ : All (λ r → Σ (proj₁ r ∈[ cfg₂ ]) (λ x → proj₁ r ++ proj₂ r ≡ proj₂ r₁)) rs₂)
    → All (λ r → proj₁ r ∈[ seq cfg₁ cfg₂ ] × proj₁ r ++ proj₂ r ≡ cs)
      (foldr _++_ []
        (Data.List.map (λ x → (proj₁ r₁ ++ proj₁ x , proj₂ x) ∷ []) rs₂)
        ++
        (concatMap (λ x →
          (concatMap (λ x₁ → (proj₁ x ++ proj₁ x₁ , proj₂ x₁) ∷ [])
            (parse (interp cfg₂) (proj₂ x))))
        rs₁))

  correct-seq₁ cfg₁ cfg₂ cs r₁ rs₁ a₁ all₁ [] [] = correct-seq₂ cfg₁ cfg₂ cs r₁ rs₁ a₁ all₁
  correct-seq₁ cfg₁ cfg₂ cs r₁ rs₁ a₁ all₁ (r₂ ∷ rs₂) (a₂ ∷ all₂)
    = ((seq (proj₁ a₁) (proj₁ a₂)) , fact) ∷ correct-seq₁ cfg₁ cfg₂ cs r₁ rs₁ a₁ all₁ rs₂ all₂
      where
      fact : (proj₁ r₁ ++ proj₁ r₂) ++ proj₂ r₂ ≡ cs
      fact rewrite ++-assoc (proj₁ r₁) (proj₁ r₂) (proj₂ r₂)
        | proj₂ a₂
        | proj₂ a₁
        = refl

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

-- correct (fix cfg) cs with (parse (interp (sub (fix cfg) cfg)) cs) | correct (sub (fix cfg) cfg) cs
-- correct (fix cfg) cs | [] | [] = {!   !}
-- correct (fix cfg) cs | r ∷ rs | a ∷ all = {!   !}
