module correct where
open import cfg
open import jarsec using (Parser ; run-parser ; partial-parse ; _>>=_ ; _>>_ ; _<*>_)

open import Data.Bool
open import Data.List hiding (lookup)
open import Data.Vec renaming ([_] to V[_] ; _++_ to _vv_) hiding (_>>=_)
open import Data.Fin hiding (_+_)
open import Data.Char
open import Agda.Builtin.Char renaming ( primCharEquality to charEq )
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Maybe hiding (Any ; All)
open import Data.Sum hiding (map)
open import Data.String hiding (length ; _++_) renaming (primStringToList to 𝕊→𝕃 ; primStringFromList to 𝕃→𝕊)
open import Data.Product hiding (map)
open import Agda.Builtin.Unit
open import Data.List.Any
open import Data.List.All

correct : ∀ (cfg : Cfg 0) (cs : List Char) (rs : List (List Char))
  → run-parser (interp cfg) (𝕃→𝕊 cs) ≡ just rs
  → All (λ r → r ∈[ cfg ] × ∃ (λ x → r ++ x ≡ cs)) rs

correct emp cs rs ()

correct eps cs ([] ∷ []) refl = (eps , cs , refl) ∷ []

correct (lit x) cs [] ε = []
correct (lit x) cs (r ∷ rs) ε = ({!   !} , ([] , {!   !}))
  ∷ correct (lit x) cs rs {!   !}

-- correct (lit x) [] [] ε = []
-- correct (lit x) [] (r ∷ rs) ()
-- correct (lit x) (c ∷ cs) [] ε = []
-- correct (lit x) (c ∷ cs) (r ∷ rs) ε = ({! lit c  !} , ([] , {!   !}))
--   ∷ correct (lit x) (c ∷ cs) rs {!   !}

correct (var ()) cs rs ε

correct (seq cfg₁ cfg₂) cs [] ε = []
correct (seq cfg₁ cfg₂) cs (r ∷ rs) ε = (seq {!   !} {!   !} , ({!   !} , {! ε  !}))
  ∷ (correct (seq cfg₁ cfg₂) cs rs {!   !})

-- correct (seq cfg₁ cfg₂) [] [] ε = []
-- correct (seq cfg₁ cfg₂) [] (r ∷ rs) ε = (seq {!   !} {!   !} , ([] , {! refl  !})) ∷ correct (seq cfg₁ cfg₂) [] rs {!   !}
-- correct (seq cfg₁ cfg₂) (c ∷ cs) [] ε = {!   !}
-- correct (seq cfg₁ cfg₂) (c ∷ cs) (r ∷ rs) ε = {!   !}

correct (alt cfg₁ cfg₂) cs rs ε = {!   !}

correct (many cfg) cs rs ε = {!   !}

correct (fix cfg) cs rs ε = {!   !}


-- correct cfg cs ε with to-witness ε
-- correct emp cs () | res
--
-- correct eps cs ε | res = eps
-- -- correct eps (() ∷ cs) ε | res
-- -- correct eps (c ∷ cs) ε | res = {!   !}
-- -- correct eps (c ∷ cs) ε | res with to-witness ε
-- -- correct eps (c ∷ cs) ε | res | hmm = {!   !}
--
-- -- I kNOW that c ∷ cs is absurd because epsilon says so, but agda doesn't
-- -- know how to make the connection between
-- -- I know I have to split out a lemma for this
-- -- but if I have to split out a lemma for every single one
-- -- then that's just the proof itself
--
-- -- LEMMA I WANT: bridge between ε and cs and res
--
--
-- correct (lit x) cs ε | res rewrite 𝕃⇄𝕊 cs = {! lit x  !}
-- correct (var ()) cs ε | res
-- correct (seq cfg₁ cfg₂) cs ε | res = {!   !}
-- correct (alt cfg₁ cfg₂) cs ε | res = {!   !}
-- correct (many cfg) cs ε | res = {!   !}
-- correct (fix cfg) cs ε | res = {!   !}


_ : (𝕊→𝕃 "") ∈[ eps ]
_ = eps

-- _ : (𝕊→𝕃 "") ∈[ eps ]
-- _ = lit 'x'

_ : (𝕊→𝕃 "x") ∈[ lit 'x' ]
_ = lit 'x'

-- _ : (𝕊→𝕃 "xx") ∈[ lit 'x' ]
-- _ = lit 'x'


-- _ : correct xX-or-ε (𝕊→𝕃 "xx") {!   !}
--     ≡
--     unroll {cfg = (alt (seq (lit 'x') (var zero)) eps)} (
--       alt₁ (seq (lit 'x') (unroll (
--         alt₁ (seq (lit 'x') (unroll (
--           alt₂ eps)))))))
-- _ = refl
