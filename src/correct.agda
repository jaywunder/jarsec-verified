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
open import Data.Maybe
open import Data.Sum hiding (map)
open import Data.String hiding (length ; _++_) renaming (primStringToList to 𝕊→𝕃 ; primStringFromList to 𝕃→𝕊)
open import Data.Product hiding (map)
open import Agda.Builtin.Unit


correct : ∀ (cfg : Cfg 0) (cs : List Char) → Is-just (run-parser (interp cfg) (𝕃→𝕊 cs)) → cs ∈[ cfg ]
correct cfg cs ε rewrite 𝕃⇄𝕊 cs with to-witness ε
correct emp cs () | res
correct eps cs ε | res = {!   !}
correct (lit x) cs ε | res = {!   !}
correct (var ()) cs ε | res
correct (seq cfg cfg₁) cs ε | res = {!   !}
correct (alt cfg cfg₁) cs ε | res = {!   !}
correct (many cfg) cs ε | res = {!   !}
correct (fix cfg) cs ε | res = {!   !}


-- _ : correct xX-or-ε (𝕊→𝕃 "xx") ≡ {!   !}
-- _ = refl
