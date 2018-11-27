complete : ∀ {n : ℕ} (cfg : Cfg 0) s → (𝕊→𝕃 s) ∈[ cfg ] → Is-just (run-parser (interp cfg) (s))
complete cfg s ε = {!   !}
