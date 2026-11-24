import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_2.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_2.L4

/-!
# `PartIII-b:C/asrc/ra/5/2` : iterated bound for the Gaussian `exp(-|x|²/(κ a))`

Assembly of `gauss_iterated_bound_of` with the two compiled inputs
`gaussQBound_proof` (L3, source 4963-4968) and `gaussExpStep_proof` (L4).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gauss_iterated_bound (κ ν s0 s1 : ℝ) (hκ : 0 < κ) (hν : 0 < ν) (hs0 : 0 < s0) (hs01 : s0 ≤ s1) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, m ≤ n → ∀ s ∈ Set.Icc s0 s1, ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ m (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1))) (s, x)‖ ≤ C * (1 + sq2 x) ^ n * Real.exp (-(sq2 x) / (κ * ageA ν s1)) :=
  gauss_iterated_bound_of κ ν s0 s1 hκ hν hs0 hs01 (gaussQBound_proof κ ν s0 s1)
    (gaussExpStep_proof κ ν s0 s1) n

end UnforcedLeray.Short.PartIIIb.Concrete
