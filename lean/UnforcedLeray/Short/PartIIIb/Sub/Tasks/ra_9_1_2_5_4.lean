import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_5_4
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_4_6

/-!
# Gaussian majorant for `V_j` and `ψ_j` on a compact set (task `ra_9_1_2_5_4`)

Source lines 4963-4968 (Gaussians `V_j`, `ψ_j`) and 4991 (Gaussian decay).

`j = 0` Gaussian core as hypothesis; that core is `gaussCore_holds`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem vjPsijMajor (ν : ℝ) (hν : 0 < ν) (K : Set Chart) (hK : IsCompact K) (hKs : K ⊆ Set.Ioi 0 ×ˢ Set.univ) (n : ℕ) : ∃ (C c : ℝ) (P : ℕ), 0 < c ∧ ∀ (j : ℤ), ∀ p ∈ K, ‖iteratedFDeriv ℝ n (fun q : Chart => Vj ν q.1 j q.2) p‖ ≤ C * (1 + |(j : ℝ)|) ^ P * Real.exp (-c * (j : ℝ) ^ 2) ∧ ‖iteratedFDeriv ℝ n (fun q : Chart => psij ν q.1 j q.2) p‖ ≤ C * (1 + |(j : ℝ)|) ^ P * Real.exp (-c * (j : ℝ) ^ 2) :=
  T54.vjPsijMajor_of gaussCore_holds ν hν K hK hKs n

end UnforcedLeray.Short.PartIIIb.Concrete
