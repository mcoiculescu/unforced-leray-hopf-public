import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_4_4.Gauss

/-!
# Gaussian core bound for `V_j` (task `ra_9_1_2_5_4_4`)

Source lines 4963-4968 (Gaussians `V_j`, `ψ_j`) and 4991 (Gaussian decay).
`V_j(s, x) = (a^2)⁻¹ e^{-|x|^2/(4a)} Jx` with `x = x_0 = x` at `j = 0`.
Near a point with `s > s0/2` the chart function agrees with the smooth function
`(a_smooth^2)⁻¹ exp(eqQ)` times `Jrot`, and the Leibniz rule (in `gauss_smul_bd`) gives the bound.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem vjCore_bound (ν : ℝ) (hν : 0 < ν) (s0 s1 : ℝ) (hs0 : 0 < s0) (n : ℕ) : ∃ (C κ : ℝ) (P : ℕ), 0 < κ ∧ ∀ z : Chart, s0 ≤ z.1 → z.1 ≤ s1 → ‖iteratedFDeriv ℝ n (fun q : Chart => Vj ν q.1 0 q.2) z‖ ≤ C * (1 + ‖z.2‖) ^ P * Real.exp (-κ * ‖z.2‖ ^ 2) := by
  have hG1 := gauss_G1sq_smooth ν hν s0 hs0
  have hG1b : ∀ j : ℕ, ∃ B : ℝ, ∀ z : Chart, s0 ≤ z.1 →
      ‖iteratedFDeriv ℝ j (fun p : Chart => ((1 + ν * ageSmoothT s0 p.1) ^ 2)⁻¹) z‖ ≤ B := by
    intro j
    obtain ⟨B, hB⟩ := ageInvPow_iteratedFDeriv_bound ν hν s0 hs0 2 j
    refine ⟨B, fun z hz => ?_⟩
    rw [← gauss_G1sq_germ ν s0 hs0 z hz j]
    exact hB z hz
  have hGb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Chart, s0 ≤ z.1 → z.1 ≤ s1 →
      ‖iteratedFDeriv ℝ i (fun p : Chart => ((1 + ν * ageSmoothT s0 p.1) ^ 2)⁻¹ * Real.exp (eqQ ν s0 p)) z‖
        ≤ C * (1 + ‖z.2‖) ^ (2 * i) * Real.exp (-gaussK ν s0 s1 * ‖z.2‖ ^ 2) :=
    fun i => gauss_prod_bd ν hν s0 s1 hs0 _ hG1 hG1b i
  obtain ⟨C, hC0, hC⟩ := gauss_smul_bd ν hν s0 s1 hs0
    (fun p : Chart => ((1 + ν * ageSmoothT s0 p.1) ^ 2)⁻¹ * Real.exp (eqQ ν s0 p))
    (hG1.mul (gauss_exp_smooth ν hν s0 hs0)) hGb n
  refine ⟨C, gaussK ν s0 s1, 2 * n + 1, gaussK_pos ν s0 s1 hν hs0, fun z hz1 hz2 => ?_⟩
  rw [((gauss_V_germ ν s0 hs0 z hz1).iteratedFDeriv ℝ n).eq_of_nhds]
  exact hC z hz1 hz2

end UnforcedLeray.Short.PartIIIb.Concrete
