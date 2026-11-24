import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_4_4.Gauss

/-!
# Gaussian core bound for `ψ_j` (task `ra_9_1_2_5_4_5`)

Source lines 4963-4968 (Gaussians `V_j`, `ψ_j`) and 4991 (Gaussian decay).
`ψ_j(s, x) = -2 a^{-1} e^{-|x|^2/(4a)}` at `j = 0`. The bound is the Leibniz rule for
`(1 + ν s)^{-1}` (via `eqd_g_bd`) against `exp(eqQ)` (via `gauss_prod_bd`), times the constant `-2`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psijCore_bound (ν : ℝ) (hν : 0 < ν) (s0 s1 : ℝ) (hs0 : 0 < s0) (n : ℕ) : ∃ (C κ : ℝ) (P : ℕ), 0 < κ ∧ ∀ z : Chart, s0 ≤ z.1 → z.1 ≤ s1 → ‖iteratedFDeriv ℝ n (fun q : Chart => psij ν q.1 0 q.2) z‖ ≤ C * (1 + ‖z.2‖) ^ P * Real.exp (-κ * ‖z.2‖ ^ 2) := by
  have hG1 := gauss_G1_smooth ν hν s0 hs0
  have hG1b : ∀ j : ℕ, ∃ B : ℝ, ∀ z : Chart, s0 ≤ z.1 →
      ‖iteratedFDeriv ℝ j (fun p : Chart => (1 + ν * ageSmoothT s0 p.1)⁻¹) z‖ ≤ B :=
    fun j => eqd_g_bd ν hν s0 hs0 j
  obtain ⟨C, hC0, hC⟩ := gauss_prod_bd ν hν s0 s1 hs0 _ hG1 hG1b n
  refine ⟨2 * C, gaussK ν s0 s1, 2 * n, gaussK_pos ν s0 s1 hν hs0, fun z hz1 hz2 => ?_⟩
  have hFz : ContDiffAt ℝ n (fun p : Chart => (1 + ν * ageSmoothT s0 p.1)⁻¹ * Real.exp (eqQ ν s0 p)) z :=
    ((hG1.mul (gauss_exp_smooth ν hν s0 hs0)).of_le (by exact_mod_cast le_top)).contDiffAt
  have hev : (fun q : Chart => psij ν q.1 0 q.2) =ᶠ[𝓝 z]
      (fun p : Chart => (-2 : ℝ) • ((1 + ν * ageSmoothT s0 p.1)⁻¹ * Real.exp (eqQ ν s0 p))) := by
    filter_upwards [gauss_germ_mem s0 hs0 z hz1] with p hp
    have hp' : s0 / 2 ≤ p.1 := (show s0 / 2 < p.1 from hp).le
    simp only [psij, xj, Int.cast_zero, zero_mul, sub_zero, Prod.mk.eta, eqQ,
      ageSmoothT_eq s0 hs0 p.1 hp', ageA, smul_eq_mul, mul_assoc]
  rw [((hev.iteratedFDeriv ℝ n).eq_of_nhds), iteratedFDeriv_const_smul_apply' hFz, norm_smul]
  have h2 : ‖(-2 : ℝ)‖ = 2 := by norm_num
  rw [h2]
  have hc := hC z hz1 hz2
  exact (mul_le_mul_of_nonneg_left hc (by norm_num)).trans (le_of_eq (by ring))

end UnforcedLeray.Short.PartIIIb.Concrete
