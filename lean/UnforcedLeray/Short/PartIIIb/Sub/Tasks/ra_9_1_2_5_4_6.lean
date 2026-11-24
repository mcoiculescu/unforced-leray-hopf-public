import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_4_4
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_4_5

/-!
# Gaussian core bound for `V_j` and `ψ_j` together (task `ra_9_1_2_5_4_6`)

Merge of `vjCore_bound` (`ra_9_1_2_5_4_4`) and `psijCore_bound` (`ra_9_1_2_5_4_5`):
`C = |C1| + |C2|`, `κ = min κ1 κ2`, `P = max P1 P2`.
Source lines 4963-4968 (Gaussians `V_j`, `ψ_j`) and 4991 (Gaussian decay).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gaussCore_holds (ν : ℝ) (hν : 0 < ν) (s0 s1 : ℝ) (hs0 : 0 < s0) (n : ℕ) : ∃ (C κ : ℝ) (P : ℕ), 0 < κ ∧ ∀ z : Chart, s0 ≤ z.1 → z.1 ≤ s1 → ‖iteratedFDeriv ℝ n (fun q : Chart => Vj ν q.1 0 q.2) z‖ ≤ C * (1 + ‖z.2‖) ^ P * Real.exp (-κ * ‖z.2‖ ^ 2) ∧ ‖iteratedFDeriv ℝ n (fun q : Chart => psij ν q.1 0 q.2) z‖ ≤ C * (1 + ‖z.2‖) ^ P * Real.exp (-κ * ‖z.2‖ ^ 2) := by
  have mono : ∀ (C1 κ1 : ℝ) (P1 : ℕ) (C κ : ℝ) (P : ℕ) (r : ℝ), 0 ≤ r → 0 ≤ C → C1 ≤ C →
      0 < κ → κ ≤ κ1 → P1 ≤ P →
      C1 * (1 + r) ^ P1 * Real.exp (-κ1 * r ^ 2) ≤ C * (1 + r) ^ P * Real.exp (-κ * r ^ 2) := by
    intro C1 κ1 P1 C κ P r hr hC0 hC1 hκ hκκ1 hP
    have h1 : (1 + r) ^ P1 ≤ (1 + r) ^ P := pow_le_pow_right₀ (by linarith) hP
    have h2 : Real.exp (-κ1 * r ^ 2) ≤ Real.exp (-κ * r ^ 2) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hκκ1 (sq_nonneg r)
      linarith
    have hX : 0 ≤ (1 + r) ^ P1 * Real.exp (-κ1 * r ^ 2) :=
      mul_nonneg (pow_nonneg (by linarith) P1) (Real.exp_pos _).le
    calc C1 * (1 + r) ^ P1 * Real.exp (-κ1 * r ^ 2)
        = C1 * ((1 + r) ^ P1 * Real.exp (-κ1 * r ^ 2)) := by ring
      _ ≤ C * ((1 + r) ^ P1 * Real.exp (-κ1 * r ^ 2)) := mul_le_mul_of_nonneg_right hC1 hX
      _ ≤ C * ((1 + r) ^ P * Real.exp (-κ * r ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h1 h2 (Real.exp_pos _).le (pow_nonneg (by linarith) P)) hC0
      _ = C * (1 + r) ^ P * Real.exp (-κ * r ^ 2) := by ring
  obtain ⟨C1, κ1, P1, hκ1, h1⟩ := vjCore_bound ν hν s0 s1 hs0 n
  obtain ⟨C2, κ2, P2, hκ2, h2⟩ := psijCore_bound ν hν s0 s1 hs0 n
  refine ⟨|C1| + |C2|, min κ1 κ2, max P1 P2, lt_min hκ1 hκ2, fun z hz1 hz2 => ⟨?_, ?_⟩⟩
  · exact (h1 z hz1 hz2).trans
      (mono C1 κ1 P1 (|C1| + |C2|) (min κ1 κ2) (max P1 P2) ‖z.2‖ (norm_nonneg _)
        (by positivity) (by linarith [le_abs_self C1, abs_nonneg C2])
        (lt_min hκ1 hκ2) (min_le_left _ _) (le_max_left _ _))
  · exact (h2 z hz1 hz2).trans
      (mono C2 κ2 P2 (|C1| + |C2|) (min κ1 κ2) (max P1 P2) ‖z.2‖ (norm_nonneg _)
        (by positivity) (by linarith [le_abs_self C2, abs_nonneg C1])
        (lt_min hκ1 hκ2) (min_le_right _ _) (le_max_right _ _))

end UnforcedLeray.Short.PartIIIb.Concrete
