import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1

/-!
# Sub5 (`NvBdd`): boundedness of the ring lift

Target `NvBdd` (parent file, source lines 2385-2387, 2562-2564, 2347-2369).

Status: the target `NvBdd` is FALSE as stated. Its hypotheses `InletProfHyp c T C κ b` allow
`κ * c < 0`; then the jet bound `C * exp (-(κ |η| / c))` grows in `|η|`, the profile
`b = χ(s) · exp η · v` (χ = 1 near s = 0, supported in s < T) satisfies every hypothesis, and
`‖realC (Nv R b τ y)‖ = √(age R y) · |b(chart)|` is unbounded. So this file proves the corrected
statement `nvBdd_of_pos` (assumes `0 < c`, `0 ≤ κ`, the source's sign regime `c ≥ 1`, `κ > 0`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.Axi

theorem nvBdd_norm_realC (x : UnforcedLeray.Space) :
    ‖UnforcedLeray.B0412.realC x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [UnforcedLeray.B0412.realC_apply, Complex.norm_real]

/-- Corrected `NvBdd`: the same conclusion under the sign regime `0 < c`, `0 ≤ κ`. -/
theorem nvBdd_of_pos (R c T C κ : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (hc : 0 < c) (hκ : 0 ≤ κ)
    (hT : 0 ≤ T) (hb : InletProfHyp c T C κ b) (τ : ℝ) (y : UnforcedLeray.Space) :
    ‖UnforcedLeray.B0412.realC (Nv R b τ y)‖ ≤ Real.sqrt T * C := by
  unfold InletProfHyp at hb
  obtain ⟨_, _, hsupp, hjet⟩ := hb
  have hbound0 : ∀ m : ℝ × (ℝ × ℝ), ‖b m‖ ≤ C * Real.exp (-(κ * |m.2.2| / c)) := by
    intro m
    have h := hjet 0 (by norm_num) m
    rwa [norm_iteratedFDeriv_zero] at h
  have hexp_le : ∀ m : ℝ × (ℝ × ℝ), Real.exp (-(κ * |m.2.2| / c)) ≤ 1 := by
    intro m
    rw [Real.exp_le_one_iff]
    have : 0 ≤ κ * |m.2.2| / c := div_nonneg (mul_nonneg hκ (abs_nonneg _)) hc.le
    linarith
  have hC : 0 ≤ C := by
    have h0 := hbound0 (0, (0, 0))
    dsimp only at h0
    have hpos := Real.exp_pos (-(κ * |(0 : ℝ)| / c))
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hpos
    linarith [norm_nonneg (b (0, (0, 0)))]
  have hC1 : ∀ m : ℝ × (ℝ × ℝ), ‖b m‖ ≤ C := fun m =>
    (hbound0 m).trans (mul_le_of_le_one_right hC (hexp_le m))
  by_cases hax : y ∈ UnforcedLeray.Axi.axis
  · have hϱ : UnforcedLeray.Axi.ϱ y = 0 := (UnforcedLeray.Axi.mem_axis_iff y).1 hax
    have hage : UnforcedLeray.Axi.age R y = 0 := by
      unfold UnforcedLeray.Axi.age
      rw [hϱ]
      simp
    rw [nvBdd_norm_realC, UnforcedLeray.Axi.Nv, hage, Real.sqrt_zero, zero_smul, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) hC
  · rw [nvBdd_norm_realC, UnforcedLeray.Axi.norm_Nv R b τ hax]
    by_cases hT' : T ≤ UnforcedLeray.Axi.age R y
    · rw [hsupp (UnforcedLeray.Axi.chart R τ y) hT', norm_zero, mul_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) hC
    · push_neg at hT'
      have hs : Real.sqrt (UnforcedLeray.Axi.age R y) ≤ Real.sqrt T :=
        Real.sqrt_le_sqrt hT'.le
      exact mul_le_mul hs (hC1 _) (norm_nonneg _) (Real.sqrt_nonneg _)

theorem nvBdd : NvBdd := fun R c T C κ b hc hκ hT hb τ y =>
  nvBdd_of_pos R c T C κ b hc hκ hT hb τ y

end UnforcedLeray.Short.PartIIIb.Concrete
