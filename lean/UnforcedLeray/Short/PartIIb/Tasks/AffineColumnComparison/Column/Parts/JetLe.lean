import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7

/-!
# Part II-b, task `PartII-b:G4/3/7/5` (`JetLe`): first-order chart calculus

Source of record: `the November 2 reference manuscript`, SP 1651-1653.

Pure calculus. With `D = ‖fderiv F x‖ = ‖iteratedFDeriv 1 F x‖` and `‖F x‖ = ‖iteratedFDeriv 0 F x‖`,
each chart derivative `dS`, `dQ`, `dEta` (directional derivatives along unit vectors) has norm
at most `D`, and `kAge F x = 2s dS F x + η dEta F x` has norm at most `(2|s| + |η|) D`.
Summing gives `chartJet F x + ‖dS F x‖ ≤ 4 (1 + |s| + |η|) (‖F x‖ + D)`, so `K = 4` works.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace JetLeHelp

/-- A directional derivative along a vector of norm at most `1` is at most the derivative norm. -/
theorem dir_le {F : Coord → Axi.Merid} (x : Coord) (v : Coord) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ F x v‖ ≤ ‖fderiv ℝ F x‖ :=
  ((fderiv ℝ F x).le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg _) hv)

theorem e1_le : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by
  simp

theorem eQ_le : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by
  simp

theorem eEta_le : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by
  simp

end JetLeHelp

open JetLeHelp

/-- **First-order chart calculus** (SP 1651-1653): `K = 4` works. -/
theorem jetLe : UnforcedLeray.Short.IIb.JetLe := by
  refine ⟨4, by norm_num, ?_⟩
  intro F _hF x
  have h0 : ‖iteratedFDeriv ℝ 0 F x‖ = ‖F x‖ := norm_iteratedFDeriv_zero
  have h1 : ‖iteratedFDeriv ℝ 1 F x‖ = ‖fderiv ℝ F x‖ := norm_iteratedFDeriv_one F
  have hS : ‖Axi.dS F x‖ ≤ ‖fderiv ℝ F x‖ := dir_le x _ e1_le
  have hQ : ‖Axi.dQ F x‖ ≤ ‖fderiv ℝ F x‖ := dir_le x _ eQ_le
  have hE : ‖Axi.dEta F x‖ ≤ ‖fderiv ℝ F x‖ := dir_le x _ eEta_le
  have hD0 : 0 ≤ ‖fderiv ℝ F x‖ := norm_nonneg _
  have hK : ‖kAge F x‖ ≤ (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ F x‖ := by
    unfold kAge
    calc ‖(2 * x.1) • Axi.dS F x + x.2.2 • Axi.dEta F x‖
        ≤ ‖(2 * x.1) • Axi.dS F x‖ + ‖x.2.2 • Axi.dEta F x‖ := norm_add_le _ _
      _ = |2 * x.1| * ‖Axi.dS F x‖ + |x.2.2| * ‖Axi.dEta F x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |2 * x.1| * ‖fderiv ℝ F x‖ + |x.2.2| * ‖fderiv ℝ F x‖ := by
          gcongr
      _ ≤ (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ F x‖ := by
          have : |2 * x.1| = 2 * |x.1| := by
            rw [abs_mul]; norm_num
          rw [this]
          nlinarith [abs_nonneg x.1, abs_nonneg x.2.2, hD0]
  have hA : 0 ≤ |x.1| := abs_nonneg _
  have hB : 0 ≤ |x.2.2| := abs_nonneg _
  have hF0 : 0 ≤ ‖F x‖ := norm_nonneg _
  unfold chartJet
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1]
  nlinarith [mul_nonneg hD0 hA, mul_nonneg hD0 hB, mul_nonneg hF0 hA, mul_nonneg hF0 hB,
    mul_nonneg hD0 hA, mul_nonneg hF0 hD0]

end UnforcedLeray.Short.IIb

end
