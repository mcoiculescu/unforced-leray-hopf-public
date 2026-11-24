import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_5

/-!
# Leaf `PartIII-a:T21/2/1/2/5/1`: the regularised stream function is smooth and periodic

Source of record: `the November 2 reference manuscript` lines 2081-2084, 3121.
`kerReg d ε z = (4π)⁻¹ log (den d z + ε)` with `den d z = cosh(2πη/d) - cos(2πq/d)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem den_contDiff_reg (d : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => UnforcedLeray.B0592.den d z) := by
  unfold UnforcedLeray.B0592.den
  fun_prop

/-- **Leaf `KerRegSmooth`** (SP 2081-2084, 3121). -/
theorem kerRegSmooth : KerRegSmooth := by
  intro d ε hd hε
  have hpos : ∀ z : ℝ × ℝ, UnforcedLeray.B0592.den d z + ε ≠ 0 := fun z => by
    linarith [den_nonneg d z]
  refine ⟨?_, ?_⟩
  · unfold kerReg
    have hlog : ContDiff ℝ ∞
        (fun z : ℝ × ℝ => Real.log (UnforcedLeray.B0592.den d z + ε)) :=
      ContDiff.log ((den_contDiff_reg d).add contDiff_const) hpos
    exact hlog.div_const _
  · intro z
    have hd0 : d ≠ 0 := hd.ne'
    have h : 2 * Real.pi * (z.1 + d) / d = 2 * Real.pi * z.1 / d + 2 * Real.pi := by
      field_simp
    simp only [kerReg, UnforcedLeray.B0592.den, h, Real.cos_add_two_pi]
