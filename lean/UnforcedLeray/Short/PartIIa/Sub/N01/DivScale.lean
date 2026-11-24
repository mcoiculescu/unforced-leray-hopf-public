import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_4

/-!
# `PartII-a:N01/4`: the outer divergence in phase variables

Source `the November 2 reference manuscript`,
lines 1639-1643, 1655-1665.  Chain rule `divScaleChain`, rows are phase tests
`tensorDiv_isPhaseTest`, and the identification `divScaleTransfer` (all in
`Sub/PartII-a_N01_4.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization (IsCartTest cartDiv outerField toX)

theorem phaseDivScale : PhaseDivScale := by
  intro ε c P _ hε hc hP U hU T hT hM
  have hΦ := (tensorDiv_isPhaseTest hT).isSliceTest 2
  have key := divScaleTransfer hε hP U hU (hM.toLp _) (tensorDiv (cartRowsC T)) hΦ
    (((ε⁻¹ : ℝ)) : ℂ) (by
      filter_upwards [MemLp.coeFn_toLp hM] with w hw
      rw [hw]
      ext i
      rw [UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.cplx3_apply,
        divScaleChain ε P hε T hT w.1 w.2 i]
      simp)
  rw [key]
  congr 1
  have h32 : ε ^ (3 / 2 : ℝ) = ε * Real.sqrt ε := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hε, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hP0 : (0 : ℝ) < P := Fact.out
  rw [← Complex.ofReal_mul, h32, Real.sqrt_mul hP0.le]
  congr 1
  field_simp

end UnforcedLeray.Short.PartIIa.N01
