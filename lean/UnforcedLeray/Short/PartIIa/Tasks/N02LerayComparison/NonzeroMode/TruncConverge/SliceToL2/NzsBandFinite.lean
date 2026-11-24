import UnforcedLeray.Short.PartIIa.Sub.N02_4_11_2

/-!
# Part II-a, `Sub3` of `PartII-a:N02/4/11/2`: finiteness of a band box for `NzsMeasureSE`

Target: `nzsBandFinite : NzsBandFinite` (`Sub/N02_4_11_2.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749.

On `Icc s0 s1` with `0 < s0` the weight `s ^ (-(3/2))` is bounded by `s0 ^ (-(3/2))`, and
`volume (Icc (-L) L)` is finite, so the product measure of the box is finite.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

theorem nzsBandFinite : NzsBandFinite := by
  intro s0 s1 L hs0
  have hS : (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun s : ℝ => ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))) (Icc s0 s1) ≠ ⊤ := by
    rw [withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    have hset : Icc s0 s1 ∩ Ioi (0 : ℝ) = Icc s0 s1 :=
      inter_eq_left.2 (fun x hx => lt_of_lt_of_le hs0 hx.1)
    rw [hset]
    have hle : ∫⁻ s in Icc s0 s1, ENNReal.ofReal (s ^ (-(3 / 2 : ℝ)))
        ≤ ∫⁻ _ in Icc s0 s1, ENNReal.ofReal (s0 ^ (-(3 / 2 : ℝ))) := by
      refine setLIntegral_mono measurable_const (fun x hx => ?_)
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_nonpos hs0 hx.1 (by norm_num)
    refine ne_top_of_le_ne_top ?_ hle
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_Icc_lt_top.ne
  rw [NzsMeasureSE, Measure.prod_prod]
  exact ENNReal.mul_ne_top hS measure_Icc_lt_top.ne

end UnforcedLeray.Short.PartIIa
