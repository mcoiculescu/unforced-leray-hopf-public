import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3

/-!
# `flatBContinuous : FlatBContinuous` (decomposition of `PartIII-b:C/flatset/col/3`, leaf 2)

Source of record `the November 2 reference manuscript` lines 4957-4958.
`A` is `C^6` on `(0,∞)` (`IsAffElem.smooth`), `χf` is `C^∞`, so `Ay = χf(ν·) • A` is `C^6` on the
the interval `(0,∞)`; its derivative is continuous there (`ContDiffOn.continuousOn_deriv_of_isOpen`),
and `s ↦ μ/s` is continuous on `(0,∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatBContinuous : FlatBContinuous := by
  intro ν μ as χf A hν hχ hA
  have hχs : ContDiffOn ℝ 6 (fun t : ℝ => χf (ν * t)) (Ioi 0) :=
    ((hχ.smooth.comp (contDiff_const.mul contDiff_id)).contDiffOn).of_le (by simp)
  have hAs : ContDiffOn ℝ 6 A (Ioi 0) := hA.smooth
  have hAy : ContDiffOn ℝ 6 (Ay ν χf A) (Ioi 0) := hχs.smul hAs
  have hdy : ContinuousOn (deriv (Ay ν χf A)) (Ioi 0) :=
    hAy.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hAyc : ContinuousOn (Ay ν χf A) (Ioi 0) := hAy.continuousOn
  have hmu : ContinuousOn (fun s : ℝ => μ / s) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt hx)
  show ContinuousOn (fun s => deriv (Ay ν χf A) s + (μ / s) • Ay ν χf A s) (Ioi 0)
  exact hdy.add (hmu.smul hAyc)
