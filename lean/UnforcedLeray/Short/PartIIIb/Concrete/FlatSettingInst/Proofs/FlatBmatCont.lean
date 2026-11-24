import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_2

/-!
# `PartIII-b:C/flatset/col/2`, leaf 1: `B = (χ A)' + μ χ A / s` is continuous on `(0,∞)`

Source of record: `the November 2 reference manuscript`, lines 4957-4958.
Route: `A ∈ C^6((0,∞))` (`IsAffElem.smooth`) and `χ` is `C^∞` (`IsSourceCutoffC.smooth`), so
`A^y = χ(ν·) • A` is `C^6` on the open set `(0,∞)`; hence its derivative is continuous there
(`ContDiffOn.continuousOn_deriv_of_isOpen`), and `μ/s • A^y` is continuous there.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatBmatCont : FlatBmatCont := by
  intro ν μ as χ A hχ hA
  have hχ6 : ContDiff ℝ 6 χ :=
    hχ.smooth.of_le (by norm_num)
  have hc : ContDiff ℝ 6 (fun s : ℝ => χ (ν * s)) :=
    hχ6.comp (contDiff_const.mul contDiff_id)
  have hAy : ContDiffOn ℝ 6 (Ay ν χ A) (Ioi 0) := by
    unfold Ay
    exact (hc.contDiffOn.mono (subset_univ _)).smul hA.smooth
  have hdc : ContinuousOn (deriv (Ay ν χ A)) (Ioi 0) :=
    hAy.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hmu : ContinuousOn (fun s : ℝ => (μ / s) • Ay ν χ A s) (Ioi 0) := by
    have h1 : ContinuousOn (fun s : ℝ => μ / s) (Ioi 0) :=
      continuousOn_const.div continuousOn_id (fun s hs => (show (0 : ℝ) < s from hs).ne')
    have h2 : ContinuousOn (fun s : ℝ => Ay ν χ A s) (Ioi 0) := hAy.continuousOn
    exact h1.smul h2
  unfold Bmat
  exact hdc.add hmu

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
