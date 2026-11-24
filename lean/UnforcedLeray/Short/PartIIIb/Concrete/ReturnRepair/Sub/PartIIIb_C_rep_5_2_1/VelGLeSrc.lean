import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org

/-!
# `PartIII-b:C/rep/5/2/1/7`: `g⁻¹ ≤ 1` on body velocities (source 5117, 5143)

`ginv ≤ 1` for `γ ≥ 0`, so `bodyMeasure ≤ srcMeasure` and `eLpNorm` is monotone in the measure.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem velGLeSrc : VelGLeSrc := by
  intro c γ ν hγ hν v
  have hle : bodyMeasure c γ ν ≤ srcMeasure c := by
    rw [Measure.le_iff]
    intro s hs
    unfold bodyMeasure srcMeasure
    rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
    refine lintegral_mono fun p => ?_
    have h1 : ginv γ ν p ≤ 1 := ginv_le_one hγ hν.le p
    have h0 : 0 ≤ ginv γ ν p := by
      unfold ginv UnforcedLeray.Short.IIIa.gainG
      positivity
    have h2 : ginv γ ν p ^ 2 ≤ 1 := by nlinarith
    exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right Real.pi_pos.le h2)
  have hnorm : ENNReal.ofReal ‖v‖ = eLpNorm (v : Chart → Merid) 2 (bodyMeasure c γ ν) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp v).eLpNorm_lt_top.ne]
  rw [hnorm]
  exact eLpNorm_mono_measure _ hle

end UnforcedLeray.Short.PartIIIb.Concrete
