import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2.L2

/-!
# Lemma 1 (`MollFderivApply`): differentiation of the spatial mollification

Source of record: `the November 2 reference manuscript`, line 2531 (spatial
mollification and slice derivative), with 1415-1424 for the slice identity.

The mollification is the Mathlib convolution with the scalar `lsmul` kernel
(`moll_eq_convolution_lsmul`). Its derivative is the convolution of `fderiv K` with `f`
(`HasCompactSupport.hasFDerivAt_convolution_left`), evaluated at `v` and then turned into the
stated integral by the substitution `z ↦ x - z`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem mollFderivApply : MollFderivApply := by
  intro K hK hKc f hf x v
  have hcf : HasCompactSupport (fderiv ℝ K) := hKc.fderiv ℝ
  have hcont : Continuous (fderiv ℝ K) := hK.continuous_fderiv one_ne_zero
  have hex : ConvolutionExists (fderiv ℝ K) f
      ((ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] UnforcedLeray.PhaseSpace.CVec3 →L[ℝ] UnforcedLeray.PhaseSpace.CVec3).precompL
          UnforcedLeray.Space) volume :=
    hcf.convolutionExists_left _ hcont hf
  rw [moll_eq_convolution_lsmul,
    (hKc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hK hf x).fderiv,
    convolution_def, ContinuousLinearMap.integral_apply (hex x) v]
  have key : ∫ z, fderiv ℝ K (x - z) v • f z = ∫ t, fderiv ℝ K t v • f (x - t) := by
    rw [← integral_sub_left_eq_self (fun t => fderiv ℝ K t v • f (x - t)) volume x]
    simp only [sub_sub_cancel]
  rw [key]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete
