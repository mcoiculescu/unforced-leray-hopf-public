import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3

/-!
# `ScD1`: first derivative of the scaled field (`PartIII-b:C/rep/8/2/pres/5/3/4`)

Source of record: `shorter-proof-2026-11-02.tex` lines 4784, 5455, 5267-5268.
`D(ε²X(ε·))(v) = ε³ DX(εv)` by `JetClockCore.fderiv_Xsc`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open MeanScaleSub

theorem scD1 : MeanScaleSub.ScD1 := by
  unfold MeanScaleSub.ScD1
  intro X ε v hX hε
  rw [JetClockCore.fderiv_Xsc hX ε v, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < ε ^ 2 * ε), norm_iteratedFDeriv_one]
  exact le_of_eq (by ring)

end UnforcedLeray.Short.PartIIIb.Concrete
