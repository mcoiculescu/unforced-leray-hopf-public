import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs

/-!
# `pdTheta`: the radial gap is automatic

Source `the November 2 reference manuscript` 5588-5589 (`e^δ < 12/11 < 6/5`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem pdTheta : PDTheta := by
  intro δ hδ
  have hx : (0 : ℝ) < Real.exp (-(δ / 2)) := Real.exp_pos _
  rw [Real.sqrt_lt' hx]
  have h2 : Real.exp (-(δ / 2)) ^ 2 = Real.exp (-δ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h2]
  have h3 : Real.exp (-Real.log (12 / 11)) < Real.exp (-δ) :=
    Real.exp_lt_exp.mpr (by linarith)
  rw [Real.exp_neg, Real.exp_log (by norm_num)] at h3
  norm_num at h3
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
