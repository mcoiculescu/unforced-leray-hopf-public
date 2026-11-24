import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_org_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.MollIntegralSplit
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

/-!
# `ShiftPairSubst`: change of variables and pulling `dotL e` out of the Bochner integral

Source `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
Integrability of `z ↦ κ z • F (x - z)` comes from `mis_integrable_kernel` (continuous compactly
supported kernel times the locally integrable `F`, `F` from `locInt_of_isInYr`). The bounded linear
map `dotL e` commutes with the integral, and `w ↦ x - w` preserves Haar measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem shiftPairSubst : ShiftPairSubst := by
  intro P hP κ hκ hcs F hF x e
  have hloc : LocallyIntegrable F volume := locInt_of_isInYr hP hF
  have hI : Integrable (fun z => κ z • F (x - z)) volume :=
    mis_integrable_kernel hloc hκ.continuous hcs x
  have hdot : ∀ (r : ℝ) (v : CVec3), dotL e (r • v) = (r : ℂ) * dotL e v := by
    intro r v
    rw [show r • v = (r : ℂ) • v from (Complex.coe_smul r v).symm, map_smul, smul_eq_mul]
  have hL := ContinuousLinearMap.integral_comp_comm (dotL e) hI
  rw [← hL]
  have hsub := integral_sub_left_eq_self
    (fun z => ((κ z : ℝ) : ℂ) * dotL e (F (x - z))) (volume : Measure (ℝ × Space)) x
  calc ∫ z, dotL e (κ z • F (x - z))
      = ∫ z, ((κ z : ℝ) : ℂ) * dotL e (F (x - z)) := by
        congr 1
        funext z
        rw [hdot]
    _ = ∫ w, ((κ (x - w) : ℝ) : ℂ) * dotL e (F (x - (x - w))) := hsub.symm
    _ = ∫ w, ((κ (x - w) : ℝ) : ℂ) * dotL e (F w) := by
        congr 1
        funext w
        rw [sub_sub_cancel]

end UnforcedLeray.Short.PartIIIb.Concrete
