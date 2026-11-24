import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Rad
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Lap

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem tcRadW : TCRadW := by
  intro σ₁ σ₂ ν μ R P T τ y hctx
  have H := tcb_of_ctxW hctx
  have hy := tcb_ann_gtW hctx
  have hρ : 0 < ϱ y := lt_of_le_of_lt H.ha hy
  have hdiff := tcb_u_diff H τ hy
  have hpsi : psiFld (sepX0 ν μ T) τ =
      fun y' => outPrim (sepX0 ν μ T) τ (ϱ y') (y' 2) • (coordinateVector 2 : Space) := rfl
  rw [hpsi, fderiv_smul_const hdiff]
  simp only [ContinuousLinearMap.smulRight_apply]
  have hdu := tcb_du H τ hy (radialUnit y)
  have hr0 : (radialUnit y) 0 = y 0 / ϱ y := by
    simp [radialUnit, div_eq_inv_mul]
  have hr1 : (radialUnit y) 1 = y 1 / ϱ y := by
    simp [radialUnit, div_eq_inv_mul]
  have hr2 : (radialUnit y) 2 = 0 := by simp [radialUnit]
  rw [hr0, hr1, hr2] at hdu
  have hsq : y 0 * (y 0 / ϱ y) + y 1 * (y 1 / ϱ y) = ϱ y := by
    have hsq' : 0 < y 0 ^ 2 + y 1 ^ 2 := by
      by_contra hh
      have : ϱ y = 0 := by
        unfold ϱ
        rw [Real.sqrt_eq_zero_of_nonpos (not_lt.1 hh)]
      linarith
    have hρ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt hsq'.le
    field_simp
    linarith
  have hrep := (tcb_rep H.hν H.hμ H.ha H.hP H.hT H.hM H.hA τ hy).2.2
  rw [hdu, hsq]
  simp [hrep]

end UnforcedLeray.Short.PartIIIb.Concrete

end
