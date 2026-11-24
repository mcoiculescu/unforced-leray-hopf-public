import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Defs

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : the pair terms are continuous

Source `the November 2 reference manuscript`
4963-4972: `V_j = a⁻² e^{-|x_j|²/(4a)} J x_j` is smooth, hence so is `b_j = [V_j, B_mer x_j]`, and
`P_{jk} = Db_j V_k + DV_k b_j` is continuous.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rcPairContinuous : RcPairContinuous := by
  intro ν s B j k
  have hb := rc_brk_contDiff ν s B j
  have hV := rc_Vj_contDiff ν s k
  have hb1 : Continuous (fderiv ℝ (rcBrk ν s B j)) := hb.continuous_fderiv (by simp)
  have hV1 : Continuous (fderiv ℝ (Vj ν s k)) := hV.continuous_fderiv (by simp)
  exact (hb1.clm_apply hV.continuous).add (hV1.clm_apply hb.continuous)

end UnforcedLeray.Short.PartIIIb.Concrete
