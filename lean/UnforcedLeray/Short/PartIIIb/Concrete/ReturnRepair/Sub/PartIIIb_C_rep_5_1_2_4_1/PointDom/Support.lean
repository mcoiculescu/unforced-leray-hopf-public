import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs

/-!
# `pdSupport`: the old source vanishes beyond the young cone

Source `the November 2 reference manuscript` 4163-4167.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem pdSupport : PDSupport := by
  intro ν R c g hν hR hg y hy hage σ z hz
  unfold age at hage
  have hpos : 0 < ϱ y ^ 2 := by positivity
  rw [← mul_div_assoc, div_le_one hpos] at hage
  have hs : Real.sqrt (5 / 6) ^ 2 = 5 / 6 := Real.sq_sqrt (by norm_num)
  have hsq : 0 ≤ Real.sqrt (5 / 6) * ϱ y := by positivity
  have hm := mul_self_lt_mul_self hsq hz
  have e : (Real.sqrt (5 / 6) * ϱ y) * (Real.sqrt (5 / 6) * ϱ y)
      = Real.sqrt (5 / 6) ^ 2 * ϱ y ^ 2 := by ring
  rw [hs] at e
  have hzpos : 0 < ϱ z ^ 2 := by
    have : 0 < ϱ z := lt_of_le_of_lt hsq hz
    positivity
  have hlt : (NearInst.chartOf R c z σ).1 < 6 / (5 * ν) := by
    show R ^ 2 / NearInst.hRad z ^ 2 < 6 / (5 * ν)
    have hr : NearInst.hRad z = ϱ z := rfl
    rw [hr, div_lt_div_iff₀ hzpos (by positivity)]
    nlinarith [hm, e, hage]
  have hg0 : g (NearInst.chartOf R c z σ) = 0 := hg _ hlt
  have hnull : NearInst.nsSym (0 : Ten3) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [NearInst.nsSym, NearInst.symRZ]
  unfold oldPhys NearInst.cartLift
  rw [hg0, hnull, smul_zero, mul_zero, zero_mul]

end UnforcedLeray.Short.PartIIIb.Concrete

end
