import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvEnvSub

/-!
# `ToMerNorm`: the meridional embedding loses at most a factor `2` in norm
(`toMer v = !₂[v.1, v.2]`, `‖v‖_{ℓ²} ≤ 2‖v‖_{sup}`; source 5040-5044).
-/

set_option autoImplicit false

noncomputable section

open Filter Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem toMerNorm : ToMerNorm := by
  intro w
  have h0 : (toMer w) 0 = w.1 := by simp [toMer]
  have h1 : (toMer w) 1 = w.2 := by simp [toMer]
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, h0, h1, Prod.norm_def]
  have ha : ‖w.1‖ ≤ max ‖w.1‖ ‖w.2‖ := le_max_left _ _
  have hb : ‖w.2‖ ≤ max ‖w.1‖ ‖w.2‖ := le_max_right _ _
  have hm0 : 0 ≤ 2 * max ‖w.1‖ ‖w.2‖ :=
    mul_nonneg zero_le_two (le_max_of_le_left (norm_nonneg _))
  rw [Real.sqrt_le_left hm0]
  nlinarith [pow_le_pow_left₀ (norm_nonneg w.1) ha 2, pow_le_pow_left₀ (norm_nonneg w.2) hb 2,
    sq_nonneg (max ‖w.1‖ ‖w.2‖)]

end UnforcedLeray.Short.PartIIIb.Concrete
