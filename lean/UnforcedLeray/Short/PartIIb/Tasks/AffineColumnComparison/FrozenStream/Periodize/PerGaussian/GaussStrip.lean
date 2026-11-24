import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_3_3

/-!
# Part II-b, task `PartII-b:G4/2/3/3/2`: strip comparison `e^{-κx₂²} ≤ K e^{-κ|x₂|/c}`

Source of record: `the November 2 reference manuscript`, lines 2349-2358.
With `K = e^{κ/4}`: `κ(|x₂|/c - x₂²) ≤ κ(|x₂| - x₂²) ≤ κ/4`, since `c ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem gaussStripLe : UnforcedLeray.Short.IIb.GaussStripLe := by
  unfold UnforcedLeray.Short.IIb.GaussStripLe
  intro κ hκ
  refine ⟨Real.exp (κ / 4), fun c hc x₂ => ?_⟩
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have habs : 0 ≤ |x₂| := abs_nonneg x₂
  have hc0 : 0 < c := by linarith
  have h1 : |x₂| / c ≤ |x₂| := div_le_self habs hc
  have h2 : |x₂| - x₂ ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_nonneg (|x₂| - 1 / 2), sq_abs x₂]
  have h3 : |x₂| / c - x₂ ^ 2 ≤ 1 / 4 := by linarith
  have h4 : κ * (|x₂| / c - x₂ ^ 2) ≤ κ * (1 / 4) :=
    mul_le_mul_of_nonneg_left h3 hκ.le
  have h5 : κ * (|x₂| / c - x₂ ^ 2) = κ * |x₂| / c - κ * x₂ ^ 2 := by ring
  have h6 : κ * |x₂| / c = κ * (|x₂| / c) := by ring
  linarith

end UnforcedLeray.Short.IIb
