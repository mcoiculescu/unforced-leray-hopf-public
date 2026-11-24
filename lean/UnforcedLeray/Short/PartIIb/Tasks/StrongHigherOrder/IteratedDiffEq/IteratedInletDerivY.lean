import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.IteratedInletDerivY.Near
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.IteratedInletDerivY.Far
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawAllDerivsBdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open UnforcedLeray.Short.PartIIIb.Concrete (cylProfile)

namespace UnforcedLeray.Short.IIb

private theorem inletResidualIteratedEnvelope_proof : InletResidualIteratedEnvelope := by
  intro lam q hq dm dp hdm
  obtain ⟨ν_n, hν_n, HN⟩ := IterInletSub.inletNearAll lam q hq dm dp hdm
  obtain ⟨ν_f, hν_f, HF⟩ := IterInletSub.inletFarAll lam q hq dm dp hdm
  refine ⟨min ν_n ν_f, lt_min hν_n hν_f, fun p d hreg hν hmode i m β => ?_⟩
  have hνn : p.ν ≤ ν_n := hν.trans (min_le_left _ _)
  have hνf : p.ν ≤ ν_f := hν.trans (min_le_right _ _)
  obtain ⟨Cf, R0, hR0, hfar⟩ := HF p d hreg hνf hmode i m β
  obtain ⟨Cn, hnear⟩ := HN p d hreg hνn hmode i m β R0 hR0
  refine ⟨max Cf Cn, R0, hR0, fun τ hτ y => ?_⟩
  by_cases hρ : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0
  · have hn := hnear τ hτ y hρ
    have hcyl : cylProfile R0 y = (1 + |y 2|) ^ (-2 : ℝ) := by
      simp [cylProfile, hρ]
    rw [hcyl]
    exact hn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))
  · have hf := hfar τ hτ y (lt_of_not_ge hρ)
    have hcyl : cylProfile R0 y = Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
        (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ) := by
      simp [cylProfile, hρ]
    rw [hcyl]
    have hnn1 : 0 ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hnn2 : 0 ≤ (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ) :=
      Real.rpow_nonneg (add_nonneg zero_le_one (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))) _
    have hmul : Cf * Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
        (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ) ≤
        max Cf Cn * (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
          (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hnn1 hnn2)
    exact hf.trans hmul

/-- **Target** `IteratedInletDerivY`: all-order `y`-derivatives of the inlet residual satisfy the
`L^{q₀}` bound in `(τ, y)` with `ν₀` independent of `m`. -/
theorem iteratedInletDerivY_proof : UnforcedLeray.Short.IIb.IteratedInletDerivY :=
  iteratedInletDerivY_of_envelope
    (UnforcedLeray.Short.PartIIIb.Concrete.inletBackgroundBounds_of
      UnforcedLeray.Short.PartIIIb.Concrete.rawJointSmooth
      (rawDerivBdd_of_all rawAllDerivsBdd_proof))
    inletResidualIteratedEnvelope_proof

end UnforcedLeray.Short.IIb
