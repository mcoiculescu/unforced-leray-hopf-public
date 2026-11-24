import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_3_1_5

/-!
# Leaf `T12/1/3/1/5/1`: the reflected mollification of a cylinder test is a cylinder test

Proves `testMollIsTest : TestMollIsTest` (SP 1670, 1923-1926). The function
`testMoll ρ φ u = ∫ y, ρ y * φ (u + y)` equals the convolution `ρ̌ ⋆ φ` with the reflected bump
`ρ̌ y = ρ (-y)` (substitution `y ↦ -y`). Smoothness follows from
`HasCompactSupport.contDiff_convolution_left`; periodicity by translating the integrand;
the `η`-support is enlarged by `ρ.rOut`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Reflected normalized bump `y ↦ ρ(-y)`. -/
def bumpReflTest (ρ : ContDiffBump (0 : ℝ × ℝ)) : ℝ × ℝ → ℝ :=
  fun y => ρ.normed volume (-y)

theorem testMoll_eq_convolution (ρ : ContDiffBump (0 : ℝ × ℝ)) (φ : ℝ × ℝ → ℝ) :
    testMoll ρ φ = convolution (bumpReflTest ρ) φ
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) volume := by
  funext u
  simp only [testMoll, convolution_def, ContinuousLinearMap.lsmul_apply, bumpReflTest, smul_eq_mul]
  refine (integral_neg_eq_self (fun y => ρ.normed volume y * φ (u + y)) volume).symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show ρ.normed volume (-t) * φ (u + -t) = ρ.normed volume (-t) * φ (u - t)
  rw [sub_eq_add_neg]

theorem testMollIsTest : UnforcedLeray.Short.IIb.TestMollIsTest := by
  intro c ρ φ hφ
  refine ⟨?_, ?_, ?_⟩
  · have hcs : HasCompactSupport (bumpReflTest ρ) := by
      unfold bumpReflTest
      simpa [Function.comp_def] using
        ρ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.neg (ℝ × ℝ))
    have hbsm : ContDiff ℝ ∞ (bumpReflTest ρ) := by
      unfold bumpReflTest
      exact ρ.contDiff_normed.comp contDiff_neg
    rw [testMoll_eq_convolution]
    exact hcs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
      hbsm hφ.smooth.continuous.locallyIntegrable
  · intro z
    simp only [testMoll]
    congr 1
    funext y
    have h := hφ.periodic (z + y)
    have e : ((z.1 + c, z.2) : ℝ × ℝ) + y = ((z + y).1 + c, (z + y).2) := by
      ext <;> simp <;> ring
    rw [e, h]
  · obtain ⟨L0, hL0⟩ := hφ.bounded
    refine ⟨L0 + ρ.rOut, fun z hz => ?_⟩
    simp only [testMoll]
    have hzero : ∀ y : ℝ × ℝ, ρ.normed volume y * φ (z + y) = 0 := by
      intro y
      by_cases hy : ρ.normed volume y = 0
      · simp [hy]
      · have hyb : y ∈ Function.support (ρ.normed volume) := hy
        rw [ContDiffBump.support_normed_eq, mem_ball_zero_iff] at hyb
        have hy2 : ‖y.2‖ ≤ ‖y‖ := norm_snd_le y
        rw [Real.norm_eq_abs] at hy2
        have hyr : |y.2| < ρ.rOut := lt_of_le_of_lt hy2 (by simpa [Real.norm_eq_abs] using hyb)
        have hineq : L0 < |(z + y).2| := by
          have e2 : (z + y).2 = z.2 + y.2 := rfl
          rw [e2]
          have h1 : |z.2| ≤ |z.2 + y.2| + |y.2| := by
            have := abs_add_le (z.2 + y.2) (-y.2)
            simpa using this
          linarith
        rw [hL0 (z + y) hineq, mul_zero]
    simp only [hzero, integral_zero]

end UnforcedLeray.Short.IIb
