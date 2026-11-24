import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5

/-!
# `PartII-b:T13/1/5/5/3` leaf: smoothness and periodicity of `convK`

Source: `the November 2 reference manuscript` lines 1932-1935.
`convK κ u` is the Mathlib convolution `u ⋆[L, volume] κ` for the bilinear map
`L z r = r • z`; smoothness comes from `HasCompactSupport.contDiff_convolution_right`, and
periodicity from translation invariance of the integral together with `QPeriodicS`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The bilinear map `(z, r) ↦ r • z` from `ℂ × ℝ` to `ℂ`, used to write `convK` as a convolution. -/
def mollConvNice_L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip

theorem mollConvNice_eq_conv (κ : Coord → ℝ) (u : Coord → ℂ) :
    convK κ u = convolution u κ mollConvNice_L volume := by
  funext x
  rw [convolution_def]
  unfold convK
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp [mollConvNice_L, Complex.real_smul, mul_comm]

theorem mollConvNice_qShift_eq (c : ℝ) (z : Coord) :
    qShift c z = z + (0, (c, 0)) := by
  ext <;> simp [qShift]

theorem mollConvNice_qShift_sub (c : ℝ) (a b : Coord) :
    qShift c a - qShift c b = a - b := by
  rw [mollConvNice_qShift_eq c a, mollConvNice_qShift_eq c b]
  abel

theorem mollConvNice_proof : UnforcedLeray.Short.IIb.MollConvNice := by
  intro c κ u hκ hu hloc
  constructor
  · rw [mollConvNice_eq_conv]
    exact hκ.2.contDiff_convolution_right mollConvNice_L hloc hκ.1
  · intro x
    have hu' : ∀ᵐ z : Coord ∂volume, u (qShift c z) = u z := hu
    have h1 := integral_add_right_eq_self (μ := (volume : Measure Coord))
      (fun y : Coord => u y * (κ (qShift c x - y) : ℂ)) ((0 : ℝ), ((c : ℝ), (0 : ℝ)))
    show ∫ y, u y * (κ (qShift c x - y) : ℂ) = ∫ y, u y * (κ (x - y) : ℂ)
    rw [← h1]
    apply integral_congr_ae
    filter_upwards [hu'] with z hz
    rw [← mollConvNice_qShift_eq c z, hz, mollConvNice_qShift_sub]

end UnforcedLeray.Short.IIb
