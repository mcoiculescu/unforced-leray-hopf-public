import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvEnvSub

/-!
# `ZPairBound`: the planar profile `(0, f)` (source 5034-5044, `H e_z`, `k e_z`)

The derivative of `y ↦ (0, f s y)` is `(0, Df)` (so `‖·‖ ≤ ‖Df‖`), and `𝒦` acts componentwise,
killing the zero component, so `‖𝒦(0,f)‖ = |𝒦 f|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

theorem zPairBound : ZPairBound := by
  intro f s x
  constructor
  · by_cases hd : DifferentiableAt ℝ (f s) x
    · have hg : HasFDerivAt (fun y => ((0 : ℝ), f s y))
          ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (fderiv ℝ (f s) x)) x :=
        (hasFDerivAt_const (0 : ℝ) x).prodMk hd.hasFDerivAt
      rw [hg.fderiv]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro v
      rw [ContinuousLinearMap.prod_apply, zero_apply, Prod.norm_def]
      dsimp only
      rw [norm_zero]
      exact max_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        ((fderiv ℝ (f s) x).le_opNorm v)
    · have hz : fderiv ℝ (fun y => ((0 : ℝ), f s y)) x = 0 := by
        apply fderiv_zero_of_not_differentiableAt
        intro h
        exact hd h.snd
      have hz2 : fderiv ℝ (f s) x = 0 := fderiv_zero_of_not_differentiableAt hd
      simp [hz, hz2]
  · have hz : Kop (fun s' y => ((0 : ℝ), f s' y).1) s x = 0 := by
      unfold Kop
      simp
    have h1 : cK (fun s' y => ((0 : ℝ), f s' y)) s x = (0, Kop f s x) := by
      unfold cK
      exact Prod.ext hz rfl
    rw [h1, Prod.norm_def]
    show max ‖(0 : ℝ)‖ ‖Kop f s x‖ ≤ |Kop f s x|
    rw [norm_zero, Real.norm_eq_abs]
    exact le_of_eq (max_eq_right (abs_nonneg _))

end UnforcedLeray.Short.PartIIIb.Concrete
