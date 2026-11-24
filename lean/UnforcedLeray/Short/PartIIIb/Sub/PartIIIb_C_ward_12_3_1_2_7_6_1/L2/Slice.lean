import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1

/-!
# Slices of `dy` (helper for `nvFirstPt`, `nvSecondPt`)

Source `the November 2 reference manuscript`
lines 2385-2387, 2562-2564: the joint partials `dy j Φ (τ, y)` are the `y`-derivatives of the
phase slice `Φ (τ, ·)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Axi

theorem dy_slice_cv {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : Differentiable ℝ Φ) (j : Fin 3)
    (τ : ℝ) (y : UnforcedLeray.Space) :
    dy j Φ (τ, y) = fderiv ℝ (fun z : UnforcedLeray.Space => Φ (τ, z)) y (coordinateVector j) := by
  have h1 : HasFDerivAt (fun z : UnforcedLeray.Space => ((τ, z) : ℝ × UnforcedLeray.Space))
      ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ UnforcedLeray.Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have h2 : (fun z : UnforcedLeray.Space => Φ (τ, z)) =
      Φ ∘ (fun z : UnforcedLeray.Space => ((τ, z) : ℝ × UnforcedLeray.Space)) := rfl
  rw [h2, fderiv_comp y (hΦ (τ, y)) h1.differentiableAt, h1.fderiv]
  simp [dy]

theorem norm_cv (i : Fin 3) : ‖(coordinateVector i : UnforcedLeray.Space)‖ = 1 := by
  simp [coordinateVector]

theorem dy_dy_le {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (j k : Fin 3)
    (τ : ℝ) (y : UnforcedLeray.Space) :
    ‖dy j (dy k Φ) (τ, y)‖ ≤ ‖iteratedFDeriv ℝ 2 (fun z : UnforcedLeray.Space => Φ (τ, z)) y‖ := by
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hdk : Differentiable ℝ (dy k Φ) := (UnforcedLeray.PhaseSpace.contDiff_dy hΦ k).differentiable (by simp)
  have hf : ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => Φ (τ, z)) :=
    hΦ.comp (contDiff_const.prodMk contDiff_id)
  have e1 : (fun z : UnforcedLeray.Space => dy k Φ (τ, z)) =
      fun z => fderiv ℝ (fun w : UnforcedLeray.Space => Φ (τ, w)) z (coordinateVector k) := by
    funext z; exact dy_slice_cv hd k τ z
  rw [dy_slice_cv hdk, e1]
  have hdf : DifferentiableAt ℝ (fderiv ℝ (fun w : UnforcedLeray.Space => Φ (τ, w))) y :=
    (hf.fderiv_right (m := 1) (by simp)).differentiable (by simp) y
  rw [fderiv_clm_apply hdf (differentiableAt_const _)]
  rw [fderiv_const_apply]
  have hn : ‖fderiv ℝ (fderiv ℝ fun w : UnforcedLeray.Space => Φ (τ, w)) y‖ =
      ‖iteratedFDeriv ℝ 2 (fun z : UnforcedLeray.Space => Φ (τ, z)) y‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  calc ‖(fderiv ℝ (fderiv ℝ fun w : UnforcedLeray.Space => Φ (τ, w)) y) (coordinateVector j)
        (coordinateVector k)‖
      ≤ ‖fderiv ℝ (fderiv ℝ fun w : UnforcedLeray.Space => Φ (τ, w)) y‖ *
          ‖coordinateVector j‖ * ‖coordinateVector k‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
    _ = ‖iteratedFDeriv ℝ 2 (fun z : UnforcedLeray.Space => Φ (τ, z)) y‖ := by
        rw [hn, norm_cv j, norm_cv k]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
