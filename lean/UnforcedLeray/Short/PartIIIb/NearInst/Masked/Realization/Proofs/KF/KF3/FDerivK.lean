import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.TailSmooth

/-!
# `kf3FDerivK : KF3FDerivK` (source 3597-3601)

For `θ > 0`, `K_θ = δG_θ + part2 (heatTail θ)` entrywise (`IIIa.heatLerayK`).  Both summands are
differentiable: `heatG θ` is smooth (explicit Gaussian), and `part2 (heatTail θ) i j` is smooth
because `heatTail θ` is (`kf3TailSmooth`).  So `fderiv` splits (`fderiv_add`), and the
`δ_{ij}` term is `if i = j` (the `i ≠ j` summand is the constant `0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- Smoothness of the heat kernel (explicit Gaussian, all `θ`). -/
theorem kf3fd_heatG_contDiff {θ : ℝ} :
    ContDiff ℝ ∞ (UnforcedLeray.Short.IIIa.heatG θ) := by
  unfold UnforcedLeray.Short.IIIa.heatG
  apply contDiff_const.mul
  apply Real.contDiff_exp.comp
  apply ContDiff.div_const
  exact (contDiff_norm_sq ℝ).neg

/-- The second partial `∂_i∂_jH` of a smooth function is smooth. -/
theorem kf3fd_part2_smooth {H : Space → ℝ} (hH : ContDiff ℝ ∞ H) (i j : Fin 3) :
    ContDiff ℝ ∞ (UnforcedLeray.Short.IIIa.part2 H i j) := by
  unfold UnforcedLeray.Short.IIIa.part2
  have hD : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (m := ∞) (by simp)
  have hφ : ContDiff ℝ ∞ (fun y : Space => fderiv ℝ H y (UnforcedLeray.coordinateVector j)) :=
    hD.clm_apply contDiff_const
  have hD2 : ContDiff ℝ ∞
      (fderiv ℝ (fun y : Space => fderiv ℝ H y (UnforcedLeray.coordinateVector j))) :=
    hφ.fderiv_right (m := ∞) (by simp)
  exact hD2.clm_apply contDiff_const

theorem kf3FDerivK : KF3FDerivK := by
  intro θ hθ i j k x
  have hG : ContDiff ℝ ∞ (UnforcedLeray.Short.IIIa.heatG θ) := kf3fd_heatG_contDiff
  have hP : ContDiff ℝ ∞
      (UnforcedLeray.Short.IIIa.part2 (UnforcedLeray.Short.IIIa.heatTail θ) i j) :=
    kf3fd_part2_smooth (kf3TailSmooth θ hθ) i j
  have hPd : DifferentiableAt ℝ
      (UnforcedLeray.Short.IIIa.part2 (UnforcedLeray.Short.IIIa.heatTail θ) i j) x :=
    (hP.differentiable (by simp)) x
  have hGd : DifferentiableAt ℝ (UnforcedLeray.Short.IIIa.heatG θ) x :=
    (hG.differentiable (by simp)) x
  simp only [UnforcedLeray.Short.IIIa.heatLerayK]
  by_cases hij : i = j
  · simp only [if_pos hij]
    rw [fderiv_fun_add hGd hPd, ContinuousLinearMap.add_apply]
  · simp only [if_neg hij, zero_add]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
