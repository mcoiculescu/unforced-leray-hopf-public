import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H5.KerUnfold
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H2
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.DualFubini
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.Basic

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/6/1/1`: (H6.1a) the gradient dual identity of the adjoint heat kernel

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050. Statement: `HeatExists/Leaves.lean` (`AdjHeatGradDual`).
Route: `adjKerUnfold` with `k = adjHeatGradKer ν θ j` (Young bound from `adjHeatGradYoung`),
then the pointwise Gaussian integration by parts `Exist.dualFub_gauss_q` / `Exist.dualFub_gauss_eta`
and `Exist.pd_cylHeatSmooth`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Pointwise dual identity of the kernel gradient:
`∫ ∂_jG_{ντ}(z) ψ(x + z) dz = -P_{ντ}(∂_jψ)(x) = -∂_j(P_{ντ}ψ)(x)`. -/
theorem adjHeatGradKer_gauss_pt {c ν θ : ℝ} (hc : 0 < c) (hν : 0 < ν) (hθ : 0 < θ)
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) (j : Fin 2) (x : ℝ × ℝ) :
    ∫ z : ℝ × ℝ, adjHeatGradKer ν θ j z * ψ (x + z) =
      -B0579.pd j (Exist.cylHeatSmooth c (ν * θ) ψ) x := by
  have hνθ : 0 < ν * θ := mul_pos hν hθ
  rw [Exist.pd_cylHeatSmooth hc hψ j]
  rcases (show j = 0 ∨ j = 1 from by fin_cases j <;> simp) with rfl | rfl
  · have hk : ∀ z : ℝ × ℝ, adjHeatGradKer ν θ 0 z = (UnforcedLeray.B0296.gradHeatKernel2 (ν * θ) z).1 :=
      fun z => if_pos rfl
    simp only [hk]
    exact Exist.dualFub_gauss_q hc hνθ hψ x
  · have hk : ∀ z : ℝ × ℝ, adjHeatGradKer ν θ 1 z = (UnforcedLeray.B0296.gradHeatKernel2 (ν * θ) z).2 :=
      fun z => if_neg (by decide)
    simp only [hk]
    exact Exist.dualFub_gauss_eta hc hνθ hψ x

theorem adjHeatGradDual (m : ℝ) (hm : 8 < m) : AdjHeatGradDual m := by
  intro ν c hν hc θ hθ j w ψ hψ
  have hθpos : 0 < θ := hθ.1
  obtain ⟨C₁, -, hY⟩ := adjHeatGradYoung m hm ν c hν hc
  have hYθ := hY θ hθ j
  have hU := adjKerUnfold m hm c hc (adjHeatGradKer ν θ j)
    (continuous_adjHeatGradKer ν θ j) _ hYθ w ψ hψ
  rw [hU]
  simp only [adjHeatGradKer_gauss_pt hc hν hθpos hψ j]
  rw [← integral_neg]
  congr 1
  funext x
  rw [Complex.ofReal_neg]
  ring

end UnforcedLeray.Short.IIIa
