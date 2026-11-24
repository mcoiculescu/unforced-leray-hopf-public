import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.PdEcCont

/-!
# `PartIII-a:T21/2/7/2/1/1/3/3`: pointwise continuity of the adjoint multiplier in the age
(`AdjMPointwiseCont`)

Source: `the November 2 reference manuscript` lines 270-288 (smooth train).
`adjM r x` is a combination of `ν Δψ(x)`, the train velocity `v(r, x)` (continuous in `r` on
`[0, ∞)` by the joint smoothness `tr.isTrain.smooth_v`) and the partials `∂_j E_c(r)(x)`
(continuous in `r` by `PdEc.pdEc_continuousOn`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem adjMPointwiseCont : UnforcedLeray.Short.IIIa.AdjMPointwiseCont := by
  unfold UnforcedLeray.Short.IIIa.AdjMPointwiseCont
  intro ν hν hν1 tr ψ uψ hψ x
  have hv : ∀ j : Fin 2, ContinuousOn (fun r : ℝ => tr.v r x j) (Ici (0 : ℝ)) := fun j =>
    (UnforcedLeray.Short.IIIa.PdEc.wComp_contDiffOn tr j).continuousOn.comp
      (f := fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ)))
      (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr, mem_univ x⟩)
  have hE : ∀ j : Fin 2, ContinuousOn
      (fun r : ℝ => UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr r) x) (Ici (0 : ℝ)) :=
    fun j => UnforcedLeray.Short.IIIa.PdEc.pdEc_continuousOn tr j x
  unfold UnforcedLeray.Short.IIIa.adjM
  exact (continuousOn_const.sub
      (((hv 0).mul continuousOn_const).add ((hv 1).mul continuousOn_const))).sub
    ((continuousOn_const.mul (hE 0)).add (continuousOn_const.mul (hE 1)))
