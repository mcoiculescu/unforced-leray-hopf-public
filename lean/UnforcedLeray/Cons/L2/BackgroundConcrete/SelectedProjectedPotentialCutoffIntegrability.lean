import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffShell
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellVectorSupport
import UnforcedLeray.Lib.Semigroups.Multiplication

set_option autoImplicit false

noncomputable section

open MeasureTheory
open Filter Topology
open Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp
open UnforcedLeray.B0412
open NavierStokesR3.ComparisonCutoffs

local instance cutoff_dual_ge_one : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

local instance cutoff_holder : ENNReal.HolderTriple (conjExp q0E) q0E 1 :=
  UnforcedLeray.Sob.holderTriple_conjExp q0E

/-- The derivative of the spatial cutoff vanishes outside its support radius. -/
private theorem gradField_cutoff_eq_zero_of_gt {R : ℝ} (hR : 0 < R) {y : Space}
    (hy : 2 * R < ‖y‖) : gradField (cutoff R) y = 0 := by
  let δ : ℝ := (‖y‖ - 2 * R) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hnear : ∀ᶠ x in 𝓝 y, cutoff R x = 0 := by
    filter_upwards [Metric.ball_mem_nhds y hδ] with x hx
    have hdist : ‖y - x‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx
    have htri : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      calc
        ‖y‖ = ‖x + (y - x)‖ := by congr 1; abel
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
    have hfar : 2 * R < ‖x‖ := by dsimp [δ] at hdist ⊢; linarith
    rw [cutoff_eq_zero hR (le_of_lt hfar)]
  have hfd : fderiv ℝ (cutoff R) y = 0 := by
    have hEq : (fun x => cutoff R x) =ᶠ[𝓝 y] fun _ : Space => 0 := hnear
    rw [hEq.fderiv_eq]
    simp
  ext i
  rw [gradField_apply, spatialTestDerivative, hfd]
  simp

private theorem memLp_projectedPotentialImGradient_cell {P : ℝ} [Fact (0 < P)]
    {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    MemLp (fun z : SpaceTime => ofImV
      (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
      (conjExp q0E) (volume.restrict (phaseCell P)) := by
  have hC := memLp_projectedNewtonCorrection_cell hΦ
  change MemLp (fun z : SpaceTime =>
      ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
        ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
      (conjExp q0E) (volume.restrict (phaseCell P)) at hC
  have hIm0 : MemLp (fun z => ofImV (imV
      (ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
        ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))))
      (conjExp q0E) (volume.restrict (phaseCell P)) :=
    (hC.continuousLinearMap_comp imV).continuousLinearMap_comp ofImV
  have hpt (z : SpaceTime) : ofImV
      (imV (ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
        ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))) =
      ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2) := by
    ext i
    simp [imV_apply, ofImV_apply]
  exact MemLp.ae_eq (ae_of_all _ fun z => hpt z) hIm0

/-- The cutoff-main real Newton-gradient term pairs integrably with every actual phase-space
`L^(11/4)` representative, by the product-cell dual bound for the full Newton correction. -/
theorem integrable_projectedPotentialReCutoffMain_pair_rep_cell {P R : ℝ}
    [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ)
    {w : Yq P q0E} :
    Integrable (fun z => dotL
      (ofReV (cutoff R z.2 •
        gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2))
      (rep w z.1 z.2)) (volume.restrict (phaseCell P)) := by
  have hC : MemLp (fun z =>
      ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
        ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
      (conjExp q0E) (volume.restrict (phaseCell P)) :=
    memLp_projectedNewtonCorrection_cell hΦ
  have hR0 : MemLp (fun z => ofReV (reV
      (ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
       ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))))
      (conjExp q0E) (volume.restrict (phaseCell P)) :=
    (hC.continuousLinearMap_comp reV).continuousLinearMap_comp ofReV
  have hRe : MemLp (fun z => ofReV
      (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2))
      (conjExp q0E) (volume.restrict (phaseCell P)) := by
    have hpt (z : SpaceTime) : ofReV
        (reV (ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
          ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))) =
        ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) := by
      ext i
      simp [reV_apply, ofReV_apply, ofImV_apply]
    have hR0' : MemLp (fun z => ofReV (reV
        (ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
         ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))))
        (conjExp q0E) (volume.restrict (phaseCell P)) := hR0
    exact MemLp.ae_eq (ae_of_all _ fun z => hpt z) hR0'
  let m : SpaceTime → ℂ := fun z => (cutoff R z.2 : ℂ)
  have hmcont : Continuous m :=
    Complex.continuous_ofReal.comp ((cutoff_smooth R).continuous.comp continuous_snd)
  have hm : AEStronglyMeasurable m (volume.restrict (phaseCell P)) := hmcont.aestronglyMeasurable
  have hmbound : ∀ᵐ z ∂(volume.restrict (phaseCell P)), ‖m z‖ ≤ 1 :=
    ae_of_all _ fun z => by
    change ‖(cutoff R z.2 : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h01 := cutoff_mem_Icc R z.2
    rw [abs_of_nonneg h01.1]
    exact h01.2
  have hmain : MemLp (fun z => m z •
      ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2))
      (conjExp q0E) (volume.restrict (phaseCell P)) :=
    UnforcedLeray.Infra.Mult.memLp_smul_of_bdd hm hmbound hRe
  have hmainEq : (fun z => ofReV (cutoff R z.2 •
      gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2)) =ᵐ[volume.restrict (phaseCell P)]
      fun z => m z • ofReV
        (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) := by
    exact ae_of_all _ fun z => by simp [m, map_smul]
  have hmain' : MemLp (fun z => ofReV (cutoff R z.2 •
      gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2))
      (conjExp q0E) (volume.restrict (phaseCell P)) := MemLp.ae_eq hmainEq.symm hmain
  have hW : MemLp (fun z : SpaceTime => rep w z.1 z.2) q0E
      (volume.restrict (phaseCell P)) :=
    memLp_rep_periodCell q0E_ne_top w
  exact integrable_dotL_of_memLp_holder hmain' hW

/-- The actual potential times the cutoff-shell gradient has compact spatial support and hence
pairs integrably with the selected joint representative on the phase cell. -/
theorem integrable_projectedPotentialReCutoffShell_pair_rep_cell {P R : ℝ}
    [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ)
    (hR : 0 < R) {w : Yq P q0E} :
    Integrable (fun z => dotL
      (ofReV (projectedPotentialRePath Φ z • gradField (cutoff R) z.2))
      (rep w z.1 z.2)) (volume.restrict (phaseCell P)) := by
  let S : ℝ := 2 * R
  let F : SpaceTime → CVec3 := fun z =>
    ofReV (projectedPotentialRePath Φ z • gradField (cutoff R) z.2)
  have hpot : Continuous (projectedPotentialRePath Φ) :=
    (contDiff_projectedPotentialRePath hΦ).continuous
  have hgrad : Continuous (fun z : SpaceTime => gradField (cutoff R) z.2) :=
    (continuous_gradField (cutoff_smooth R)).comp continuous_snd
  have hcont : Continuous F := by
    exact ofReV.continuous.comp (hpot.smul hgrad)
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) S) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC0, hC⟩ := exists_norm_bound_on_compact F hcont hK
  have hbound : ∃ C : ℝ, ∀ z ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) S,
      ‖F z‖ ≤ C := ⟨C, hC⟩
  have hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ y : Space, S < ‖y‖ → F (τ, y) = 0 := by
    intro τ hτ y hy
    have hgrad0 := gradField_cutoff_eq_zero_of_gt hR (by simpa [S] using hy)
    simp [F, hgrad0]
  have hF : MemLp F (conjExp q0E) (volume.restrict (phaseCell P)) :=
    memLp_vector_on_phaseCell_of_spatialSupport
      (p := conjExp q0E) (conjExp_ne_top one_lt_q0E) hcont.aestronglyMeasurable hbound hzero
  have hW : MemLp (fun z : SpaceTime => rep w z.1 z.2) q0E
      (volume.restrict (phaseCell P)) :=
    memLp_rep_periodCell q0E_ne_top w
  exact integrable_dotL_of_memLp_holder hF hW

/-- The imaginary-source shell pairing uses the actual `ofImV` component. -/
theorem integrable_projectedPotentialImCutoffMain_pair_rep_cell {P R : ℝ}
    [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ)
    {w : Yq P q0E} :
    Integrable (fun z => dotL
      (ofImV (cutoff R z.2 •
        gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
      (rep w z.1 z.2)) (volume.restrict (phaseCell P)) := by
  have hIm := memLp_projectedPotentialImGradient_cell hΦ
  let m : SpaceTime → ℂ := fun z => (cutoff R z.2 : ℂ)
  have hmcont : Continuous m :=
    Complex.continuous_ofReal.comp ((cutoff_smooth R).continuous.comp continuous_snd)
  have hm : AEStronglyMeasurable m (volume.restrict (phaseCell P)) :=
    hmcont.aestronglyMeasurable
  have hmbound : ∀ᵐ z ∂(volume.restrict (phaseCell P)), ‖m z‖ ≤ 1 :=
    ae_of_all _ fun z => by
      change ‖(cutoff R z.2 : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h01 := cutoff_mem_Icc R z.2
      rw [abs_of_nonneg h01.1]
      exact h01.2
  have hmain : MemLp (fun z => m z • ofImV
      (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
      (conjExp q0E) (volume.restrict (phaseCell P)) :=
    UnforcedLeray.Infra.Mult.memLp_smul_of_bdd hm hmbound hIm
  have hmainEq : (fun z => ofImV (cutoff R z.2 •
      gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2)) =ᵐ[
        volume.restrict (phaseCell P)] fun z => m z • ofImV
        (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2) :=
    ae_of_all _ fun z => by simp [m, map_smul]
  have hM : MemLp (fun z => ofImV (cutoff R z.2 •
      gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
      (conjExp q0E) (volume.restrict (phaseCell P)) :=
    MemLp.ae_eq hmainEq.symm hmain
  have hW : MemLp (fun z : SpaceTime => rep w z.1 z.2) q0E
      (volume.restrict (phaseCell P)) :=
    memLp_rep_periodCell q0E_ne_top w
  exact integrable_dotL_of_memLp_holder hM hW

theorem integrable_projectedPotentialImCutoffShell_pair_rep_cell {P R : ℝ}
    [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ)
    (hR : 0 < R) {w : Yq P q0E} :
    Integrable (fun z => dotL
      (ofImV (projectedPotentialImPath Φ z • gradField (cutoff R) z.2))
      (rep w z.1 z.2)) (volume.restrict (phaseCell P)) := by
  let S : ℝ := 2 * R
  let F : SpaceTime → CVec3 := fun z =>
    ofImV (projectedPotentialImPath Φ z • gradField (cutoff R) z.2)
  have hpot : Continuous (projectedPotentialImPath Φ) :=
    (contDiff_projectedPotentialImPath hΦ).continuous
  have hgrad : Continuous (fun z : SpaceTime => gradField (cutoff R) z.2) :=
    (continuous_gradField (cutoff_smooth R)).comp continuous_snd
  have hcont : Continuous F := by
    exact ofImV.continuous.comp (hpot.smul hgrad)
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) S) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC0, hC⟩ := exists_norm_bound_on_compact F hcont hK
  have hbound : ∃ C : ℝ, ∀ z ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) S,
      ‖F z‖ ≤ C := ⟨C, hC⟩
  have hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ y : Space, S < ‖y‖ → F (τ, y) = 0 := by
    intro τ hτ y hy
    have hgrad0 := gradField_cutoff_eq_zero_of_gt hR (by simpa [S] using hy)
    simp [F, hgrad0]
  have hF : MemLp F (conjExp q0E) (volume.restrict (phaseCell P)) :=
    memLp_vector_on_phaseCell_of_spatialSupport
      (p := conjExp q0E) (conjExp_ne_top one_lt_q0E) hcont.aestronglyMeasurable hbound hzero
  have hW : MemLp (fun z : SpaceTime => rep w z.1 z.2) q0E
      (volume.restrict (phaseCell P)) := by
    simpa [phaseCell] using memLp_rep_periodCell q0E_ne_top w
  exact integrable_dotL_of_memLp_holder hF hW

#print axioms integrable_projectedPotentialReCutoffMain_pair_rep_cell
#print axioms integrable_projectedPotentialReCutoffShell_pair_rep_cell
#print axioms integrable_projectedPotentialImCutoffMain_pair_rep_cell
#print axioms integrable_projectedPotentialImCutoffShell_pair_rep_cell

end UnforcedLeray.Cons.C03.Concrete

end
