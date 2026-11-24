import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellVectorSupport
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellIntegratedConvection

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412
open UnforcedLeray.B0411
open UnforcedLeray.Axi

private theorem realC_eq_cplxV_advT : realC = Axi.cplxV := by
  funext x
  ext i
  simp [realC_apply, Axi.cplxV_apply]

private def advMapCell (Φ : ℝ × Space → CVec3) (z : SpaceTime) :
    CVec3 →L[ℂ] CVec3 :=
  ∑ j : Fin 3,
    (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).smulRight (dy j Φ z)

/-- The actual background advection of a compact phase test belongs to every finite Lp on the
phase cell. This is the concrete compact-support and bounded-background supplier needed to use
the pointwise transpose identity in the phase integral. -/
theorem memLp_advT_background_cell {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {V : ℝ → SpatialField} (hV : IsBoundedBackground V)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    MemLp (fun z : SpaceTime => advT (fun z => realC (V z.1 z.2)) Φ z) p
      (volume.restrict (phaseCell P)) := by
  obtain ⟨R0, hspace0⟩ := (hΦ.dy 0).bounded_support
  obtain ⟨R1, hspace1⟩ := (hΦ.dy 1).bounded_support
  obtain ⟨R2, hspace2⟩ := (hΦ.dy 2).bounded_support
  let R : ℝ := max R0 (max R1 R2)
  have hR0 : R0 ≤ R := le_max_left _ _
  have hR1 : R1 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR2 : R2 ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hΦc : Continuous Φ := hΦ.smooth.continuous
  let K : Set SpaceTime := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hdy0c : Continuous (dy 0 Φ) := (hΦ.dy 0).smooth.continuous
  have hdy1c : Continuous (dy 1 Φ) := (hΦ.dy 1).smooth.continuous
  have hdy2c : Continuous (dy 2 Φ) := (hΦ.dy 2).smooth.continuous
  obtain ⟨MD0, hMD00, hMD0⟩ := exists_norm_bound_on_compact (dy 0 Φ) hdy0c
    (by simpa [K] using hK)
  obtain ⟨MD1, hMD10, hMD1⟩ := exists_norm_bound_on_compact (dy 1 Φ) hdy1c
    (by simpa [K] using hK)
  obtain ⟨MD2, hMD20, hMD2⟩ := exists_norm_bound_on_compact (dy 2 Φ) hdy2c
    (by simpa [K] using hK)
  obtain ⟨CV, hCV⟩ := hV.bounded
  have hCV0 : 0 ≤ CV := (norm_nonneg _).trans (hCV 0 0).1
  let A : SpaceTime → CVec3 →L[ℂ] CVec3 := advMapCell Φ
  have hterm (j : Fin 3) : Continuous (fun z : SpaceTime =>
      (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).smulRight (dy j Φ z)) := by
    have hdy : Continuous (dy j Φ) := (hΦ.dy j).smooth.continuous
    exact (ContinuousLinearMap.smulRightL ℂ CVec3 CVec3
      (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ)).continuous.comp hdy
  have hAc : Continuous A := continuous_finsetSum Finset.univ fun j hj => hterm j
  have hrealC : AEStronglyMeasurable
      (fun z : SpaceTime => realC (V z.1 z.2)) volume := by
    have hC : Continuous (Axi.cplxV : Space →L[ℝ] CVec3) := Axi.cplxV.continuous
    have h := hC.comp_aestronglyMeasurable hV.measurable
    have heq : (fun z : SpaceTime => Axi.cplxV (V z.1 z.2)) =
        (fun z => realC (V z.1 z.2)) := by
      funext z
      rw [realC_eq_cplxV_advT]
    exact h.congr (ae_of_all _ fun z => congrFun heq z)
  have hmap : AEStronglyMeasurable
      (fun z : SpaceTime => A z (realC (V z.1 z.2))) volume := by
    have htuple : AEStronglyMeasurable
        (fun z : SpaceTime => (A z, realC (V z.1 z.2))) volume :=
      hAc.aestronglyMeasurable.prodMk hrealC
    have heval : Continuous (fun a : (CVec3 →L[ℂ] CVec3) × CVec3 => a.1 a.2) :=
      isBoundedBilinearMap_apply.continuous.comp (continuous_fst.prodMk continuous_snd)
    exact heval.comp_aestronglyMeasurable htuple
  have hEq (z : SpaceTime) : A z (realC (V z.1 z.2)) =
      advT (fun z => realC (V z.1 z.2)) Φ z := by
    ext i
    simp [A, advMapCell, advT, ContinuousLinearMap.smulRight_apply,
      PiLp.proj_apply, Finset.sum_apply]
  have hbound : ∃ C : ℝ, ∀ z ∈ K,
      ‖advT (fun z => realC (V z.1 z.2)) Φ z‖ ≤ C := by
    refine ⟨3 * CV * max MD0 (max MD1 MD2), ?_⟩
    intro z hz
    have hVcoord (j : Fin 3) : ‖realC (V z.1 z.2) j‖ ≤ CV := by
      calc
        ‖realC (V z.1 z.2) j‖ ≤ ‖realC (V z.1 z.2)‖ :=
          PiLp.norm_apply_le (realC (V z.1 z.2)) j
        _ = ‖V z.1 z.2‖ := by
          rw [realC_eq_cplxV_advT, norm_cplxV]
        _ ≤ CV := (hCV z.1 z.2).1
    have hdy (j : Fin 3) : ‖dy j Φ z‖ ≤ max MD0 (max MD1 MD2) := by
      fin_cases j
      · exact (hMD0 z (by simpa [K] using hz)).trans (le_max_left _ _)
      · exact (hMD1 z (by simpa [K] using hz)).trans
          (le_trans (le_max_left _ _) (le_max_right _ _))
      · exact (hMD2 z (by simpa [K] using hz)).trans
          (le_trans (le_max_right _ _) (le_max_right _ _))
    have hsum : ‖advT (fun z => realC (V z.1 z.2)) Φ z‖ ≤
        ∑ j : Fin 3, CV * max MD0 (max MD1 MD2) := by
      rw [advT]
      calc
        ‖∑ j : Fin 3, realC (V z.1 z.2) j • dy j Φ z‖ ≤
            ∑ j : Fin 3, ‖realC (V z.1 z.2) j • dy j Φ z‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin 3, CV * max MD0 (max MD1 MD2) :=
          Finset.sum_le_sum fun j hj => by
            rw [norm_smul]
            exact mul_le_mul (hVcoord j) (hdy j) (norm_nonneg _) hCV0
    simpa [mul_assoc] using hsum
  have hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ y : Space, R < ‖y‖ →
      advT (fun z => realC (V z.1 z.2)) Φ (τ, y) = 0 := by
    intro τ hτ y hy
    have h0 := hspace0 τ y (lt_of_le_of_lt hR0 hy)
    have h1 := hspace1 τ y (lt_of_le_of_lt hR1 hy)
    have h2 := hspace2 τ y (lt_of_le_of_lt hR2 hy)
    rw [advT]
    apply Finset.sum_eq_zero
    intro j hj
    fin_cases j <;> simp [h0, h1, h2]
  have hmemA : MemLp (fun z : SpaceTime => A z (realC (V z.1 z.2))) p
      (volume.restrict (phaseCell P)) :=
    memLp_vector_on_phaseCell_of_spatialSupport hp hmap hbound (by
      intro τ hτ y hy
      rw [hEq]
      exact hzero τ hτ y hy)
  have heqMem : (fun z : SpaceTime => A z (realC (V z.1 z.2))) =ᵐ[
      volume.restrict (phaseCell P)]
      (fun z => advT (fun z => realC (V z.1 z.2)) Φ z) := ae_of_all _ hEq
  exact (memLp_congr_ae heqMem).mp hmemA

#print axioms memLp_advT_background_cell

end UnforcedLeray.Cons.C03.Concrete
