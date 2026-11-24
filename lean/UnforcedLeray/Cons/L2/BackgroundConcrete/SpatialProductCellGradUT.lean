import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellConvectionPointwise

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

private theorem norm_dotLR_gradUT (a b : CVec3) :
    ‖dotLR a b‖ ≤ ‖dotLR‖ * ‖a‖ * ‖b‖ := by
  calc
    ‖dotLR a b‖ ≤ ‖dotLR a‖ * ‖b‖ := (dotLR a).le_opNorm b
    _ ≤ (‖dotLR‖ * ‖a‖) * ‖b‖ :=
      mul_le_mul_of_nonneg_right (dotLR.le_opNorm a) (norm_nonneg _)

private theorem realC_eq_cplxV_gradUT : realC = cplxV := by
  funext x
  ext i
  simp [realC_apply, cplxV_apply]

/-- Each actual coordinate of the transpose-gradient test has compact spatial support, is jointly
measurable, and is uniformly bounded by the concrete background value/gradient bounds. -/
theorem memLp_gradUT_coordinate_cell {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {V : ℝ → SpatialField} (hV : IsBoundedBackground V)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (j : Fin 3) :
    MemLp (fun z : SpaceTime => gradUT V Φ z j) p
      (volume.restrict (phaseCell P)) := by
  obtain ⟨R, hspace⟩ := hΦ.bounded_support
  have hΦc : Continuous Φ := hΦ.smooth.continuous
  let K : Set SpaceTime := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨MΦ, hMΦ0, hMΦ⟩ := exists_norm_bound_on_compact Φ hΦc (by simpa [K] using hK)
  obtain ⟨CV, hCV⟩ := hV.bounded
  have hCV0 : 0 ≤ CV := (norm_nonneg _).trans (hCV 0 0).1
  let e : Space := EuclideanSpace.single j (1 : ℝ)
  let g : SpaceTime → ℂ := fun z =>
    dotLR (Φ z) (cplxV (fderiv ℝ (V z.1) z.2 e))
  have hgEq (z : SpaceTime) : g z = gradUT V Φ z j := by
    simp [g, gradUT, dotLR_apply, dotL_apply, cplxV_apply, e]
  have hD : AEStronglyMeasurable
      (fun z : SpaceTime => fderiv ℝ (V z.1) z.2 e) volume :=
    aeStronglyMeasurable_backgroundFderiv V hV e
  have htuple : AEStronglyMeasurable
      (fun z : SpaceTime => (z, (Φ z, fderiv ℝ (V z.1) z.2 e))) volume := by
    exact aestronglyMeasurable_id.prodMk (hΦc.aestronglyMeasurable.prodMk hD)
  have hA : Continuous (fun b : SpaceTime × (CVec3 × Space) => dotLR b.2.1) :=
    dotLR.continuous.comp (continuous_fst.comp continuous_snd)
  have hmap : Continuous (fun b : SpaceTime × (CVec3 × Space) =>
      dotLR b.2.1 (cplxV b.2.2)) :=
    hA.clm_apply (cplxV.continuous.comp (continuous_snd.comp continuous_snd))
  have hg : AEStronglyMeasurable g volume := by
    have h := hmap.comp_aestronglyMeasurable htuple
    have heq : (fun z : SpaceTime =>
        dotLR (Φ z) (cplxV (fderiv ℝ (V z.1) z.2 e))) = g := rfl
    exact h.congr (ae_of_all _ fun z => congrFun heq z)
  have hbound : ∃ C : ℝ, ∀ z ∈ K, ‖g z‖ ≤ C := by
    refine ⟨‖dotLR‖ * MΦ * CV, ?_⟩
    intro z hz
    have hΦz : ‖Φ z‖ ≤ MΦ := hMΦ z (by simpa [K] using hz)
    have hDop : ‖fderiv ℝ (V z.1) z.2‖ ≤ CV := (hCV z.1 z.2).2
    have he : ‖e‖ = 1 := by simp [e]
    have hDvec : ‖fderiv ℝ (V z.1) z.2 e‖ ≤ CV := by
      calc
        ‖fderiv ℝ (V z.1) z.2 e‖ ≤ ‖fderiv ℝ (V z.1) z.2‖ * ‖e‖ :=
          (fderiv ℝ (V z.1) z.2).le_opNorm e
        _ = ‖fderiv ℝ (V z.1) z.2‖ := by rw [he, mul_one]
        _ ≤ CV := hDop
    have hCplx : ‖cplxV (fderiv ℝ (V z.1) z.2 e)‖ ≤ CV := by
      rw [norm_cplxV]
      exact hDvec
    calc
      ‖g z‖ ≤ ‖dotLR‖ * ‖Φ z‖ *
          ‖cplxV (fderiv ℝ (V z.1) z.2 e)‖ := norm_dotLR_gradUT _ _
      _ ≤ ‖dotLR‖ * MΦ * CV := by gcongr
  have hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ y : Space, R < ‖y‖ → g (τ, y) = 0 := by
    intro τ hτ y hy
    have hΦ0 := hspace τ y hy
    simp [g, hΦ0]
  have hgMem : MemLp g p (volume.restrict (phaseCell P)) :=
    memLp_on_phaseCell_of_spatialSupport hp hg hbound hzero
  have heq : g =ᵐ[volume.restrict (phaseCell P)]
      (fun z => gradUT V Φ z j) := ae_of_all _ hgEq
  exact (memLp_congr_ae heq).mp hgMem

/-- The full actual transpose-gradient test is in every finite `Lᵖ` on a phase cell. -/
theorem memLp_gradUT_cell {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {V : ℝ → SpatialField} (hV : IsBoundedBackground V)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    MemLp (fun z : SpaceTime => gradUT V Φ z) p
      (volume.restrict (phaseCell P)) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  have hcoord (j : Fin 3) : MemLp (fun z : SpaceTime => gradUT V Φ z j) p μ :=
    memLp_gradUT_coordinate_cell hΦ hV hp j
  have hterm (j : Fin 3) : MemLp (fun z : SpaceTime =>
      gradUT V Φ z j • EuclideanSpace.single j (1 : ℂ)) p μ := by
    let A : ℂ →L[ℝ] CVec3 := ContinuousLinearMap.smulRight
      (1 : ℂ →L[ℝ] ℂ) (EuclideanSpace.single j (1 : ℂ))
    exact (hcoord j).continuousLinearMap_comp A
  have hsum := memLp_finsetSum' Finset.univ (fun j _ => hterm j)
  have heq : (fun z : SpaceTime => gradUT V Φ z) =ᵐ[μ]
      (fun z => ∑ j : Fin 3,
        gradUT V Φ z j • EuclideanSpace.single j (1 : ℂ)) := by
    filter_upwards with z
    ext i
    simp [Finset.sum_apply, PiLp.smul_apply, Pi.single_apply]
  exact (memLp_congr_ae heq).mpr hsum

#print axioms memLp_gradUT_coordinate_cell
#print axioms memLp_gradUT_cell

end UnforcedLeray.Cons.C03.Concrete
