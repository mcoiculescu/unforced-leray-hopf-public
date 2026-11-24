import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialCellLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductBounds
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductDerivativeMeas
import UnforcedLeray.Lib.AxisymmetricB.Bridge

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412
open UnforcedLeray.B0411
open UnforcedLeray.Axi

private theorem norm_dotLR_le_cell (a b : CVec3) :
    ‖dotLR a b‖ ≤ ‖dotLR‖ * ‖a‖ * ‖b‖ := by
  calc
    ‖dotLR a b‖ ≤ ‖dotLR a‖ * ‖b‖ := (dotLR a).le_opNorm b
    _ ≤ (‖dotLR‖ * ‖a‖) * ‖b‖ :=
      mul_le_mul_of_nonneg_right (dotLR.le_opNorm a) (norm_nonneg _)

private theorem realC_eq_cplxV_cell : realC = cplxV := by
  funext x
  ext i
  simp [realC_apply, cplxV_apply]

private theorem fderiv_realC_eq_cplxV_cell (x : Space) :
    fderiv ℝ realC x = cplxV := by
  rw [realC_eq_cplxV_cell]
  exact cplxV.hasFDerivAt.fderiv

/-- The actual compact-test/background scalar product is in finite `L^p` on each phase cell,
from the background's genuine uniform bound and the test's compact spatial support. -/
theorem scalarTestBackground_memLp_cell {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    MemLp (fun z : SpaceTime => scalarTestBackground Φ U z) p
      (volume.restrict (phaseCell P)) := by
  obtain ⟨R, hspace⟩ := hΦ.bounded_support
  have hΦc : Continuous Φ := hΦ.smooth.continuous
  let K : Set SpaceTime := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨MΦ, hMΦ0, hMΦ⟩ := exists_norm_bound_on_compact Φ hΦc (by simpa [K] using hK)
  obtain ⟨CU, hCU⟩ := hU.bounded
  have hCU0 : 0 ≤ CU := (norm_nonneg _).trans (hCU 0 0).1
  have hbound : ∀ z ∈ K, ‖scalarTestBackground Φ U z‖ ≤ ‖dotLR‖ * MΦ * CU := by
    intro z hz
    have hUval : ‖U z.1 z.2‖ ≤ CU := (hCU z.1 z.2).1
    have hrealnorm : ‖realC (U z.1 z.2)‖ = ‖U z.1 z.2‖ := by
      rw [realC_eq_cplxV_cell]
      exact norm_cplxV _
    have hzΦ : z ∈ K := hz
    calc
      ‖scalarTestBackground Φ U z‖ = ‖dotLR (Φ z) (realC (U z.1 z.2))‖ := rfl
      _ ≤ ‖dotLR‖ * ‖Φ z‖ * ‖realC (U z.1 z.2)‖ := norm_dotLR_le_cell _ _
      _ ≤ ‖dotLR‖ * MΦ * CU := by
        rw [hrealnorm]
        gcongr
        exact hMΦ z hzΦ
  have hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ y : Space, R < ‖y‖ →
      scalarTestBackground Φ U (τ, y) = 0 := by
    intro τ hτ y hy
    have hΦ0 := hspace τ y hy
    simp [scalarTestBackground, hΦ0]
  have hbound' : ∃ C : ℝ, ∀ z ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R,
      ‖scalarTestBackground Φ U z‖ ≤ C := by
    exact ⟨‖dotLR‖ * MΦ * CU, fun z hz => hbound z (by simpa [K] using hz)⟩
  exact memLp_on_phaseCell_of_spatialSupport (P := P) (R := R) (p := p)
    hp (aesm_scalarTestBackground hΦ hU) hbound' hzero

/-- Every actual spatial derivative of the compact-test/background product is in finite `L^p`
on a phase cell, using the bounded `U,∇U` supplied by the concrete background. -/
theorem scalarTestBackground_spatialDerivative_memLp_cell {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (j : Fin 3) :
    MemLp (fun z : SpaceTime =>
      fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
        (EuclideanSpace.single j (1 : ℝ))) p (volume.restrict (phaseCell P)) := by
  obtain ⟨RΦ, hspaceΦ⟩ := hΦ.bounded_support
  have hdy : IsPhaseTest P (PhaseSpace.dy j Φ) := hΦ.dy j
  obtain ⟨Rdy, hspaceDy⟩ := hdy.bounded_support
  let R : ℝ := max RΦ Rdy
  have hRΦ : RΦ ≤ R := le_max_left _ _
  have hRdy : Rdy ≤ R := le_max_right _ _
  have hΦc : Continuous Φ := hΦ.smooth.continuous
  obtain ⟨CU, hCU⟩ := hU.bounded
  have hCU0 : 0 ≤ CU := (norm_nonneg _).trans (hCU 0 0).1
  let e : Space := EuclideanSpace.single j (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  let K : Set SpaceTime := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨MΦ, hMΦ0, hMΦ⟩ := exists_norm_bound_on_compact Φ hΦc (by simpa [K] using hK)
  let dΦ : SpaceTime → CVec3 := fun z => fderiv ℝ Φ z (0, e)
  have hdΦc : Continuous dΦ :=
    (hΦ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨MDΦ, hMDΦ0, hMDΦ⟩ := exists_norm_bound_on_compact dΦ hdΦc
    (by simpa [K] using hK)
  have hrealnorm (z : SpaceTime) : ‖realC (U z.1 z.2)‖ = ‖U z.1 z.2‖ := by
    rw [realC_eq_cplxV_cell]
    exact norm_cplxV _
  have hformula (z : SpaceTime) :
      fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2 e =
        dotLR (Φ z) (fderiv ℝ (fun x : Space => realC (U z.1 x)) z.2 e) +
        dotLR (fderiv ℝ (fun x : Space => Φ (z.1, x)) z.2 e)
          (realC (U z.1 z.2)) := by
    simpa only [add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply] using
        fderiv_scalarTestBackground hΦ hU z.1 z.2 e
  have hbound : ∃ C : ℝ, ∀ z ∈ K,
      ‖fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2 e‖ ≤ C := by
    refine ⟨‖dotLR‖ * (MΦ + MDΦ) * CU, ?_⟩
    intro z hz
    have hUval : ‖U z.1 z.2‖ ≤ CU := (hCU z.1 z.2).1
    have hDU : ‖fderiv ℝ (U z.1) z.2 e‖ ≤ CU := by
      calc
        ‖fderiv ℝ (U z.1) z.2 e‖ ≤ ‖fderiv ℝ (U z.1) z.2‖ * ‖e‖ :=
          (fderiv ℝ (U z.1) z.2).le_opNorm e
        _ = ‖fderiv ℝ (U z.1) z.2‖ := by rw [he, mul_one]
        _ ≤ CU := (hCU z.1 z.2).2
    have hDrealC :
        ‖fderiv ℝ (fun x : Space => realC (U z.1 x)) z.2 e‖ ≤ CU := by
      rw [fderiv_realC_background hU z.1 z.2 e, fderiv_realC_eq_cplxV_cell]
      calc
        ‖cplxV (fderiv ℝ (U z.1) z.2 e)‖ = ‖fderiv ℝ (U z.1) z.2 e‖ := norm_cplxV _
        _ ≤ CU := hDU
    have hDΦ :
        ‖fderiv ℝ (fun x : Space => Φ (z.1, x)) z.2 e‖ ≤ MDΦ := by
      rw [fderiv_slice_eq_spatial (hΦ.smooth.differentiable (by simp))]
      have hzK : z ∈ K := hz
      exact hMDΦ z hzK
    rw [hformula z]
    calc
      ‖dotLR (Φ z) (fderiv ℝ (fun x : Space => realC (U z.1 x)) z.2 e) +
          dotLR (fderiv ℝ (fun x : Space => Φ (z.1, x)) z.2 e)
            (realC (U z.1 z.2))‖ ≤
          ‖dotLR (Φ z) (fderiv ℝ (fun x : Space => realC (U z.1 x)) z.2 e)‖ +
          ‖dotLR (fderiv ℝ (fun x : Space => Φ (z.1, x)) z.2 e)
            (realC (U z.1 z.2))‖ := norm_add_le _ _
      _ ≤ ‖dotLR‖ * MΦ * CU + ‖dotLR‖ * MDΦ * CU := by
        apply add_le_add
        · calc
            ‖dotLR (Φ z) (fderiv ℝ (fun x : Space => realC (U z.1 x)) z.2 e)‖ ≤
                ‖dotLR‖ * ‖Φ z‖ *
                  ‖fderiv ℝ (fun x : Space => realC (U z.1 x)) z.2 e‖ := norm_dotLR_le_cell _ _
            _ ≤ ‖dotLR‖ * MΦ * CU := by
              gcongr
              exact hMΦ z hz
        · calc
            ‖dotLR (fderiv ℝ (fun x : Space => Φ (z.1, x)) z.2 e)
                (realC (U z.1 z.2))‖ ≤
                ‖dotLR‖ *
                  ‖fderiv ℝ (fun x : Space => Φ (z.1, x)) z.2 e‖ *
                  ‖realC (U z.1 z.2)‖ := norm_dotLR_le_cell _ _
            _ ≤ ‖dotLR‖ * MDΦ * CU := by
              rw [hrealnorm z]
              gcongr
      _ = ‖dotLR‖ * (MΦ + MDΦ) * CU := by ring
  have hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ y : Space, R < ‖y‖ →
      fderiv ℝ (fun x : Space => scalarTestBackground Φ U (τ, x)) y e = 0 := by
    intro τ hτ y hy
    have hΦ0 := hspaceΦ τ y (lt_of_le_of_lt hRΦ hy)
    have hdy0 := hspaceDy τ y (lt_of_le_of_lt hRdy hy)
    have hgrad : fderiv ℝ (fun x : Space => Φ (τ, x)) y e = 0 := by
      rw [fderiv_slice_eq_spatial (hΦ.smooth.differentiable (by simp))]
      have hecoord : e = coordinateVector j := by
        ext i
        simp [e, coordinateVector]
      rw [hecoord]
      simpa [PhaseSpace.dy] using hdy0
    rw [hformula (τ, y), hΦ0, hgrad]
    simp
  exact memLp_on_phaseCell_of_spatialSupport (P := P) (R := R) (p := p)
    hp (aesm_spatialFderiv_scalarTestBackground hΦ hU e) hbound hzero

#print axioms scalarTestBackground_memLp_cell
#print axioms scalarTestBackground_spatialDerivative_memLp_cell

end UnforcedLeray.Cons.C03.Concrete
