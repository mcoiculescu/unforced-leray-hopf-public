import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellOuterPairing
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellLp
import UnforcedLeray.Lib.AxisymmetricB.Bridge

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412
open UnforcedLeray.Axi
open UnforcedLeray.B0411

private theorem realC_eq_cplxV_convection : realC = cplxV := by
  funext x
  ext i
  simp [realC_apply, cplxV_apply]

private theorem fderiv_realC_convection (x : Space) :
    fderiv ℝ realC x = cplxV := by
  rw [realC_eq_cplxV_convection]
  exact cplxV.hasFDerivAt.fderiv

/-- Pointwise product rule for the actual spatial-slice gradient paired with a field. The two
terms are exactly the transpose gradient of the background and the advected test paired with the
background. No temporal differentiability of the background or of the slice gradient is used. -/
theorem scalarSliceGrad_dotL_productRule {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {V : ℝ → SpatialField} (hV : IsBoundedBackground V)
    (W : SpaceTime → CVec3) (z : SpaceTime) :
    dotL (scalarSliceGrad (scalarTestBackground Φ V) z) (W z) =
      dotL (gradUT V Φ z) (W z) +
        dotL (advT W Φ z) (realC (V z.1 z.2)) := by
  let e (j : Fin 3) : Space := EuclideanSpace.single j (1 : ℝ)
  have he (j : Fin 3) : e j = coordinateVector j := by
    ext i
    simp [e, coordinateVector_apply]
  have hderiv (j : Fin 3) :
      fderiv ℝ (fun x : Space => scalarTestBackground Φ V (z.1, x)) z.2 (e j) =
        (∑ i : Fin 3, Φ z i *
          ((fderiv ℝ (V z.1) z.2 (e j) i : ℝ) : ℂ)) +
        (∑ i : Fin 3, dy j Φ z i * ((V z.1 z.2 i : ℝ) : ℂ)) := by
    rw [fderiv_scalarTestBackground hΦ hV z.1 z.2 (e j)]
    have hreal : fderiv ℝ (fun x : Space => realC (V z.1 x)) z.2 (e j) =
        cplxV (fderiv ℝ (V z.1) z.2 (e j)) := by
      rw [fderiv_realC_background hV z.1 z.2 (e j), fderiv_realC_convection]
    have hphi : fderiv ℝ (fun x : Space => Φ (z.1, x)) z.2 (e j) = dy j Φ z := by
      rw [fderiv_slice_eq_spatial (hΦ.smooth.differentiable (by simp))]
      have h := congrArg (fun v : Space => fderiv ℝ Φ z (0, v)) (he j)
      simpa [dy] using h
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, UnforcedLeray.B0411.dotLR_apply, dotL_apply,
      hreal, hphi, realC_apply, cplxV_apply, e, mul_comm]
  calc
    dotL (scalarSliceGrad (scalarTestBackground Φ V) z) (W z) =
        ∑ j : Fin 3,
          ((∑ i : Fin 3, Φ z i *
              ((fderiv ℝ (V z.1) z.2 (e j) i : ℝ) : ℂ)) +
            (∑ i : Fin 3, dy j Φ z i * ((V z.1 z.2 i : ℝ) : ℂ))) * W z j := by
      simp [scalarSliceGrad, dotL_apply, hderiv, e]
    _ = dotL (gradUT V Φ z) (W z) +
        dotL (advT W Φ z) (realC (V z.1 z.2)) := by
      have hgrad : dotL (gradUT V Φ z) (W z) =
          ∑ j : Fin 3, (∑ i : Fin 3, Φ z i *
            ((fderiv ℝ (V z.1) z.2 (e j) i : ℝ) : ℂ)) * W z j := by
        simp [gradUT, dotL_apply, e]
      have hadv : dotL (advT W Φ z) (realC (V z.1 z.2)) =
          ∑ i : Fin 3, (∑ j : Fin 3, W z j * dy j Φ z i) *
            ((V z.1 z.2 i : ℝ) : ℂ) := by
        simp only [advT, dotL_apply, realC_apply, WithLp.ofLp_sum,
          Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
      rw [hgrad, hadv]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ j : Fin 3, (∑ i : Fin 3,
            dy j Φ z i * ((V z.1 z.2 i : ℝ) : ℂ)) * W z j) =
            ∑ j : Fin 3, W z j *
              (∑ i : Fin 3, dy j Φ z i * ((V z.1 z.2 i : ℝ) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = ∑ j : Fin 3, ∑ i : Fin 3,
              (W z j * dy j Φ z i) * ((V z.1 z.2 i : ℝ) : ℂ) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ∑ i : Fin 3, ∑ j : Fin 3,
              (W z j * dy j Φ z i) * ((V z.1 z.2 i : ℝ) : ℂ) := Finset.sum_comm
        _ = ∑ i : Fin 3, (∑ j : Fin 3, W z j * dy j Φ z i) *
              ((V z.1 z.2 i : ℝ) : ℂ) := by
          simp only [Finset.sum_mul]

#print axioms scalarSliceGrad_dotL_productRule

end UnforcedLeray.Cons.C03.Concrete
