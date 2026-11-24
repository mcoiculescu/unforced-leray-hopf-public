import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductBounds
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductMeas
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductDerivativeMeas
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductIntegrability
import UnforcedLeray.Lib.AxisymmetricB.Bridge

/-! Actual compact-test integrability for the spatial line-IBP pairings of `Φ·U`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0411
open UnforcedLeray.B0412
open UnforcedLeray.Axi

private theorem norm_dotLR_le (a b : CVec3) :
    ‖dotLR a b‖ ≤ ‖dotLR‖ * ‖a‖ * ‖b‖ := by
  calc
    ‖dotLR a b‖ ≤ ‖dotLR a‖ * ‖b‖ := (dotLR a).le_opNorm b
    _ ≤ (‖dotLR‖ * ‖a‖) * ‖b‖ :=
      mul_le_mul_of_nonneg_right (dotLR.le_opNorm a) (norm_nonneg _)

private theorem realC_eq_cplxV : realC = cplxV := by
  funext x
  ext i
  simp [realC_apply, cplxV_apply]

private theorem fderiv_realC_eq_cplxV (x : Space) : fderiv ℝ realC x = cplxV := by
  rw [realC_eq_cplxV]
  exact cplxV.hasFDerivAt.fderiv

/-- For a compactly supported smooth scalar test, each of the three line-IBP pairings with the
actual scalar product `Φ·U` is integrable. The estimates use the actual uniform value/gradient
bound on `U`; they do not introduce an independent integrability premise. -/
theorem scalarTestBackground_linePairings_integrable {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {η : SpaceTime → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (j : Fin 3) :
    Integrable (fun z : SpaceTime =>
      (fderiv ℝ η z (0, EuclideanSpace.single j (1 : ℝ)) : ℝ) •
        scalarTestBackground Φ U z) volume ∧
    Integrable (fun z : SpaceTime => η z •
      fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
        (EuclideanSpace.single j (1 : ℝ))) volume ∧
    Integrable (fun z : SpaceTime => η z • scalarTestBackground Φ U z) volume := by
  obtain ⟨CU, hCU⟩ := hU.bounded
  have hCU0 : 0 ≤ CU := (norm_nonneg _).trans (hCU 0 0).1
  let e : Space := EuclideanSpace.single j (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  let ηD : SpaceTime → ℝ := fun z => fderiv ℝ η z (0, e)
  have hηDc : Continuous ηD :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hηDcomp : HasCompactSupport ηD := by
    refine HasCompactSupport.intro ((hηc.fderiv (𝕜 := ℝ)).isCompact) fun z hz => ?_
    have hzero : fderiv ℝ η z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [ηD, hzero]
  let K : Set SpaceTime := tsupport η ∪ tsupport ηD
  have hK : IsCompact K := hηc.union hηDcomp.isCompact
  have hΦc : Continuous Φ := hΦ.smooth.continuous
  obtain ⟨MΦ, hMΦ0, hMΦ⟩ := exists_norm_bound_on_compact Φ hΦc hK
  let dΦ : SpaceTime → CVec3 := fun z => fderiv ℝ Φ z (0, e)
  have hdΦc : Continuous dΦ :=
    (hΦ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨MDΦ, hMDΦ0, hMDΦ⟩ := exists_norm_bound_on_compact dΦ hdΦc hK
  have hrealnorm (z : SpaceTime) : ‖realC (U z.1 z.2)‖ = ‖U z.1 z.2‖ := by
    rw [realC_eq_cplxV]
    exact norm_cplxV _
  have hGbound : ∀ z ∈ K, ‖scalarTestBackground Φ U z‖ ≤ ‖dotLR‖ * MΦ * CU := by
    intro z hz
    have hUval : ‖U z.1 z.2‖ ≤ CU := (hCU z.1 z.2).1
    calc
      ‖scalarTestBackground Φ U z‖ = ‖dotLR (Φ z) (realC (U z.1 z.2))‖ := rfl
      _ ≤ ‖dotLR‖ * ‖Φ z‖ * ‖realC (U z.1 z.2)‖ := norm_dotLR_le _ _
      _ ≤ ‖dotLR‖ * MΦ * CU := by
        rw [hrealnorm z]
        gcongr
        exact hMΦ z hz
  have hGmeas := aesm_scalarTestBackground hΦ hU
  have hDmeas := aesm_spatialFderiv_scalarTestBackground hΦ hU e
  have h1 := integrable_smul_aesm_of_compactMultiplier_bound
    hηDc hηDcomp hGmeas (C := ‖dotLR‖ * MΦ * CU) (fun z hz => hGbound z (Or.inr hz))
  have h3 := integrable_smul_aesm_of_compactMultiplier_bound
    hη.continuous hηc hGmeas (C := ‖dotLR‖ * MΦ * CU) (fun z hz => hGbound z (Or.inl hz))
  have hDformula (z : SpaceTime) :
      fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2 e =
        dotLR (Φ z) (fderiv ℝ (fun x : Space => realC (U z.1 x)) z.2 e) +
        dotLR (fderiv ℝ (fun x : Space => Φ (z.1, x)) z.2 e)
          (realC (U z.1 z.2)) := by
    simpa only [add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply] using
        fderiv_scalarTestBackground hΦ hU z.1 z.2 e
  have hDbound : ∀ z ∈ tsupport η,
      ‖fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2 e‖ ≤
        ‖dotLR‖ * (MΦ + MDΦ) * CU := by
    intro z hz
    have hzK : z ∈ K := Or.inl hz
    have hUval : ‖U z.1 z.2‖ ≤ CU := (hCU z.1 z.2).1
    have hDU : ‖fderiv ℝ (U z.1) z.2 e‖ ≤ CU := by
      calc
        ‖fderiv ℝ (U z.1) z.2 e‖ ≤ ‖fderiv ℝ (U z.1) z.2‖ * ‖e‖ :=
          (fderiv ℝ (U z.1) z.2).le_opNorm e
        _ = ‖fderiv ℝ (U z.1) z.2‖ := by rw [he, mul_one]
        _ ≤ CU := (hCU z.1 z.2).2
    have hDrealC :
        ‖fderiv ℝ (fun x : Space => realC (U z.1 x)) z.2 e‖ ≤ CU := by
      rw [fderiv_realC_background hU z.1 z.2 e, fderiv_realC_eq_cplxV]
      calc
        ‖cplxV (fderiv ℝ (U z.1) z.2 e)‖ =
            ‖fderiv ℝ (U z.1) z.2 e‖ := norm_cplxV _
        _ ≤ CU := hDU
    have hDΦ :
        ‖fderiv ℝ (fun x : Space => Φ (z.1, x)) z.2 e‖ ≤ MDΦ := by
      rw [fderiv_slice_eq_spatial (hΦ.smooth.differentiable (by simp))]
      exact hMDΦ z hzK
    rw [hDformula z]
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
                  ‖fderiv ℝ (fun x : Space => realC (U z.1 x)) z.2 e‖ := norm_dotLR_le _ _
            _ ≤ ‖dotLR‖ * MΦ * CU := by
              gcongr
              exact hMΦ z hzK
        · calc
            ‖dotLR (fderiv ℝ (fun x : Space => Φ (z.1, x)) z.2 e)
                (realC (U z.1 z.2))‖ ≤
                ‖dotLR‖ *
                  ‖fderiv ℝ (fun x : Space => Φ (z.1, x)) z.2 e‖ *
                  ‖realC (U z.1 z.2)‖ := norm_dotLR_le _ _
            _ ≤ ‖dotLR‖ * MDΦ * CU := by
              rw [hrealnorm z]
              gcongr
      _ = ‖dotLR‖ * (MΦ + MDΦ) * CU := by ring
  have h2 := integrable_smul_aesm_of_compactMultiplier_bound
    hη.continuous hηc hDmeas (C := ‖dotLR‖ * (MΦ + MDΦ) * CU) hDbound
  exact ⟨h1, h2, h3⟩

#print axioms scalarTestBackground_linePairings_integrable

end UnforcedLeray.Cons.C03.Concrete
