import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductMeas
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Joint measurability of the spatial derivative of the rough scalar product. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace

/-- The spatial derivative of the actual scalar product is jointly a.e. strongly measurable.
This uses difference quotients, so no temporal regularity of the background is required. -/
theorem aesm_spatialFderiv_scalarTestBackground {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U) (v : Space) :
    AEStronglyMeasurable
      (fun z : SpaceTime =>
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2 v) volume := by
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let D : ℕ → SpaceTime → ℂ := fun n z =>
    (δ n)⁻¹ • (scalarTestBackground Φ U (z.1, z.2 + δ n • v) -
      scalarTestBackground Φ U (z.1, z.2))
  have hshift (n : ℕ) : AEStronglyMeasurable
      (fun z : SpaceTime => scalarTestBackground Φ U (z.1, z.2 + δ n • v)) volume := by
    have hq : Measure.QuasiMeasurePreserving
        (Prod.map (id : ℝ → ℝ) (fun y : Space => y + δ n • v)) volume volume :=
      QuasiMeasurePreserving.prodMap
        (Measure.QuasiMeasurePreserving.id volume)
        (measurePreserving_add_right volume (δ n • v)).quasiMeasurePreserving
    exact (aesm_scalarTestBackground hΦ hU).comp_quasiMeasurePreserving hq
  have hD (n : ℕ) : AEStronglyMeasurable (D n) volume := by
    have h := ((hshift n).sub (aesm_scalarTestBackground hΦ hU)).const_smul ((δ n)⁻¹)
    have heq : (δ n)⁻¹ •
        ((fun z : SpaceTime => scalarTestBackground Φ U (z.1, z.2 + δ n • v)) -
          fun z : SpaceTime => scalarTestBackground Φ U (z.1, z.2)) = D n := by
      funext z
      simp [D]
    rw [heq] at h
    exact h
  have hδ : Tendsto δ atTop (𝓝[>] (0 : ℝ)) := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_nhdsGT_zero.comp ht
  have hlim (z : SpaceTime) : Tendsto (fun n => D n z) atTop
      (𝓝 (fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2 v)) := by
    have hline := (differentiableAt_scalarTestBackground hΦ hU z.1 z.2).hasFDerivAt.hasLineDerivAt v
    simpa only [D, Function.comp_def] using hline.tendsto_slope_zero_right.comp hδ
  exact aestronglyMeasurable_of_tendsto_ae atTop hD (ae_of_all _ hlim)

#print axioms aesm_spatialFderiv_scalarTestBackground

end UnforcedLeray.Cons.C03.Concrete
