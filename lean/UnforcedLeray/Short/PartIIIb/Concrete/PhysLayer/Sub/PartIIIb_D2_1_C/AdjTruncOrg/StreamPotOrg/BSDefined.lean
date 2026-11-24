import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Defs
import Mathlib.MeasureTheory.Integral.Prod

/-!
# `BSDefined`: measurability and periodicity of the Biot-Savart potential

Source `the November 2 reference manuscript` lines 1351-1362.  With the Bochner
integral convention (non-integrable integrals are `0`), measurability follows from Fubini
(`AEStronglyMeasurable.integral_prod_right'`) and periodicity from a.e. periodicity of `Φ`
slice by slice; no Hardy-Littlewood-Sobolev bound is needed for these two statements.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem measurable_bsKernel : Measurable bsKernel := by
  unfold bsKernel
  refine (PiLp.continuous_toLp 2 _).measurable.comp ?_
  refine measurable_pi_lambda _ fun i => ?_
  exact Complex.measurable_ofReal.comp (by fun_prop)

theorem continuous_crossC' : Continuous (fun p : CVec3 × CVec3 => crossC p.1 p.2) := by
  unfold crossC
  fun_prop

set_option maxHeartbeats 1000000 in
theorem bsDefined : BSDefined := by
  intro P hP Φ hΦ _
  have hqmp : Measure.QuasiMeasurePreserving
      (fun p : (ℝ × Space) × Space => (p.1.1, p.2))
      (volume : Measure ((ℝ × Space) × Space)) (volume : Measure (ℝ × Space)) := by
    have h1 : Measure.QuasiMeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × Space) × Space ≃ᵐ
        ℝ × Space × Space) (volume.prod volume) (volume.prod (volume.prod volume)) := by
      exact (MeasureTheory.measurePreserving_prodAssoc _ _ _).quasiMeasurePreserving
    have h2 : Measure.QuasiMeasurePreserving
        (Prod.map (id : ℝ → ℝ) (Prod.snd : Space × Space → Space))
        (volume.prod (volume.prod volume)) (volume.prod volume) :=
      QuasiMeasurePreserving.prodMap
        (Measure.QuasiMeasurePreserving.id _) Measure.quasiMeasurePreserving_snd
    exact h2.comp h1
  refine ⟨?_, ?_⟩
  · have hA : AEStronglyMeasurable (fun p : (ℝ × Space) × Space => Φ (p.1.1, p.2)) volume :=
      hΦ.meas.comp_quasiMeasurePreserving hqmp
    have hsub : Measurable (fun p : (ℝ × Space) × Space => p.1.2 - p.2) :=
      (measurable_snd.comp measurable_fst).sub measurable_snd
    have hK : AEStronglyMeasurable (fun p : (ℝ × Space) × Space => bsKernel (p.1.2 - p.2))
        volume :=
      (measurable_bsKernel.comp hsub).aestronglyMeasurable
    have hF : AEStronglyMeasurable (fun p : (ℝ × Space) × Space =>
        crossC (Φ (p.1.1, p.2)) (bsKernel (p.1.2 - p.2))) volume :=
      continuous_crossC'.comp_aestronglyMeasurable (hA.prodMk hK)
    exact AEStronglyMeasurable.integral_prod_right' (f := fun p : (ℝ × Space) × Space =>
        crossC (Φ (p.1.1, p.2)) (bsKernel (p.1.2 - p.2))) hF
  · have hp := hΦ.periodic
    have hp' : ∀ᵐ x : ℝ × Space, Φ (x.1 + P, x.2) = Φ x := hp
    rw [Measure.volume_eq_prod] at hp'
    have h1 := Measure.ae_ae_of_ae_prod hp'
    have h2 : ∀ᵐ x : ℝ × Space, ∀ᵐ z : Space, Φ (x.1 + P, z) = Φ (x.1, z) :=
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space))).ae h1
    filter_upwards [h2] with x hx
    unfold bsPot
    refine integral_congr_ae ?_
    filter_upwards [hx] with z hz
    simp only [hz]

end UnforcedLeray.Short.PartIIIb.Concrete
