import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.Int

/-!
# `SepIntegrableCongrAE` (PartIII-b:IIIb-D2/3/1/2/3/2/org/1)

Source of record: `the November 2 reference manuscript` 3611-3621 (`sep:resolvent`).
The integrand `sepPhi ν μ T τ i p y` depends on `T` only through `T (τ + 2 log p.1) p.2`.
The map `(l, z) ↦ (τ + 2 log l, z)` is quasi-measure-preserving from `sepRho` to the volume on
`ℝ × Space`: its one-dimensional factor `l ↦ τ + 2 log l` pulls null sets back to null sets of
`(0,1)` (its inverse `t ↦ exp((t - τ)/2)` is locally Lipschitz). Hence a.e. equality of `T₁`
and `T₂` transfers to a `sepRho`-a.e. equality of the integrands.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The one-dimensional phase map `l ↦ τ + 2 log l` is quasi-measure-preserving from
`(0,1)` (Lebesgue measure restricted) to `ℝ`. -/
theorem qmp_log_phase (τ : ℝ) :
    Measure.QuasiMeasurePreserving (fun l : ℝ => τ + 2 * Real.log l)
      (volume.restrict (Ioo (0 : ℝ) 1)) volume := by
  have hgm : Measurable (fun l : ℝ => τ + 2 * Real.log l) :=
    measurable_const.add (measurable_const.mul Real.measurable_log)
  refine ⟨hgm, ?_⟩
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hs0
  rw [Measure.map_apply hgm hs, Measure.restrict_apply (hgm hs)]
  refine measure_mono_null ?_
    (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (f := fun t : ℝ => Real.exp ((t - τ) / 2)) (s := s) (by fun_prop) hs0)
  rintro l ⟨hls, hl⟩
  refine ⟨τ + 2 * Real.log l, hls, ?_⟩
  show Real.exp ((τ + 2 * Real.log l - τ) / 2) = l
  rw [show (τ + 2 * Real.log l - τ) / 2 = Real.log l by ring, Real.exp_log hl.1]

/-- The phase map `(l, z) ↦ (τ + 2 log l, z)` is quasi-measure-preserving from `sepRho`. -/
theorem qmp_phase_prod (τ : ℝ) :
    Measure.QuasiMeasurePreserving (Prod.map (fun l : ℝ => τ + 2 * Real.log l) (id : Space → Space))
      sepRho volume := by
  rw [Measure.volume_eq_prod]
  exact QuasiMeasurePreserving.prodMap (qmp_log_phase τ)
    (Measure.QuasiMeasurePreserving.id _)

theorem sepIntegrableCongrAE : SepIntegrableCongrAE := by
  intro ν μ T₁ T₂ hT y τ hI
  have hae : ∀ᵐ p ∂sepRho, T₁ (τ + 2 * Real.log p.1) p.2 = T₂ (τ + 2 * Real.log p.1) p.2 :=
    (qmp_phase_prod τ).ae hT
  unfold SepIntegrableAt at hI ⊢
  intro i
  refine (hI i).congr ?_
  filter_upwards [hae] with p hp
  simp only [sepPhi, hp]

end UnforcedLeray.Short.PartIIIb.Concrete
