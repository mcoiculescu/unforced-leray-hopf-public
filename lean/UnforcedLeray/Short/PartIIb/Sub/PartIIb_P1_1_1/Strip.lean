import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1_1

/-!
# `PartII-b:P1/1/1`, step (3a): the inverse-chart profile on one period

Source `the November 2 reference manuscript` 1902-1906.  The body of
`Axi.mem_range_Jv` (`Lib/AxisymmetricB/Unitary.lean`) without the `L²` hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Axi

theorem blrStrip {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (W : ℝ × Space → Space) (hW : Measurable W)
    (hsym : ∀ᵐ τ : ℝ, IsAxisymmetricNoSwirl fun y => W (τ, y)) :
    ∃ B₀ : ℝ × (ℝ × ℝ) → Merid, Measurable B₀ ∧
      liftFun R c B₀ =ᵐ[phaseμ P] W := by
  have hsym' : ∀ᵐ τ ∂((ENNReal.ofReal P)⁻¹ • volume.restrict (Ioc (0 : ℝ) P)),
      IsAxisymmetricNoSwirl fun y => W (τ, y) :=
    Measure.ae_smul_measure (ae_restrict_of_ae hsym) _
  have hrep : (W : ℝ × Space → Space) =ᵐ[phaseμ P] fun x =>
      avgR W (x.1, mer x.2) • eR x.2 + avgZ W (x.1, mer x.2) • e3 :=
    ae_eq_avgLift hW hsym'
  have hbm : Measurable (invLift R P (avgMer W)) :=
    measurable_invLift R P (measurable_avgMer hW)
  have hτ : ∀ᵐ x ∂phaseμ P, x.1 ∈ Ioc 0 P :=
    Measure.quasiMeasurePreserving_fst.ae
      (Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _)
  have hy : ∀ᵐ x ∂phaseμ P, x.2 ∉ axis :=
    Measure.quasiMeasurePreserving_snd.ae ae_not_mem_axis
  refine ⟨invLift R P (avgMer W), hbm, ?_⟩
  filter_upwards [hrep, hτ, hy] with x h1 h2 h3
  obtain ⟨τ, y⟩ := x
  rw [h1, liftFun_invLift hR hc hP _ h2 h3, frameL_apply]
  rfl

end UnforcedLeray.Short.IIb
