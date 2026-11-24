import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10

/-!
# Part II-b, task `PartII-b:T10/4` (`FreeResponseCongr`): `IsFreeResponse` up to a.e. equality

Source of record: `the November 2 reference manuscript`, lines 1339-1364.

Target: `freeResponseCongr_proof : UnforcedLeray.Short.IIb.FreeResponseCongr`.

Proof outline. Every clause of `IsFreeResponse` is an a.e. notion or a pairing `pairF`, and
`pairF P Φ u` integrates `u` over `Ioc 0 P × Space`, so it only sees `u` up to a.e. equality
(`pairF_congr_ae'`). Periodicity of an a.e.-defined field is preserved under a.e. equality
because the phase shift `(t, y) ↦ (t + P, y)` is measure preserving (`isInYr_congr`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace FreeRespCongrHelp

/-- A pairing with a fixed test only sees its field up to a.e. equality. -/
lemma pairF_congr_ae' (P : ℝ) (Φ u u' : ℝ × Space → CVec3) (h : u =ᵐ[volume] u') :
    pairF P Φ u = pairF P Φ u' := by
  unfold pairF phaseInt
  congr 1
  have h' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)), u x = u' x := by
    rw [← Measure.volume_eq_prod]
    exact h
  have h2 := Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => u z = u' z) h'
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae h2] with t ht
  refine integral_congr_ae ?_
  filter_upwards [ht] with y hy
  simp only [hy]

/-- A phase-periodic field is preserved by a.e. equality (translation by `P` is measure
preserving on `ℝ × Space`, and the phase norm is an integral). -/
lemma isInYr_congr {P r : ℝ} {f g : ℝ × Space → CVec3} (h : f =ᵐ[volume] g)
    (hf : UnforcedLeray.Short.IIb.IsInYr P r f) : UnforcedLeray.Short.IIb.IsInYr P r g := by
  have hmp : MeasurePreserving (fun x : ℝ × Space => (x.1 + P, x.2)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_right (volume : Measure ℝ) P).prod
      (MeasurePreserving.id (volume : Measure Space))
  refine ⟨?_, hf.meas.congr h, ?_⟩
  · filter_upwards [hf.periodic, h, hmp.quasiMeasurePreserving.ae h] with x h1 h2 h3
    rw [← h3, h1, h2]
  · have hn : phaseLpNorm P r g = phaseLpNorm P r f := by
      unfold UnforcedLeray.Short.IIb.phaseLpNorm
      have h' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)), f x = g x := by
        rw [← Measure.volume_eq_prod]
        exact h
      have h2 := Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => f z = g z) h'
      congr 2
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae h2] with t ht
      refine lintegral_congr_ae ?_
      filter_upwards [ht] with y hy
      simp only [hy]
    rw [hn]
    exact hf.finite

end FreeRespCongrHelp

open FreeRespCongrHelp in
theorem freeResponseCongr_proof : UnforcedLeray.Short.IIb.FreeResponseCongr := by
  intro ν μ r P f f' w w' hP hf hw h
  obtain ⟨hmem, ⟨a, haY, hap⟩, ⟨b, hbY, hbp⟩, hsol, heq⟩ := h
  refine ⟨isInYr_congr hw hmem, ⟨a, haY, fun Φ hΦ => ?_⟩, ⟨b, hbY, fun Φ hΦ => ?_⟩,
    fun φ hφ => ?_, fun Φ hΦ => ?_⟩
  · exact (pairF_congr_ae' P _ w w' hw).symm.trans (hap Φ hΦ)
  · exact (pairF_congr_ae' P _ w w' hw).symm.trans (hbp Φ hΦ)
  · exact (pairF_congr_ae' P _ w w' hw).symm.trans (hsol φ hφ)
  · exact (pairF_congr_ae' P _ w w' hw).symm.trans
      ((heq Φ hΦ).trans (pairF_congr_ae' P Φ f f' hf))

end UnforcedLeray.Short.IIb
