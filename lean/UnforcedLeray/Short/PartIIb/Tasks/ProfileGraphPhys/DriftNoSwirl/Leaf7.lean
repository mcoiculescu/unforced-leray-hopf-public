import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6_1
import UnforcedLeray.Short.PartIIb.Bridge.Rep

/-!
# Part II-b, task `PartII-b:T10/6/1/7` (`DriftNoSwirl/Leaf7`): `PhaseFundamental`

Source of record: `the November 2 reference manuscript`, lines 1912-1915.

Two fields `e₁, e₂ ∈ Y_r` with equal pairings against all phase tests have the same
`Y_q`-element `F` (separation `B0411.eq_of_forall_phasePair`, through the representatives of
`Bridge/Rep.lean`). Two jointly measurable representatives of the same element agree a.e.
(Fubini on the slices, then `Measure.ae_prod_iff_ae_ae` on the measurable set where the
strongly measurable versions agree).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Cons.C03.Concrete

namespace PhaseFundHelp

/-- Two jointly measurable representatives of the same element of `Y_q` agree a.e. -/
lemma hasRepY_ae_eq {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] {F : Yq P q}
    {W W' : ℝ × Space → CVec3} (hW : HasRepY F W) (hW' : HasRepY F W') :
    W =ᵐ[volume] W' := by
  set m := hW.meas.mk W with hm_def
  set m' := hW'.meas.mk W' with hm'_def
  have hm : Measurable m := hW.meas.stronglyMeasurable_mk.measurable
  have hm' : Measurable m' := hW'.meas.stronglyMeasurable_mk.measurable
  have hWm : W =ᵐ[volume] m := hW.meas.ae_eq_mk
  have hW'm : W' =ᵐ[volume] m' := hW'.meas.ae_eq_mk
  have hprod : ∀ᵐ x ∂(volume.prod volume : Measure (ℝ × Space)), W x = m x := by
    rw [← Measure.volume_eq_prod]; exact hWm
  have hprod' : ∀ᵐ x ∂(volume.prod volume : Measure (ℝ × Space)), W' x = m' x := by
    rw [← Measure.volume_eq_prod]; exact hW'm
  have hslW := Measure.ae_ae_of_ae_prod hprod
  have hslW' := Measure.ae_ae_of_ae_prod hprod'
  have hmeasSet : MeasurableSet {x : ℝ × Space | m x = m' x} := measurableSet_eq_fun hm hm'
  have hdiag : ∀ᵐ x ∂(volume.prod volume : Measure (ℝ × Space)), m x = m' x := by
    rw [Measure.ae_prod_iff_ae_ae hmeasSet]
    filter_upwards [hW.slice, hW'.slice, hslW, hslW'] with τ a1 a2 a3 a4
    have a12 : (fun y => W (τ, y)) =ᵐ[volume] (fun y => W' (τ, y)) := a1.trans a2.symm
    filter_upwards [a12, a3, a4] with y e e3 e4
    rw [← e3, ← e4]
    exact e
  have hdiag' : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), m x = m' x := by
    rw [Measure.volume_eq_prod]; exact hdiag
  filter_upwards [hWm, hW'm, hdiag'] with x h1 h2 h3
  rw [h1, h2]
  exact h3

end PhaseFundHelp

/-- **`PhaseFundamental`**: phase tests separate points of `Y_r`. -/
theorem phaseFundamental : UnforcedLeray.Short.IIb.PhaseFundamental := by
  intro P r e₁ e₂ hP hr h1 h2 hpair
  haveI : Fact (0 < P) := ⟨hP⟩
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  haveI : Fact (1 ≤ ENNReal.ofReal r) := ⟨ENNReal.one_le_ofReal.2 hr.le⟩
  obtain ⟨F₁, hF₁, -⟩ := exists_hasRepY P r hr0 e₁ h1
  obtain ⟨F₂, hF₂, -⟩ := exists_hasRepY P r hr0 e₂ h2
  have hFeq : F₁ = F₂ := eq_of_forall_phasePair fun Φ hΦ => by
    rw [phasePair_eq_pairF_of_hasRepY F₁ e₁ hF₁ hΦ, phasePair_eq_pairF_of_hasRepY F₂ e₂ hF₂ hΦ]
    exact hpair Φ hΦ
  subst hFeq
  exact PhaseFundHelp.hasRepY_ae_eq hF₁ hF₂

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.phaseFundamental
