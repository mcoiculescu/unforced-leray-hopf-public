import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Infra.JointMeasurableRep

/-!
# Part III-a, leaf `PartIII-a:T18/2/4/2/1`: joint measurable representative

Target: `UnforcedLeray.Short.IIIa.JointRepVecC` (`Sub/T18_2_4_2.lean`).
Source of record: `the November 2 reference manuscript`, lines 3442-3465.

Proof: apply `Infra/JointMeasurableRep.lean`,
`exists_stronglyMeasurable_rep_of_continuousOn`, to each of the two paths on `Ioi 0` with
`μ = Cyl.cellμ c`, then take `F = F₁ + i F₂` componentwise.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem jointRepVecC : UnforcedLeray.Short.IIIa.JointRepVecC := by
  unfold JointRepVecC
  intro c _hc γ₁ γ₂ h₁ h₂
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := fact_one_le_two_ennreal
  obtain ⟨F₁, hF₁m, hF₁⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      (μ := UnforcedLeray.Cyl.cellμ c) measurableSet_Ioi h₁
  obtain ⟨F₂, hF₂m, hF₂⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      (μ := UnforcedLeray.Cyl.cellμ c) measurableSet_Ioi h₂
  refine ⟨fun p i => ((F₁ p i : ℝ) : ℂ) + Complex.I * ((F₂ p i : ℝ) : ℂ), ?_, ?_⟩
  · intro i
    have hc₁ : Continuous fun v : UnforcedLeray.Cyl.Vec2 => v i := by fun_prop
    have hc₂ : Continuous fun v : UnforcedLeray.Cyl.Vec2 => v i := by fun_prop
    have m₁ : Measurable fun p => F₁ p i := (hc₁.comp_stronglyMeasurable hF₁m).measurable
    have m₂ : Measurable fun p => F₂ p i := (hc₂.comp_stronglyMeasurable hF₂m).measurable
    exact (Complex.measurable_ofReal.comp m₁).add
      (measurable_const.mul (Complex.measurable_ofReal.comp m₂))
  · intro t ht
    rw [← cellμ_eq c]
    have e₁ := hF₁ t (Set.mem_Ioi.mpr ht)
    have e₂ := hF₂ t (Set.mem_Ioi.mpr ht)
    filter_upwards [e₁, e₂] with x hx₁ hx₂
    have h₁' : F₁ (t, x) = γ₁ t x := hx₁
    have h₂' : F₂ (t, x) = γ₂ t x := hx₂
    intro i
    simp only [cplxOf, h₁', h₂']

end UnforcedLeray.Short.IIIa

end
