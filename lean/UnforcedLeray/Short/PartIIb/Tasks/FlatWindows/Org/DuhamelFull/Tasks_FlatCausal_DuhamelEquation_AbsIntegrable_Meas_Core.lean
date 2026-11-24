import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Meas.Core
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7

/-!
# Helpers for `PartII-b:T12/7/7/1` (`dfe_deqAbsMeas`): measurability of the `dfe_DeqAbsIntegrable` integrand

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

The integrand `deqAbsIntegrand ν μ G Ψ` is built from `flatHeat (ν (s - t)) (G (t, ·)) z`. For a
strongly measurable representative `G'` the joint map `(t, (s, z)) ↦ flatHeat ... ` is strongly
measurable (parametric Bochner integral, as in `DuhamelMeasurable.lean`). Replacing `G` by `G'`
changes the integrand only on a null set (Fubini and translation invariance in `w`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The integrand of `dfe_DeqAbsIntegrable` for a strongly measurable `G'` is measurable. -/
theorem dfe_deqam_integrand_measurable (ν : ℝ) (μ : ℂ) (Ψ : Coord → Fin 2 → ℝ)
    (hΨ : IsPlanarTestDfe Ψ) {G' : CProf} (hG' : StronglyMeasurable G') :
    Measurable (deqAbsIntegrand ν μ G' Ψ) := by
  have hΦ := (deqam_flatHeat_stronglyMeasurable ν hG').measurable
  have hT : ∀ i : Fin 2, Continuous (fun x => flatTranspose ν μ Ψ x i) :=
    fun i => (dfe_deqTransposeTest ν μ hΨ i).1
  have hset : MeasurableSet {p : ℝ × Coord | 0 < p.1 ∧ p.1 < p.2.1} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst (measurable_fst.comp measurable_snd))
  unfold deqAbsIntegrand
  refine Measurable.ite hset ?_ measurable_const
  have h1 : Measurable (fun p : ℝ × Coord => ‖(((p.1 / p.2.1 : ℝ) : ℂ) ^ μ)‖) :=
    ((Complex.measurable_ofReal.comp
      (measurable_fst.div (measurable_fst.comp measurable_snd))).pow_const μ).norm
  have h2 : Measurable (fun p : ℝ × Coord => p.1⁻¹) := measurable_fst.inv
  have h3 : Measurable (fun p : ℝ × Coord =>
      ‖flatHeat (ν * (p.2.1 - p.1)) (fun w => G' (p.1, w)) p.2.2‖) := hΦ.norm
  have h4 : Measurable (fun p : ℝ × Coord => ∑ i : Fin 2, ‖flatTranspose ν μ Ψ p.2 i‖) := by
    apply Finset.measurable_sum
    intro i _
    exact ((hT i).norm.measurable).comp measurable_snd
  exact ((h1.mul h2).mul h3).mul h4

end UnforcedLeray.Short.IIb
