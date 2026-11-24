import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Reduction

/-!
# Helpers for `PartII-b:T12/7/7/1` (`deqAbsMeas`): measurability of the `DeqAbsIntegrable` integrand

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

/-- For a strongly measurable `G'`, the flat heat semigroup is jointly strongly measurable in
`(t, (s, z))`. -/
theorem deqam_flatHeat_stronglyMeasurable (ν : ℝ) {G' : CProf} (hG' : StronglyMeasurable G') :
    StronglyMeasurable (fun p : ℝ × Coord =>
      flatHeat (ν * (p.2.1 - p.1)) (fun w => G' (p.1, w)) p.2.2) := by
  have hK : Measurable (fun q : (ℝ × Coord) × (ℝ × ℝ) =>
      flatHeatKernel (ν * (q.1.2.1 - q.1.1)) q.2) := by
    unfold flatHeatKernel
    fun_prop
  have hGm : Measurable (fun q : (ℝ × Coord) × (ℝ × ℝ) =>
      ((q.1.1, q.1.2.2 - q.2) : Coord)) := by
    fun_prop
  have hΘ : StronglyMeasurable (fun q : (ℝ × Coord) × (ℝ × ℝ) =>
      flatHeatKernel (ν * (q.1.2.1 - q.1.1)) q.2 • G' (q.1.1, q.1.2.2 - q.2)) :=
    hK.stronglyMeasurable.smul (hG'.comp_measurable hGm)
  unfold flatHeat
  exact hΘ.integral_prod_right'

/-- The integrand of `DeqAbsIntegrable` for a strongly measurable `G'` is measurable. -/
theorem deqam_integrand_measurable (ν : ℝ) (μ : ℂ) (Ψ : Coord → Fin 2 → ℝ)
    (hΨ : IsPlanarSolTest Ψ) {G' : CProf} (hG' : StronglyMeasurable G') :
    Measurable (deqAbsIntegrand ν μ G' Ψ) := by
  have hΦ := (deqam_flatHeat_stronglyMeasurable ν hG').measurable
  have hT : ∀ i : Fin 2, Continuous (fun x => flatTranspose ν μ Ψ x i) :=
    fun i => (deqTransposeTest ν μ hΨ i).1
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

/-- Changing the profile on a `t`-slice that agrees a.e. does not change the flat heat semigroup. -/
theorem deqam_flatHeat_congr {G G' : CProf} (θ t : ℝ)
    (hy : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), G (t, y) = G' (t, y)) (z : ℝ × ℝ) :
    flatHeat θ (fun w => G (t, w)) z = flatHeat θ (fun w => G' (t, w)) z := by
  unfold flatHeat
  refine integral_congr_ae ?_
  filter_upwards [((volume : Measure (ℝ × ℝ)).measurePreserving_sub_left z).quasiMeasurePreserving.ae
    hy] with w hw
  have hw' : G (t, z - w) = G' (t, z - w) := hw
  show flatHeatKernel θ w • G (t, z - w) = flatHeatKernel θ w • G' (t, z - w)
  rw [hw']

/-- Off a null set in `(t, (s, z))`, the integrand of `G` equals that of a representative `G'`
which agrees with `G` a.e. on `{t > 0}`. -/
theorem deqam_ae_eq (ν : ℝ) (μ : ℂ) (Ψ : Coord → Fin 2 → ℝ) {G G' : CProf}
    (h : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → G x = G' x) :
    deqAbsIntegrand ν μ G Ψ =ᵐ[(volume : Measure (ℝ × Coord))] deqAbsIntegrand ν μ G' Ψ := by
  have h' : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))),
      0 < z.1 → G z = G' z := h
  have hprod : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)),
      0 < t → G (t, y) = G' (t, y) :=
    Measure.ae_ae_of_ae_prod h'
  rw [Measure.volume_eq_prod]
  have hq := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure Coord)))
  filter_upwards [hq.ae hprod] with p hp
  have hp' : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 → G (p.1, y) = G' (p.1, y) := hp
  unfold deqAbsIntegrand
  split_ifs with hc
  · have hy : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), G (p.1, y) = G' (p.1, y) := by
      filter_upwards [hp'] with y hy
      exact hy hc.1
    rw [deqam_flatHeat_congr (ν * (p.2.1 - p.1)) p.1 hy p.2.2]
  · rfl

end UnforcedLeray.Short.IIb
