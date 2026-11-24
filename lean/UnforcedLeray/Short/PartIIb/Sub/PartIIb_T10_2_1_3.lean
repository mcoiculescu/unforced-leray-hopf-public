import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2_1

/-!
# `PartII-b:T10/2/1/3` (`PsiQMP`): decomposition

Source of record: `the November 2 reference manuscript` lines 1902-1906.

`Φ(z,θ) = (psiTau R z, psiSpace R z θ)`.  On `U = {s > 0, θ ∈ (0,2π)}` it has the left inverse
`g(τ,y) = (chart R τ y, psiAz y)` with `psiAz y = π + arg(-(y₀ + i y₁))`, differentiable on
`W = {y off the axis and off the positive half-line {y₁ = 0, y₀ > 0}}`.  Hence
`Φ⁻¹ N ∩ U ⊆ g '' (N ∩ W)`, which is Lebesgue-null by the null-image theorem.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

/-- The azimuth of `y` in `(0, 2π)`: `π + arg(-(y₀ + i y₁))`. -/
def psiAz (y : UnforcedLeray.Space) : ℝ :=
  Real.pi + Complex.arg (-(⟨y 0, y 1⟩ : ℂ))

/-- The open-image region `W`: off the axis and off the half-line `{y₁ = 0, y₀ > 0}`. -/
def psiW : Set (ℝ × UnforcedLeray.Space) :=
  {x | x.2 ∉ Axi.axis ∧ ¬ (0 < x.2 0 ∧ x.2 1 = 0)}

/-- The left inverse of `Φ`. -/
def psiG (R : ℝ) (x : ℝ × UnforcedLeray.Space) : Coord × ℝ :=
  (Axi.chart R x.1 x.2, psiAz x.2)

/-- **`T10/2/1/3/1`** (SP 1902-1906): for `R > 0`, `s > 0`, `θ ∈ (0, 2π)` the section point lies in
`W` and has azimuth `θ`: `psiAz (psiSpace R z θ) = θ` (`-(ϱcosθ + iϱ sinθ) = ϱ e^{i(θ-π)}`,
`arg = θ - π`). -/
def PsiAzimuth : Prop :=
  ∀ (R : ℝ) (z : Coord) (θ : ℝ), 0 < R → 0 < z.1 → θ ∈ Ioo 0 (2 * Real.pi) →
    psiAz (psiSpace R z θ) = θ ∧ (psiTau R z, psiSpace R z θ) ∈ psiW

/-- **`T10/2/1/3/2`**: `psiG R` is differentiable on `psiW` (`Axi.hasFDerivAt_chart` for the chart
part; `Complex.differentiableAt_arg`-type lemma for `arg` on the slit plane, composed with
`y ↦ -(y₀ + i y₁)`). -/
def PsiGDiff : Prop :=
  ∀ R : ℝ, 0 < R → DifferentiableOn ℝ (psiG R) psiW

/-- **`T10/2/1/3/3`**: a differentiable map `ℝ × ℝ³ → ℝ × (ℝ × ℝ) × ℝ` (equal finite dimension 4)
sends Lebesgue-null sets to Lebesgue-null sets (transport by a linear equivalence and
`Measure.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`, or
`MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` after
`LinearEquiv`/`ContinuousLinearEquiv` between the two 4-dimensional spaces; linear equivalences preserve
null sets by `Measure.addHaar_image_linearMap`/`MeasurableEquiv` arguments). -/
def NullImageDim4 : Prop :=
  ∀ (f : ℝ × UnforcedLeray.Space → Coord × ℝ) (s : Set (ℝ × UnforcedLeray.Space)),
    DifferentiableOn ℝ f s → volume s = 0 → volume (f '' s) = 0

/-- **`T10/2/1/3/4`**: the domain measure is `≪ volume` and carried by `s > 0`, `θ ∈ (0, 2π)`
(`ageμ_ac_volume`, `ageμ_ae_pos`, `Measure.AbsolutelyContinuous.prod`). -/
def PsiDomainAC : Prop :=
  ∀ c r : ℝ, ((hMeas c r).prod (volume.restrict (Ioo 0 (2 * Real.pi)))) ≪ (volume : Measure (Coord × ℝ)) ∧
    ∀ᵐ p : Coord × ℝ ∂((hMeas c r).prod (volume.restrict (Ioo 0 (2 * Real.pi)))),
      0 < p.1.1 ∧ p.2 ∈ Ioo 0 (2 * Real.pi)

theorem psiQMP_proof_of (h1 : ChartSectionEq) (h2 : PsiAzimuth) (h3 : PsiGDiff)
    (h4 : NullImageDim4) (h5 : PsiDomainAC) : PsiQMP := by
  intro c r R hR hc
  set Φ : Coord × ℝ → ℝ × UnforcedLeray.Space :=
    fun p => (psiTau R p.1, psiSpace R p.1 p.2) with hΦ
  have hmeas : Measurable Φ := by
    refine Measurable.prodMk ?_ ?_
    · unfold psiTau
      fun_prop
    · unfold psiSpace
      fun_prop
  refine ⟨hmeas, ?_⟩
  intro N h0
  apply measure_mono_null (subset_toMeasurable volume N)
  rw [Measure.map_apply hmeas (measurableSet_toMeasurable _ _)]
  set M := toMeasurable volume N with hM
  have hM0 : volume M = 0 := by rw [hM, measure_toMeasurable]; exact h0
  obtain ⟨hac, hae⟩ := h5 c r
  have hT : volume (psiG R '' (M ∩ psiW)) = 0 :=
    h4 _ _ ((h3 R hR).mono inter_subset_right) (measure_mono_null inter_subset_left hM0)
  have hsub : Φ ⁻¹' M ⊆ psiG R '' (M ∩ psiW) ∪
      {p : Coord × ℝ | ¬ (0 < p.1.1 ∧ p.2 ∈ Ioo 0 (2 * Real.pi))} := by
    intro p hp
    by_cases hU : 0 < p.1.1 ∧ p.2 ∈ Ioo 0 (2 * Real.pi)
    · left
      obtain ⟨ha, hW⟩ := h2 R p.1 p.2 hR hU.1 hU.2
      refine ⟨Φ p, ⟨hp, hW⟩, ?_⟩
      simp only [psiG, hΦ]
      rw [ha, h1 R p.1 p.2 hR hU.1]
    · right
      exact hU
  refine measure_mono_null hsub (measure_union_null (hac hT) ?_)
  exact ae_iff.1 hae

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.psiQMP_proof_of
