import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/14` (`MollLimit`): local integrability of the energies

Source of record: `the November 2 reference manuscript` lines 3427-3440 (energy
class) and 3541-3552. Target: `lmEnergyLocInt : LMEnergyLocInt`, i.e. for `0 < s₁ < s₂` the maps
`s ↦ E(s)`, `s ↦ N(s)` (for `G`) and `s ↦ N_F(s)` (for `F`) are integrable on `[s₁, s₂]`.

Route. On `[s₁, s₂] × cell` the functions `vnorm2 (b p)^2`, `tnorm2 (G p)^2`, `tnorm2 (F p)^2` are
integrable, by domination by the finite integrals of `energyLoc` and `L2locTensor`. Integrating
out the cell variable (`Integrable.integral_prod_left` on the product measure
`(volume.restrict [s₁,s₂]).prod (volume.restrict cell)`) gives the integrability of the
slice energies in `s`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Measurability of the Euclidean norm of a `ℂ²`-valued function. -/
theorem loc_measurable_vnorm2 {β : Type*} [MeasurableSpace β] {f : β → Fin 2 → ℂ}
    (hf : ∀ i, Measurable fun p => f p i) : Measurable fun p => vnorm2 (f p) := by
  unfold vnorm2
  exact Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ fun i _ => ((hf i).norm).pow_const 2)

/-- Measurability of the Frobenius norm of a `ℂ²ˣ²`-valued function. -/
theorem loc_measurable_tnorm2 {β : Type*} [MeasurableSpace β] {T : β → Fin 2 → Fin 2 → ℂ}
    (hT : ∀ i j, Measurable fun p => T p i j) : Measurable fun p => tnorm2 (T p) := by
  unfold tnorm2
  exact Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      ((hT i j).norm).pow_const 2)

/-- A nonnegative measurable real function dominated by an integrand with finite lower integral is
integrable. -/
theorem loc_integrable_of_dominated {β : Type*} [MeasurableSpace β] {μ : Measure β}
    {f g : β → ℝ} (hf : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hle : ∀ p, f p ≤ g p) (hfin : ∫⁻ p, ENNReal.ofReal (g p) ∂μ < ⊤) :
    Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hfin
  rw [Real.enorm_eq_ofReal (hfn p)]
  exact ENNReal.ofReal_le_ofReal (hle p)

/-- The energies are locally integrable in `s` (SP 3427-3440). -/
theorem lmEnergyLocInt : LMEnergyLocInt := by
  intro c ν μ F b G hD s₁ s₂ h0 h12
  -- `b`, `G` part: the product integrability from `energyLoc`
  have hEN : Integrable (fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) ^ 2)
      ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c))) ∧
      Integrable (fun p : ℝ × (ℝ × ℝ) => tnorm2 (G p) ^ 2)
      ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    have hloc := hD.sol.energyLoc s₁ s₂ h0 h12
    have hb : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (b p) ^ 2 :=
      (loc_measurable_vnorm2 hD.sol.measurable).pow_const 2
    have hG : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (G p) ^ 2 :=
      (loc_measurable_tnorm2 hD.sol.gradMeasurable).pow_const 2
    constructor
    · refine loc_integrable_of_dominated hb (fun p => sq_nonneg _) (fun p => ?_) hloc
      exact le_add_of_nonneg_right (sq_nonneg _)
    · refine loc_integrable_of_dominated hG (fun p => sq_nonneg _) (fun p => ?_) hloc
      exact le_add_of_nonneg_left (sq_nonneg _)
  -- `F` part: the product integrability from `L2locTensor`
  have hF : Integrable (fun p : ℝ × (ℝ × ℝ) => tnorm2 (F p) ^ 2)
      ((volume.restrict (Icc s₁ s₂)).prod (volume.restrict (B0579.cell c))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    have hF2 : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (F p) ^ 2 :=
      (loc_measurable_tnorm2 hD.meas).pow_const 2
    exact loc_integrable_of_dominated hF2 (fun p => sq_nonneg _) (fun p => le_rfl)
      (hD.l2loc s₁ s₂ h0 h12)
  refine ⟨?_, ?_, ?_⟩
  · have h := hEN.1.integral_prod_left
    unfold IntegrableOn energyE
    exact h
  · have h := hEN.2.integral_prod_left
    unfold IntegrableOn energyN
    exact h
  · have h := hF.integral_prod_left
    unfold IntegrableOn energyN
    exact h

end UnforcedLeray.Short.IIIa
