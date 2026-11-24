import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.RhsCont.WeightedCS

/-!
# `PartIII-a:T21/2/7/2/1/1/6/3`: an `X_{-m,c}`-derivative is a tested derivative (`TestedOfXDeriv`)

Source: `the November 2 reference manuscript` lines 3060 (the age derivative of a
weak adjoint, tested against cylinder tests) and 3052-3058 (weighted Cauchy-Schwarz on the cell).

For a cylinder test `χ` and `r ∈ (a, b)`, the difference quotient of `F(r') = ∫_cell f(r') χ` is
`∫_cell h(r') χ + ∫_cell f'(r) χ` with `h(r') = (r' - r)⁻¹ (f(r') - f(r)) - f'(r)`, and
`|∫_cell h χ| ≤ ‖h‖_{X_{-m}} ‖χ‖_{X_m}` by `WeightedCS`, which tends to zero by `HasXDerivOn`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Integrability of `f χ` on the cell for a cylinder test `χ` and `f ∈ X_{-m,c}` (`integrable_pair`
with `N = χ`, `B = |χ| ∈ X_m`). -/
theorem tc_integrable (hCS : WeightedCS) {c m : ℝ} {f : ℝ × ℝ → ℂ} {χ : ℝ × ℝ → ℝ}
    (hχ : B0579.IsCylTest c χ) (hf : MemLp f 2 (B0579.cellMeasure c (-m))) :
    Integrable (fun x => f x * ((χ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) := by
  have hB : MemLp (fun x => |χ x|) 2 (B0579.cellMeasure c m) := by
    simpa [Real.norm_eq_abs] using (hχ.memLp m).norm
  exact integrable_pair hCS (K := 1) hf hB hχ.continuous.aestronglyMeasurable
    (fun x _ => by simp)

/-- The weighted pairing bound: `‖∫_cell g χ‖ₑ ≤ ‖g‖_{X_{-m,c}} ‖χ‖_{X_{m,c}}` (`WeightedCS`). -/
theorem tc_bound (hCS : WeightedCS) {c m : ℝ} {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ)
    (g : ℝ × ℝ → ℂ) (hg : AEStronglyMeasurable g (B0579.cellMeasure c (-m))) :
    ‖∫ x in B0579.cell c, g x * ((χ x : ℝ) : ℂ)‖ₑ ≤
      xNorm c (-m) g * eLpNorm χ 2 (B0579.cellMeasure c m) := by
  have hpt : ∀ x, ‖g x * ((χ x : ℝ) : ℂ)‖ₑ = ‖g x‖ₑ * ‖χ x‖ₑ := fun x => by
    simp only [enorm_eq_nnnorm, nnnorm_mul, Complex.nnnorm_real, ENNReal.coe_mul]
  calc ‖∫ x in B0579.cell c, g x * ((χ x : ℝ) : ℂ)‖ₑ
      ≤ ∫⁻ x in B0579.cell c, ‖g x * ((χ x : ℝ) : ℂ)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x in B0579.cell c, ‖g x‖ₑ * ‖χ x‖ₑ := lintegral_congr hpt
    _ ≤ xNorm c (-m) g * eLpNorm χ 2 (B0579.cellMeasure c m) :=
        hCS c m g χ hg (hχ.memLp m).aestronglyMeasurable

/-- A squeeze in `ℝ≥0∞` transferred to `ℂ`: `‖G r'‖ₑ ≤ X r' C` with `X → 0` gives `G → 0`. -/
theorem tc_squeeze {β : Type*} {l : Filter β} (X : β → ℝ≥0∞) (G : β → ℂ) (C : ℝ≥0∞)
    (hC : C ≠ ⊤) (hX : Tendsto X l (𝓝 0)) (hG : ∀ᶠ r' in l, ‖G r'‖ₑ ≤ X r' * C) :
    Tendsto G l (𝓝 0) := by
  have hup : Tendsto (fun r' => X r' * C) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hX (Or.inr hC)
  have hsq : Tendsto (fun r' => ‖G r'‖ₑ) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun _ => zero_le) hG
  have hr : Tendsto (fun r' => (‖G r'‖ₑ).toReal) l (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsq
    simpa [Function.comp_def] using this
  apply tendsto_zero_iff_norm_tendsto_zero.2
  exact hr.congr (fun r' => by rw [enorm_eq_nnnorm]; simp)

/-- **`TestedOfXDeriv`**: an `X_{-m,c}`-derivative on `(a, b)` is a tested derivative against every
cylinder test (SP 3060, 3052-3058). -/
theorem testedOfXDeriv : TestedOfXDeriv := by
  have hCS : WeightedCS := weightedCS
  unfold TestedOfXDeriv
  intro c m a b f f' _hc hf hf' hX χ hχ r hr
  unfold HasXDerivOn at hX
  have hXr := hX r hr
  have hI : 𝓝[Ioo a b \ {r}] r = 𝓝[≠] r := by
    have hmem : Ioo a b ∈ 𝓝[{r}ᶜ] r := mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hr.1 hr.2)
    rw [Set.sdiff_eq]
    exact nhdsWithin_inter_of_mem hmem
  have hCtop : eLpNorm χ 2 (B0579.cellMeasure c m) ≠ ⊤ := (hχ.memLp m).2.ne
  -- the slope is the integral of the difference quotient plus the constant `∫ f' r χ`
  have hsl : ∀ᶠ r' in 𝓝[Ioo a b \ {r}] r,
      slope (fun r' => ∫ x in B0579.cell c, f r' x * ((χ x : ℝ) : ℂ)) r r' =
        (∫ x in B0579.cell c,
            (((((r' - r)⁻¹ : ℝ) : ℂ)) * (f r' x - f r x) - f' r x) * ((χ x : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, f' r x * ((χ x : ℝ) : ℂ) := by
    filter_upwards [eventually_mem_nhdsWithin] with r' hr'
    have hr'I : r' ∈ Ioo a b := hr'.1
    have I1 : Integrable (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x * ((χ x : ℝ) : ℂ)))
        (volume.restrict (B0579.cell c)) :=
      (tc_integrable hCS hχ (hf r' hr'I)).const_mul _
    have I2 : Integrable (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r x * ((χ x : ℝ) : ℂ)))
        (volume.restrict (B0579.cell c)) :=
      (tc_integrable hCS hχ (hf r hr)).const_mul _
    have I3 : Integrable (fun x => f' r x * ((χ x : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) :=
      tc_integrable hCS hχ (hf' r hr)
    have hpt : ∀ x, (((((r' - r)⁻¹ : ℝ) : ℂ)) * (f r' x - f r x) - f' r x) * ((χ x : ℝ) : ℂ) =
        (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x * ((χ x : ℝ) : ℂ))
          - (((r' - r)⁻¹ : ℝ) : ℂ) * (f r x * ((χ x : ℝ) : ℂ)) - f' r x * ((χ x : ℝ) : ℂ) :=
      fun x => by ring
    simp only [hpt]
    have J12 : Integrable (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x * ((χ x : ℝ) : ℂ))
        - (((r' - r)⁻¹ : ℝ) : ℂ) * (f r x * ((χ x : ℝ) : ℂ)))
        (volume.restrict (B0579.cell c)) := I1.sub I2
    rw [integral_sub J12 I3, integral_sub I1 I2, integral_const_mul, integral_const_mul]
    simp only [slope_def_module, Complex.real_smul]
    ring
  -- the difference quotient of the integral tends to zero
  have hG : Tendsto (fun r' => ∫ x in B0579.cell c,
      (((((r' - r)⁻¹ : ℝ) : ℂ)) * (f r' x - f r x) - f' r x) * ((χ x : ℝ) : ℂ))
      (𝓝[Ioo a b \ {r}] r) (𝓝 0) := by
    refine tc_squeeze _ _ _ hCtop hXr ?_
    filter_upwards [eventually_mem_nhdsWithin] with r' hr'
    have hr'I : r' ∈ Ioo a b := hr'.1
    have hm : AEStronglyMeasurable
        (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x)
        (B0579.cellMeasure c (-m)) :=
      (((hf r' hr'I).aestronglyMeasurable.sub (hf r hr).aestronglyMeasurable).const_mul _).sub
        (hf' r hr).aestronglyMeasurable
    exact tc_bound hCS hχ _ hm
  have hL := hG.add_const (∫ x in B0579.cell c, f' r x * ((χ x : ℝ) : ℂ))
  rw [zero_add] at hL
  rw [hasDerivAt_iff_tendsto_slope, ← hI]
  exact hL.congr' (hsl.mono fun r' h => h.symm)

end UnforcedLeray.Short.IIIa
