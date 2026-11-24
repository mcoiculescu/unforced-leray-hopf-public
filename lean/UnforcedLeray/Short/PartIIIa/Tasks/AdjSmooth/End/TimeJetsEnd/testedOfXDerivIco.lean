import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_2
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.TestedOfXDeriv

/-!
# `PartIII-a:T21/2/7/2/1/2/1/2/2`: an `X_{-m,c}`-derivative on `[a, b)` is a tested derivative

Ico transcription of `Tasks/AdjSmooth/Interior/TimeJets/TestedOfXDeriv.lean` (`testedOfXDeriv`,
Ioo). The helpers `tc_integrable`, `tc_bound`, `tc_squeeze` are reused unchanged.  The only change
is the filter: the difference quotients converge along `𝓝[Ico a b \ {r}] r` (the filter of
`HasXDerivOn` on `Ico a b`), and the derivative within `Ico a b` is read off with
`hasDerivWithinAt_iff_tendsto_slope`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **`TestedOfXDerivIco`**: an `X_{-m,c}`-derivative on `[a, b)` is a tested derivative against
every cylinder test, at every `r ∈ [a, b)` (within `[a, b)`). -/
theorem testedOfXDerivIco : TestedOfXDerivIco := by
  have hCS : WeightedCS := weightedCS
  unfold TestedOfXDerivIco
  intro c m a b f f' _hc hf hf' hX χ hχ r hr
  unfold HasXDerivOn at hX
  have hXr := hX r hr
  have hCtop : eLpNorm χ 2 (B0579.cellMeasure c m) ≠ ⊤ := (hχ.memLp m).2.ne
  -- the slope is the integral of the difference quotient plus the constant `∫ f' r χ`
  have hsl : ∀ᶠ r' in 𝓝[Ico a b \ {r}] r,
      slope (fun r' => ∫ x in B0579.cell c, f r' x * ((χ x : ℝ) : ℂ)) r r' =
        (∫ x in B0579.cell c,
            (((((r' - r)⁻¹ : ℝ) : ℂ)) * (f r' x - f r x) - f' r x) * ((χ x : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, f' r x * ((χ x : ℝ) : ℂ) := by
    filter_upwards [eventually_mem_nhdsWithin] with r' hr'
    have hr'I : r' ∈ Ico a b := hr'.1
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
      (𝓝[Ico a b \ {r}] r) (𝓝 0) := by
    refine tc_squeeze _ _ _ hCtop hXr ?_
    filter_upwards [eventually_mem_nhdsWithin] with r' hr'
    have hr'I : r' ∈ Ico a b := hr'.1
    have hm : AEStronglyMeasurable
        (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x)
        (B0579.cellMeasure c (-m)) :=
      (((hf r' hr'I).aestronglyMeasurable.sub (hf r hr).aestronglyMeasurable).const_mul _).sub
        (hf' r hr).aestronglyMeasurable
    exact tc_bound hCS hχ _ hm
  have hL := hG.add_const (∫ x in B0579.cell c, f' r x * ((χ x : ℝ) : ℂ))
  rw [zero_add] at hL
  rw [hasDerivWithinAt_iff_tendsto_slope]
  exact hL.congr' (hsl.mono fun r' h => h.symm)

end UnforcedLeray.Short.IIIa
