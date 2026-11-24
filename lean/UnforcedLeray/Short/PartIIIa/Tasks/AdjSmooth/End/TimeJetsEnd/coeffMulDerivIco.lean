import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_2
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.CoeffMulDeriv

/-!
# `PartIII-a:T21/2/7/2/1/2/1/2/4`: the product rule with a smooth coefficient on `[a, b)`

Ico transcription of `Tasks/AdjSmooth/Interior/TimeJets/CoeffMulDeriv.lean` (`coeffMulDeriv`,
Ioo). The helpers of `CoeffMulAux` (`coeff_bound`, `tri3`, `enn_small`) are reused unchanged. The
only change is the neighbourhood filter: `HasCoeffDeriv (Ico a b)` and `HasXDerivOn` on `Ico a b`
both use `𝓝[Ico a b \ {r}] r`, and the product-rule estimate is the same.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open CoeffMulAux

/-- **`CoeffMulDerivIco`**: the product rule `∂_r(A f) = A' f + A ∂_r f` in `X_{-m,c}` on `[a, b)`
(SP 3060), from the pointwise identity
`Q = A(r') D + (A(r') - A(r)) f' + ((r'-r)⁻¹(A(r') - A(r)) - A'(r)) f` (`D` the difference
quotient of `f`) and the three coefficient bounds. -/
theorem coeffMulDerivIco : CoeffMulDerivIco := by
  intro c m a b A A' f f' hc hA hA' hAd hf hf' hX r hr
  unfold xNorm at *
  have hAr := hA.2 [] r hr
  simp only [rSpatial] at hAr
  obtain ⟨⟨B0, hB0⟩, hAc⟩ := hAr
  set I := Ico a b with hI
  set μ := B0579.cellMeasure c (-m) with hμ
  set Bm := max B0 0 with hBm
  have hBm0 : 0 ≤ Bm := le_max_right _ _
  have hB0' : ∀ x, |A r x| ≤ Bm := fun x => (hB0 x).trans (le_max_left _ _)
  have hAc1 : ∀ᶠ r' in 𝓝[I \ {r}] r, ∀ x, |A r' x - A r x| ≤ 1 :=
    nhdsWithin_mono r sdiff_subset (hAc 1 one_pos)
  have hAbd : ∀ᶠ r' in 𝓝[I \ {r}] r, ∀ x, ‖(A r' x : ℂ)‖ ≤ Bm + 1 := by
    filter_upwards [hAc1] with r' h1 x
    rw [Complex.norm_real, Real.norm_eq_abs]
    have e : |A r' x| ≤ |A r x| + |A r' x - A r x| := by
      calc |A r' x| = |A r x + (A r' x - A r x)| := by congr 1; ring
        _ ≤ |A r x| + |A r' x - A r x| := abs_add_le _ _
    linarith [hB0' x, h1 x]
  have hK : eLpNorm (f' r) 2 μ + eLpNorm (f r) 2 μ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨(hf' r hr).eLpNorm_lt_top.ne, (hf r hr).eLpNorm_lt_top.ne⟩
  -- the difference quotient of `f` tends to `0`, weighted by the bound of `A`
  have hu : Tendsto (fun r' => ENNReal.ofReal (Bm + 1) *
      eLpNorm (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x) 2 μ)
      (𝓝[I \ {r}] r) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Bm + 1)) (hX r hr)
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at this
    exact this
  refine ENNReal.tendsto_nhds_zero.2 fun δ hδ => ?_
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨ε, hε, hεK⟩ := enn_small hK hδ2
  have hAε : ∀ᶠ r' in 𝓝[I \ {r}] r, ∀ x, |A r' x - A r x| ≤ ε :=
    nhdsWithin_mono r sdiff_subset (hAc ε hε)
  have hAdε : ∀ᶠ r' in 𝓝[I \ {r}] r, ∀ x, |(r' - r)⁻¹ * (A r' x - A r x) - A' r x| ≤ ε := by
    filter_upwards [hAd r hr ε hε] with r' h x
    have := h x
    simpa using this
  have hev : ∀ᶠ r' in 𝓝[I \ {r}] r,
      eLpNorm (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * ((A r' x : ℂ) * f r' x - (A r x : ℂ) * f r x)
          - ((A' r x : ℂ) * f r x + (A r x : ℂ) * f' r x)) 2 μ ≤
        ENNReal.ofReal (Bm + 1) * eLpNorm
            (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x) 2 μ +
          ENNReal.ofReal ε * (eLpNorm (f' r) 2 μ + eLpNorm (f r) 2 μ) := by
    filter_upwards [hAbd, hAε, hAdε, self_mem_nhdsWithin] with r' hb h1 h2 hr'
    have hr'I : r' ∈ I := hr'.1
    have hfr' : MemLp (f r') 2 μ := hf r' hr'I
    have hcA : Continuous (fun x => (A r' x : ℂ)) :=
      Complex.continuous_ofReal.comp (hA.1 r' hr'I).1.continuous
    have hcAd : Continuous (fun x => ((A r' x - A r x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((hA.1 r' hr'I).1.continuous.sub (hA.1 r hr).1.continuous)
    have hcC : Continuous (fun x => (((r' - r)⁻¹ * (A r' x - A r x) - A' r x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((continuous_const.mul ((hA.1 r' hr'I).1.continuous.sub (hA.1 r hr).1.continuous)).sub
          (hA'.1 r hr).1.continuous)
    have hD : AEStronglyMeasurable
        (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x) μ :=
      ((hfr'.aestronglyMeasurable.sub (hf r hr).aestronglyMeasurable).const_mul _).sub
        (hf' r hr).aestronglyMeasurable
    have hm1 : AEStronglyMeasurable
        (fun x => (A r' x : ℂ) * ((((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x)) μ :=
      hcA.aestronglyMeasurable.mul hD
    have hm2 : AEStronglyMeasurable (fun x => ((A r' x - A r x : ℝ) : ℂ) * f' r x) μ :=
      hcAd.aestronglyMeasurable.mul (hf' r hr).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable
        (fun x => (((r' - r)⁻¹ * (A r' x - A r x) - A' r x : ℝ) : ℂ) * f r x) μ :=
      hcC.aestronglyMeasurable.mul (hf r hr).aestronglyMeasurable
    have hQ : ∀ x, (((r' - r)⁻¹ : ℝ) : ℂ) * ((A r' x : ℂ) * f r' x - (A r x : ℂ) * f r x)
          - ((A' r x : ℂ) * f r x + (A r x : ℂ) * f' r x) =
        (A r' x : ℂ) * ((((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x) +
          ((A r' x - A r x : ℝ) : ℂ) * f' r x +
          (((r' - r)⁻¹ * (A r' x - A r x) - A' r x : ℝ) : ℂ) * f r x := by
      intro x
      push_cast
      ring
    have hfun := funext (fun x => hQ x)
    have hsplit := (congrArg (fun F => eLpNorm F 2 μ) hfun).trans_le
      (tri3 μ _ _ _ hm1 hm2 hm3)
    have hb1 := coeff_bound μ (fun x => (A r' x : ℂ)) (by linarith [hBm0]) hb
      (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (f r' x - f r x) - f' r x)
    have hb2 := coeff_bound μ (fun x => ((A r' x - A r x : ℝ) : ℂ)) hε.le
      (fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact h1 x) (f' r)
    have hb3 := coeff_bound μ (fun x => (((r' - r)⁻¹ * (A r' x - A r x) - A' r x : ℝ) : ℂ))
      hε.le (fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact h2 x) (f r)
    exact hsplit.trans ((add_le_add (add_le_add hb1 hb2) hb3).trans_eq (by ring))
  have hsmall := hu.eventually (gt_mem_nhds hδ2)
  filter_upwards [hev, hsmall] with r' h1 h2
  exact h1.trans ((add_le_add h2.le hεK.le).trans (ENNReal.add_halves δ).le)

end UnforcedLeray.Short.IIIa
