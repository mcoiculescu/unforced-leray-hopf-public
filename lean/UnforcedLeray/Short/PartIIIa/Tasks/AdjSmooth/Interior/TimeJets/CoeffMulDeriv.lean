import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace CoeffMulAux

/-- A bounded complex coefficient multiplies the `L²` norm by at most its bound. -/
theorem coeff_bound (μ : Measure (ℝ × ℝ)) (b : ℝ × ℝ → ℂ) {B0 : ℝ} (hB0 : 0 ≤ B0)
    (hb : ∀ x, ‖b x‖ ≤ B0) (g : ℝ × ℝ → ℂ) :
    eLpNorm (fun x => b x * g x) 2 μ ≤ ENNReal.ofReal B0 * eLpNorm g 2 μ := by
  calc eLpNorm (fun x => b x * g x) 2 μ ≤ eLpNorm (fun x => (B0 : ℂ) * g x) 2 μ := by
        refine eLpNorm_mono fun x => ?_
        show ‖b x * g x‖ ≤ ‖(B0 : ℂ) * g x‖
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hB0]
        exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
    _ = ‖(B0 : ℂ)‖ₑ * eLpNorm g 2 μ := by
        rw [← eLpNorm_const_smul (B0 : ℂ) g 2 μ]
        rfl
    _ = ENNReal.ofReal B0 * eLpNorm g 2 μ := by
        rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg hB0]

/-- Triangle inequality for three summands in `L²`. -/
theorem tri3 (μ : Measure (ℝ × ℝ)) (g1 g2 g3 : ℝ × ℝ → ℂ) (h1 : AEStronglyMeasurable g1 μ)
    (h2 : AEStronglyMeasurable g2 μ) (h3 : AEStronglyMeasurable g3 μ) :
    eLpNorm (fun x => g1 x + g2 x + g3 x) 2 μ ≤
      eLpNorm g1 2 μ + eLpNorm g2 2 μ + eLpNorm g3 2 μ := by
  have e1 : eLpNorm (fun x => g1 x + g2 x + g3 x) 2 μ ≤
      eLpNorm (fun x => g1 x + g2 x) 2 μ + eLpNorm g3 2 μ :=
    eLpNorm_add_le (h1.add h2) h3 (by norm_num)
  have e2 : eLpNorm (fun x => g1 x + g2 x) 2 μ ≤ eLpNorm g1 2 μ + eLpNorm g2 2 μ :=
    eLpNorm_add_le h1 h2 (by norm_num)
  exact e1.trans (add_le_add e2 le_rfl)

/-- A small multiple of a finite quantity is small: `ε ↦ ε K` tends to `0`. -/
theorem enn_small {K : ℝ≥0∞} (hK : K ≠ ⊤) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε * K < δ := by
  have hc : Tendsto (fun ε : ℝ => ENNReal.ofReal ε * K) (𝓝 0) (𝓝 (ENNReal.ofReal 0 * K)) :=
    ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto 0) (Or.inr hK)
  rw [ENNReal.ofReal_zero, zero_mul] at hc
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ENNReal.ofReal ε * K < δ := hc.eventually (gt_mem_nhds hδ)
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal ε * K < δ := nhdsWithin_le_nhds h1
  have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε2, hε1⟩ := (h2.and h3).exists
  exact ⟨ε, hε1, hε2⟩

end CoeffMulAux

open CoeffMulAux

/-- **(11) Age derivative of a product with a smooth coefficient** (SP 3060): the product rule
`∂_r(A f) = A' f + A ∂_r f` in `X_{-m,c}`, from the pointwise identity
`Q = A(r') D + (A(r') - A(r)) f' + ((r'-r)⁻¹(A(r') - A(r)) - A'(r)) f` (`D` the difference
quotient of `f`) and the three coefficient bounds. -/
theorem coeffMulDeriv : CoeffMulDeriv := by
  intro c m a b A A' f f' hc hA hA' hAd hf hf' hX r hr
  unfold xNorm at *
  have hAr := hA.2 [] r hr
  simp only [rSpatial] at hAr
  obtain ⟨⟨B0, hB0⟩, hAc⟩ := hAr
  set I := Ioo a b with hI
  set μ := B0579.cellMeasure c (-m) with hμ
  set Bm := max B0 0 with hBm
  have hBm0 : 0 ≤ Bm := le_max_right _ _
  have hB0' : ∀ x, |A r x| ≤ Bm := fun x => (hB0 x).trans (le_max_left _ _)
  have hAc1 : ∀ᶠ r' in 𝓝[I \ {r}] r, ∀ x, |A r' x - A r x| ≤ 1 :=
    nhdsWithin_mono r diff_subset (hAc 1 one_pos)
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
    nhdsWithin_mono r diff_subset (hAc ε hε)
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
