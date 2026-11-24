import UnforcedLeray.Short.PartIIb.Sub.T12
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzExists.Bounded

/-!
# Pairings of `L^r` fields with bounded weights are continuous in `L^r`

For `H ∈ L^r(avgμ c)` and weights `w_i` (continuous, bounded by `M`, vanishing for `|η| > L`),
the pairing `z ↦ ∑_i H z i * w i z` is integrable and its `L^1` norm is controlled by the
`L^r` norm of `H` (Hölder on the finite-measure strip `univ ×ˢ Icc (-L) L`). Consequently
`H_k → H` in `L^r` makes the integrated pairings converge.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- The weighted pairing `∑_i H_i w_i` of a `ℂ²`-valued field with `w : Fin 2 → plane → ℂ`. -/
def cylPair (w : Fin 2 → ℝ × ℝ → ℂ) (H : ℝ × ℝ → CMerid) (z : ℝ × ℝ) : ℂ :=
  ∑ i : Fin 2, H z i * w i z

theorem avgμ_strip_lt_top {c L : ℝ} (hc : 0 < c) :
    UnforcedLeray.Cyl.avgμ c (univ ×ˢ Icc (-L) L) < ⊤ := by
  rw [UnforcedLeray.Cyl.avgμ_univ_prod hc, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-- Pointwise and Hölder bound for the weighted pairing. -/
theorem cylPair_lintegral_le {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {L M : ℝ}
    {w : Fin 2 → ℝ × ℝ → ℂ} (hwb : ∀ i z, ‖w i z‖ ≤ M) (hws : ∀ i z, L < |z.2| → w i z = 0)
    {H : ℝ × ℝ → CMerid} (hH : MemLp H (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)) :
    ∫⁻ z, ‖cylPair w H z‖ₑ ∂(UnforcedLeray.Cyl.avgμ c) ≤
      ENNReal.ofReal (2 * M) * (UnforcedLeray.Cyl.avgμ c (univ ×ˢ Icc (-L) L)) ^ ((1 : ℝ) - 1 / r) *
        eLpNorm H (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
  set μ := UnforcedLeray.Cyl.avgμ c with hμ
  set S : Set (ℝ × ℝ) := univ ×ˢ Icc (-L) L with hS
  have hSm : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Icc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hwb 0 (0, 0))
  have hpt : ∀ z, ‖cylPair w H z‖ₑ ≤
      S.indicator (fun z => ENNReal.ofReal (2 * M) * ‖H z‖ₑ) z := by
    intro z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
        ← ENNReal.ofReal_mul (by linarith)]
      apply ENNReal.ofReal_le_ofReal
      unfold cylPair
      refine (norm_sum_le _ _).trans ?_
      have h0 : ∀ i : Fin 2, ‖H z i * w i z‖ ≤ ‖H z‖ * M := fun i => by
        rw [norm_mul]
        exact mul_le_mul (PiLp.norm_apply_le _ i) (hwb i z) (norm_nonneg _) (norm_nonneg _)
      simp only [Fin.sum_univ_two]
      nlinarith [h0 0, h0 1]
    · have hL : L < |z.2| := by
        by_contra h
        push_neg at h
        exact hz ⟨mem_univ _, abs_le.mp h⟩
      rw [indicator_of_notMem hz]
      unfold cylPair
      simp [hws _ _ hL]
  have hres : (μ.restrict S) univ = μ S := Measure.restrict_apply_univ S
  calc ∫⁻ z, ‖cylPair w H z‖ₑ ∂μ
      ≤ ∫⁻ z, S.indicator (fun z => ENNReal.ofReal (2 * M) * ‖H z‖ₑ) z ∂μ := lintegral_mono hpt
    _ = ∫⁻ z in S, ENNReal.ofReal (2 * M) * ‖H z‖ₑ ∂μ := lintegral_indicator hSm _
    _ = ENNReal.ofReal (2 * M) * ∫⁻ z in S, ‖H z‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (2 * M) * eLpNorm H 1 (μ.restrict S) := by
        rw [eLpNorm_one_eq_lintegral_enorm]
    _ ≤ ENNReal.ofReal (2 * M) * (eLpNorm H (ENNReal.ofReal r) (μ.restrict S) *
          (μ.restrict S) univ ^ ((1 : ℝ) - 1 / r)) := by
        gcongr
        have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict S) (p := 1)
          (q := ENNReal.ofReal r) (by
            rw [← ENNReal.ofReal_one]
            exact (ENNReal.ofReal_le_ofReal hr.le))
          hH.1.restrict
        rw [ENNReal.toReal_one, ENNReal.toReal_ofReal (by linarith)] at h
        simpa using h
    _ ≤ ENNReal.ofReal (2 * M) * ((μ S) ^ ((1 : ℝ) - 1 / r) * eLpNorm H (ENNReal.ofReal r) μ) := by
        rw [hres]
        have hm : eLpNorm H (ENNReal.ofReal r) (μ.restrict S) ≤ eLpNorm H (ENNReal.ofReal r) μ :=
          eLpNorm_mono_measure H Measure.restrict_le_self
        rw [mul_comm (eLpNorm H (ENNReal.ofReal r) (μ.restrict S))]
        gcongr
    _ = ENNReal.ofReal (2 * M) * (μ S) ^ ((1 : ℝ) - 1 / r) * eLpNorm H (ENNReal.ofReal r) μ := by
        ring

/-- The weighted pairing is integrable. -/
theorem cylPair_integrable {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {L M : ℝ}
    {w : Fin 2 → ℝ × ℝ → ℂ} (hwc : ∀ i, Continuous (w i))
    (hwb : ∀ i z, ‖w i z‖ ≤ M) (hws : ∀ i z, L < |z.2| → w i z = 0)
    {H : ℝ × ℝ → CMerid} (hH : MemLp H (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)) :
    Integrable (cylPair w H) (UnforcedLeray.Cyl.avgμ c) := by
  refine ⟨?_, ?_⟩
  · unfold cylPair
    have hterm : ∀ i : Fin 2, AEStronglyMeasurable
        (fun z : ℝ × ℝ => H z i * w i z) (UnforcedLeray.Cyl.avgμ c) := fun i =>
      ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hH.1).mul
        (hwc i).aestronglyMeasurable
    simp only [Fin.sum_univ_two]
    exact (hterm 0).add (hterm 1)
  · rw [hasFiniteIntegral_iff_enorm]
    refine (cylPair_lintegral_le hc hr hwb hws hH).trans_lt ?_
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_) hH.2
    exact ENNReal.rpow_lt_top_of_nonneg (by
      have : 1 / r ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      linarith) (avgμ_strip_lt_top hc).ne

/-- Continuity of the integrated weighted pairing in `L^r`. -/
theorem cylPair_tendsto {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {L M : ℝ}
    {w : Fin 2 → ℝ × ℝ → ℂ} (hwc : ∀ i, Continuous (w i))
    (hwb : ∀ i z, ‖w i z‖ ≤ M) (hws : ∀ i z, L < |z.2| → w i z = 0)
    {H : ℕ → ℝ × ℝ → CMerid} {H₀ : ℝ × ℝ → CMerid}
    (hH : ∀ k, MemLp (H k) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
    (hH₀ : MemLp H₀ (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
    (hlim : Tendsto (fun k => eLpNorm (H k - H₀) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
      atTop (𝓝 0)) :
    Tendsto (fun k => ∫ z, cylPair w (H k) z ∂(UnforcedLeray.Cyl.avgμ c)) atTop
      (𝓝 (∫ z, cylPair w H₀ z ∂(UnforcedLeray.Cyl.avgμ c))) := by
  set μ := UnforcedLeray.Cyl.avgμ c with hμ
  have hKtop : ENNReal.ofReal (2 * M) * (μ (univ ×ˢ Icc (-L) L)) ^ ((1 : ℝ) - 1 / r) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg ?_ (avgμ_strip_lt_top hc).ne)
    have : 1 / r ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have hdiff : ∀ k, ∫ z, cylPair w (H k) z ∂μ - ∫ z, cylPair w H₀ z ∂μ =
      ∫ z, cylPair w (H k - H₀) z ∂μ := by
    intro k
    rw [← integral_sub (cylPair_integrable hc hr hwc hwb hws (hH k))
      (cylPair_integrable hc hr hwc hwb hws hH₀)]
    congr 1
    funext z
    simp only [cylPair, Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [← tendsto_sub_nhds_zero_iff]
  simp_rw [hdiff]
  have htend : Tendsto (fun k => (ENNReal.ofReal (2 * M) * (μ (univ ×ˢ Icc (-L) L)) ^
      ((1 : ℝ) - 1 / r) * eLpNorm (H k - H₀) (ENNReal.ofReal r) μ).toReal) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul hlim (Or.inr hKtop)
    rw [mul_zero] at h1
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    rw [ENNReal.toReal_zero] at h2
    exact h2
  refine squeeze_zero_norm (fun k => ?_) htend
  have hb := cylPair_lintegral_le hc hr hwb hws ((hH k).sub (hH₀))
  have hfin : ENNReal.ofReal (2 * M) * (μ (univ ×ˢ Icc (-L) L)) ^ ((1 : ℝ) - 1 / r) *
      eLpNorm (H k - H₀) (ENNReal.ofReal r) μ ≠ ⊤ :=
    ENNReal.mul_ne_top hKtop (((hH k).sub hH₀).2).ne
  refine (norm_integral_le_lintegral_norm _).trans ?_
  apply ENNReal.toReal_mono hfin
  simpa only [← ofReal_norm_eq_enorm] using hb

end UnforcedLeray.Short.IIb
