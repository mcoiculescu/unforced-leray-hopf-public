import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9_1_1_1

/-!
# `PartIII-a:T21/2/3/1/9/1/1/1`, smoothing (`ladDensSmooth`)

Source `the November 2 reference manuscript` lines 3230-3240.

Given a continuous `c`-periodic `g` vanishing for `|η|` large, the convolutions
`h_n = φ_n ⋆ g` with normalized bumps `φ_n` of outer radius `1/(n+1) ≤ 1` are smooth, `c`-periodic,
vanish for `|η| > R + 1`, and converge pointwise to `g`. Dominated convergence on the cell
(where the weight is finite on the strip `|η| ≤ R + 1`) gives `xNorm (g - h_n) → 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

namespace DensSmoothAux

/-- A continuous `c`-periodic function vanishing for `|η|` large is bounded. -/
lemma bdd_of_periodic_band {c R : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ} (hg : Continuous g)
    (hp : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) (hb : ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) :
    ∃ B : ℝ, ∀ x : ℝ × ℝ, ‖g x‖ ≤ B := by
  set K : Set (ℝ × ℝ) := Icc (0 : ℝ) c ×ˢ Icc (-|R|) |R| with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : |x.2| ≤ |R|
  · have hper : Function.Periodic (fun t : ℝ => g (t, x.2)) c := fun t => hp (t, x.2)
    set n : ℤ := ⌊x.1 / c⌋ with hn
    have h1 : (n : ℝ) * c ≤ x.1 := by
      have := Int.floor_le (x.1 / c)
      rwa [le_div_iff₀ hc] at this
    have h2 : x.1 < ((n : ℝ) + 1) * c := by
      have := Int.lt_floor_add_one (x.1 / c)
      rwa [div_lt_iff₀ hc] at this
    have heq : g x = g (x.1 - n * c, x.2) := by
      have := hper.sub_int_mul_eq (x := x.1) n
      rw [this]
    rw [heq]
    refine le_trans (hC _ ⟨⟨?_, ?_⟩, abs_le.mp hx⟩) (le_max_left _ _)
    · linarith
    · nlinarith
  · have hgz : g x = 0 := hb x (lt_of_le_of_lt (le_abs_self R) (not_le.mp hx))
    rw [hgz, norm_zero]
    exact le_max_right _ _

/-- The bump family with inner radius `1/(2(n+1))` and outer radius `1/(n+1)`. -/
def bumpSeq (n : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith)

lemma bumpSeq_rOut_le (n : ℕ) : (bumpSeq n).rOut ≤ 1 := by
  show 1 / ((n : ℝ) + 1) ≤ 1
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

lemma bumpSeq_rOut_tendsto : Tendsto (fun n : ℕ => (bumpSeq n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The convolution `φ_n ⋆ g` of the normalized bump `φ_n` with `g`. -/
def smoothSeq (n : ℕ) (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  ((bumpSeq n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g

lemma smoothSeq_contDiff (n : ℕ) {g : ℝ × ℝ → ℂ} (hg : Continuous g) :
    ContDiff ℝ ∞ (smoothSeq n g) :=
  by
    unfold smoothSeq
    exact HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (bumpSeq n).hasCompactSupport_normed (bumpSeq n).contDiff_normed hg.locallyIntegrable

lemma smoothSeq_periodic (n : ℕ) {c : ℝ} {g : ℝ × ℝ → ℂ}
    (hgp : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) (x : ℝ × ℝ) :
    smoothSeq n g (x.1 + c, x.2) = smoothSeq n g x := by
  unfold smoothSeq
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
  congr 1
  funext t
  have e : ((x.1 + c, x.2) - t) = ((x - t).1 + c, (x - t).2) := by
    ext <;> simp <;> ring
  rw [e, hgp]

lemma smoothSeq_band (n : ℕ) {R : ℝ} {g : ℝ × ℝ → ℂ}
    (hb : ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) (x : ℝ × ℝ) (hx : R + 1 < |x.2|) :
    smoothSeq n g x = 0 := by
  unfold smoothSeq
  rw [convolution_def]
  have hz : ∀ t : ℝ × ℝ, ((bumpSeq n).normed volume t) •
      g (x - t) = 0 := by
    intro t
    by_cases ht : (bumpSeq n).normed volume t = 0
    · simp [ht]
    · have hmem : t ∈ Function.support ((bumpSeq n).normed volume) := ht
      rw [ContDiffBump.support_normed_eq, Metric.mem_ball, dist_zero_right] at hmem
      have h1 : |t.2| < 1 := by
        have := norm_snd_le t
        rw [Real.norm_eq_abs] at this
        linarith [bumpSeq_rOut_le n]
      have h3 : R < |(x - t).2| := by
        rw [Prod.snd_sub]
        have := abs_sub_abs_le_abs_sub x.2 t.2
        linarith
      rw [hb (x - t) h3, smul_zero]
  simp only [ContinuousLinearMap.lsmul_apply]
  simp [hz]

lemma smoothSeq_norm_le (n : ℕ) {g : ℝ × ℝ → ℂ} {B : ℝ} (hB : ∀ x : ℝ × ℝ, ‖g x‖ ≤ B)
    (x : ℝ × ℝ) : ‖smoothSeq n g x‖ ≤ B := by
  unfold smoothSeq
  rw [convolution_def]
  have key : ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) ((bumpSeq n).normed volume t) (g (x - t))
      ∂volume‖ ≤ ∫ t, B * (bumpSeq n).normed volume t ∂volume := by
    apply norm_integral_le_of_norm_le ((bumpSeq n).integrable_normed.const_mul B)
    refine Eventually.of_forall (fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, norm_smul]
    rw [Real.norm_of_nonneg ((bumpSeq n).nonneg_normed t), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) ((bumpSeq n).nonneg_normed t)
  rw [integral_const_mul, (bumpSeq n).integral_normed] at key
  simpa using key

/-- The measure of the cell strip `K0` is finite. -/
lemma cellMeasure_K0_lt_top (c m R : ℝ) (hc : 0 < c) :
    B0579.cellMeasure c m (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) < ⊤ := by
  set K : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨D, hD⟩ := hKc.exists_bound_of_continuousOn (B0579.continuous_jb_rpow m).continuousOn
  rw [B0579.cellMeasure, withDensity_apply _ hKm]
  have hle : ∫⁻ x in K, (B0579.density m x : ℝ≥0∞) ∂(volume.restrict (B0579.cell c))
      ≤ ∫⁻ x in K, ENNReal.ofReal D ∂(volume.restrict (B0579.cell c)) := by
    apply setLIntegral_mono' hKm
    intro x hx
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [B0579.coe_density]
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hD x hx)
  refine lt_of_le_of_lt hle ?_
  rw [setLIntegral_const]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  exact lt_of_le_of_lt (Measure.restrict_apply_le _ _) hKc.measure_lt_top

/-- The cell is `cellMeasure`-almost everywhere. -/
lemma ae_mem_cell (c m : ℝ) : ∀ᵐ x ∂(B0579.cellMeasure c m), x ∈ B0579.cell c :=
  (B0579.cellMeasure_ac c m).ae_le (ae_restrict_mem (B0579.measurableSet_cell c))

lemma eLpNorm_two_lt_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    {ε : ℝ} (hε : 0 < ε) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ENNReal.ofReal (ε ^ 2)) :
    eLpNorm f 2 μ < ENNReal.ofReal ε := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have h' : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ENNReal.ofReal (ε ^ 2) := by
    simpa only [ENNReal.rpow_two] using h
  have hfin : (ENNReal.ofReal (ε ^ 2)) ^ (1 / (2 : ℝ)) = ENNReal.ofReal ε := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hε.le]
  calc (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      < (ENNReal.ofReal (ε ^ 2)) ^ (1 / (2 : ℝ)) := ENNReal.rpow_lt_rpow h' (by norm_num)
    _ = ENNReal.ofReal ε := hfin

end DensSmoothAux

open DensSmoothAux in
theorem ladDensSmooth : LadDensSmooth := by
  intro c m hc g hg hgp hbR ε hε
  obtain ⟨R, hR⟩ := hbR
  obtain ⟨B, hB⟩ := bdd_of_periodic_band hc hg hgp hR
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set μ := B0579.cellMeasure c m with hμ
  set K0 : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(R + 1)) (R + 1) with hK0
  have hK0m : MeasurableSet K0 := measurableSet_Icc.prod measurableSet_Icc
  have hμK0 : μ K0 < ⊤ := cellMeasure_K0_lt_top c m (R + 1) hc
  have hlim : ∀ x : ℝ × ℝ, Tendsto (fun n => smoothSeq n g x) atTop (𝓝 (g x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) bumpSeq_rOut_tendsto hg x
  have hI : Tendsto (fun n => ∫⁻ x, ‖g x - smoothSeq n g x‖ₑ ^ 2 ∂μ) atTop
      (𝓝 (∫⁻ _x, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (K0.indicator fun _ => ENNReal.ofReal ((2 * B) ^ 2)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall (fun n => ?_)
      have hc' : Continuous (fun x => ‖g x - smoothSeq n g x‖ₑ ^ 2) :=
        (ENNReal.continuous_pow 2).comp ((hg.sub (smoothSeq_contDiff n hg).continuous).enorm)
      exact hc'.measurable
    · refine Eventually.of_forall (fun n => ?_)
      filter_upwards [ae_mem_cell c m] with a ha
      by_cases hs : |a.2| ≤ R + 1
      · have haK : a ∈ K0 := ⟨Ico_subset_Icc_self ha.1, abs_le.mp hs⟩
        rw [indicator_of_mem haK]
        have hb2 : ‖g a - smoothSeq n g a‖ ≤ 2 * B := by
          have := norm_sub_le (g a) (smoothSeq n g a)
          linarith [hB a, smoothSeq_norm_le n hB a]
        rw [← ofReal_norm (g a - smoothSeq n g a), ← ENNReal.ofReal_pow (norm_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        exact pow_le_pow_left₀ (norm_nonneg _) hb2 2
      · have hs' : R + 1 < |a.2| := lt_of_not_ge hs
        have hga : g a = 0 := hR a (by linarith)
        have hsa : smoothSeq n g a = 0 := smoothSeq_band n hR a hs'
        rw [hga, hsa, sub_zero, enorm_zero]
        simp
    · rw [lintegral_indicator_const hK0m]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμK0.ne
    · refine Eventually.of_forall (fun a => ?_)
      have h1 : Tendsto (fun n => g a - smoothSeq n g a) atTop (𝓝 (g a - g a)) :=
        tendsto_const_nhds.sub (hlim a)
      rw [sub_self] at h1
      have h2 : Tendsto (fun n => ‖g a - smoothSeq n g a‖ₑ ^ 2) atTop
          (𝓝 (‖(0 : ℂ)‖ₑ ^ 2)) :=
        ((ENNReal.continuous_pow 2).tendsto _).comp h1.enorm
      simpa using h2
  have hev : ∀ᶠ n in atTop, ∫⁻ x, ‖g x - smoothSeq n g x‖ₑ ^ 2 ∂μ < ENNReal.ofReal (ε ^ 2) := by
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε ^ 2) := ENNReal.ofReal_pos.2 (by positivity)
    simp only [lintegral_zero] at hI
    exact hI.eventually (gt_mem_nhds hpos)
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨smoothSeq n g, smoothSeq_contDiff n hg, smoothSeq_periodic n hgp,
    ⟨R + 1, fun x hx => smoothSeq_band n hR x hx⟩, ?_⟩
  unfold xNorm
  exact eLpNorm_two_lt_of_lintegral hε hn

end UnforcedLeray.Short.IIIa
