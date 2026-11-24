import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2

/-!
# Helper for `PartII-b:T11/2/2/2` (`DualTestEq`): integrability on the cell measure

If `b ∈ H_r` and `w` is a continuous field vanishing outside `σ₀ ≤ σ ≤ H`, `|η| ≤ L`
(`σ₀ > 0`), then `Σ b_i w_i` is integrable for `ageμ c 0`: on that box the weight `σ^{r/2-5/2}`
of `H_r` is bounded below, so `b ∈ L^r` of the box measure, hence `L^1` (finite measure).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

instance sFinite_avgμ_dt (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ; infer_instance

/-- the box `σ₀ ≤ σ ≤ H`, `|η| ≤ L`. -/
def dtBox (σ₀ H L : ℝ) : Set Coord := Icc σ₀ H ×ˢ (univ ×ˢ Icc (-L) L)

theorem measurableSet_dtBox (σ₀ H L : ℝ) : MeasurableSet (dtBox σ₀ H L) :=
  measurableSet_Icc.prod (MeasurableSet.univ.prod measurableSet_Icc)

theorem ageμ_zero_dtBox_lt_top {c : ℝ} (hc : 0 < c) (σ₀ H L : ℝ) :
    Axi.ageμ c 0 (dtBox σ₀ H L) < ⊤ := by
  unfold dtBox Axi.ageμ
  rw [Measure.prod_prod, Cyl.avgμ_univ_prod hc]
  refine ENNReal.mul_lt_top ?_ measure_Icc_lt_top
  rw [withDensity_apply _ measurableSet_Icc]
  simp only [Real.rpow_zero, ENNReal.ofReal_one, lintegral_const, one_mul]
  exact lt_of_le_of_lt ((Measure.restrict_apply_univ _).trans_le (Measure.restrict_apply_le _ _))
    measure_Icc_lt_top

/-- a.e. for the cell measure, `q ∈ [-c/2, c/2)`. -/
theorem ae_ageμ_q_mem {c : ℝ} (a : ℝ) : ∀ᵐ x ∂(Axi.ageμ c a), x.2.1 ∈ Ico (-c / 2) (c / 2) := by
  rw [ae_iff]
  unfold Axi.ageμ
  have hm : MeasurableSet {x : Coord | ¬ x.2.1 ∈ Ico (-c / 2) (c / 2)} := by
    have : MeasurableSet (univ ×ˢ ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) : Set Coord) :=
      MeasurableSet.univ.prod (measurableSet_Ico.compl.prod MeasurableSet.univ)
    convert this using 1
    ext x; simp
  have heq : {x : Coord | ¬ x.2.1 ∈ Ico (-c / 2) (c / 2)} =
      (univ : Set ℝ) ×ˢ ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) := by
    ext x; simp
  rw [heq, Measure.prod_prod]
  have : Cyl.avgμ c ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Cyl.avgμ, Measure.smul_apply, Cyl.cellμ, Measure.restrict_apply
      (measurableSet_Ico.compl.prod MeasurableSet.univ)]
    have : (Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ) ∩ Cyl.cell c = ∅ := by
      ext x; simp [Cyl.cell]
    simp [this]
  simp [this]

/-- comparison of the box measures: `ageμ c 0 ≤ C • ageμ c a` on the box. -/
theorem ageμ_restrict_le {c : ℝ} (hc : 0 < c) (a σ₀ H L : ℝ) (hσ : 0 < σ₀) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      (Axi.ageμ c 0).restrict (dtBox σ₀ H L) ≤ C • (Axi.ageμ c a).restrict (dtBox σ₀ H L) := by
  by_cases hH : σ₀ ≤ H
  · have hcont : ContinuousOn (fun t : ℝ => t ^ a) (Icc σ₀ H) :=
      ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (by
        have h1 := hx.1; exact ne_of_gt (lt_of_lt_of_le hσ h1))
    obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hH) hcont
    have hm : 0 < t0 ^ a := Real.rpow_pos_of_pos (lt_of_lt_of_le hσ ht0.1) a
    refine ⟨ENNReal.ofReal ((t0 ^ a)⁻¹), ENNReal.ofReal_ne_top, ?_⟩
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    have hs' : MeasurableSet (s ∩ dtBox σ₀ H L) := hs.inter (measurableSet_dtBox _ _ _)
    rw [← lintegral_indicator_one hs', ← lintegral_indicator_one hs',
      Axi.lintegral_ageμ hc 0 (measurable_one.indicator hs'),
      Axi.lintegral_ageμ hc a (measurable_one.indicator hs'),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    refine Filter.Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ s ∩ dtBox σ₀ H L
    · simp only [indicator_of_mem hp, Pi.one_apply, mul_one]
      have hp1 : p.1 ∈ Icc σ₀ H := hp.2.1
      have hle : t0 ^ a ≤ p.1 ^ a := hmin hp1
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hm.le)]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_zero]
      have : (t0 ^ a)⁻¹ * (c⁻¹ * p.1 ^ a) ≥ c⁻¹ := by
        have h1 : 1 ≤ (t0 ^ a)⁻¹ * p.1 ^ a := by
          rw [inv_mul_eq_div, le_div_iff₀ hm]; linarith
        calc c⁻¹ = c⁻¹ * 1 := by ring
          _ ≤ c⁻¹ * ((t0 ^ a)⁻¹ * p.1 ^ a) := by gcongr
          _ = _ := by ring
      linarith
    · simp [indicator_of_notMem hp]
  · refine ⟨0, ENNReal.zero_ne_top, ?_⟩
    have : dtBox σ₀ H L = ∅ := by
      ext x; simp only [dtBox, mem_prod, mem_Icc, mem_univ, true_and, mem_empty_iff_false,
        iff_false]
      rintro ⟨⟨h1, h2⟩, -⟩; exact hH (h1.trans h2)
    simp [this]

/-- `b ∈ H_r` is integrable on the box for the cell measure `ageμ c 0`. -/
theorem integrableOn_box {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {b : CProf} (hb : InHr c r b)
    (σ₀ H L : ℝ) (hσ : 0 < σ₀) :
    IntegrableOn b (dtBox σ₀ H L) (Axi.ageμ c 0) := by
  obtain ⟨C, hC, hle⟩ := ageμ_restrict_le hc (r / 2 - 5 / 2) σ₀ H L hσ
  have hmem : MemLp b (ENNReal.ofReal r) (hMeas c r) := ⟨hb.meas, hb.finite⟩
  have h1 : MemLp b (ENNReal.ofReal r) ((hMeas c r).restrict (dtBox σ₀ H L)) :=
    hmem.mono_measure Measure.restrict_le_self
  have h2 : MemLp b (ENNReal.ofReal r)
      (C • (hMeas c r).restrict (dtBox σ₀ H L)) := h1.smul_measure hC
  have h3 : MemLp b (ENNReal.ofReal r) ((Axi.ageμ c 0).restrict (dtBox σ₀ H L)) :=
    h2.mono_measure hle
  have : IsFiniteMeasure ((Axi.ageμ c 0).restrict (dtBox σ₀ H L)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact ageμ_zero_dtBox_lt_top hc _ _ _⟩
  have h4 : MemLp b 1 ((Axi.ageμ c 0).restrict (dtBox σ₀ H L)) :=
    h3.mono_exponent (by
      have : (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      rw [this]; exact ENNReal.ofReal_le_ofReal hr.le)
  exact memLp_one_iff_integrable.1 h4

/-- **Integrability lemma.** -/
theorem integrable_pair_of_box {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {b : CProf} (hb : InHr c r b)
    (σ₀ H L : ℝ) (hσ : 0 < σ₀) (w : Coord → Fin 2 → ℂ)
    (hw : ∀ i, Continuous fun x => w x i)
    (hvan : ∀ x, x ∉ dtBox σ₀ H L → ∀ i, w x i = 0) :
    Integrable (fun x => ∑ i : Fin 2, b x i * w x i) (Axi.ageμ c 0) := by
  have hbox := integrableOn_box hc hr hb σ₀ H L hσ
  set K : Set Coord := Icc σ₀ H ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L) with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    (f := fun x => ‖w x 0‖ + ‖w x 1‖)
    (((hw 0).norm.add (hw 1).norm).continuousOn)
  have hbound : ∀ᵐ x ∂(Axi.ageμ c 0), x ∈ dtBox σ₀ H L →
      ‖∑ i : Fin 2, b x i * w x i‖ ≤ M * ‖b x‖ := by
    filter_upwards [ae_ageμ_q_mem (c := c) 0] with x hq hx
    have hxK : x ∈ K := by
      refine ⟨hx.1, ⟨?_, ?_⟩, hx.2.2⟩
      · have := hq.1; have : -c / 2 ≤ x.2.1 := this; exact this
      · exact hq.2.le
    have hMx := hM x hxK
    have hMx : ‖w x 0‖ + ‖w x 1‖ ≤ M := by
      have := hMx; rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    calc ‖∑ i : Fin 2, b x i * w x i‖ ≤ ∑ i : Fin 2, ‖b x i * w x i‖ := norm_sum_le _ _
      _ = ‖b x 0‖ * ‖w x 0‖ + ‖b x 1‖ * ‖w x 1‖ := by
          simp [Fin.sum_univ_two, norm_mul]
      _ ≤ ‖b x‖ * ‖w x 0‖ + ‖b x‖ * ‖w x 1‖ := by
          gcongr
          · exact PiLp.norm_apply_le (b x) 0
          · exact PiLp.norm_apply_le (b x) 1
      _ = ‖b x‖ * (‖w x 0‖ + ‖w x 1‖) := by ring
      _ ≤ ‖b x‖ * M := by gcongr
      _ = M * ‖b x‖ := by ring
  have hmeas : AEStronglyMeasurable (fun x => ∑ i : Fin 2, b x i * w x i)
      ((Axi.ageμ c 0).restrict (dtBox σ₀ H L)) := by
    have hb' := hbox.aestronglyMeasurable
    have hbi : ∀ i : Fin 2, AEStronglyMeasurable (fun x => b x i)
        ((Axi.ageμ c 0).restrict (dtBox σ₀ H L)) := fun i =>
      ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hb')
    have := Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin 2))
      (f := fun i x => b x i * w x i) fun i _ => (hbi i).mul (hw i).aestronglyMeasurable
    exact this
  have hon : IntegrableOn (fun x => ∑ i : Fin 2, b x i * w x i) (dtBox σ₀ H L)
      (Axi.ageμ c 0) := by
    refine Integrable.mono' (hbox.norm.const_mul M) hmeas ?_
    refine (ae_restrict_iff' (measurableSet_dtBox _ _ _)).2 ?_
    filter_upwards [hbound] with x hx hxs using hx hxs
  have hsupp : Function.support (fun x => ∑ i : Fin 2, b x i * w x i) ⊆ dtBox σ₀ H L := by
    intro x hx
    by_contra hxn
    exact hx (by simp [hvan x hxn])
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hon

end UnforcedLeray.Short.IIb
