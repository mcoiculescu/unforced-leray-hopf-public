import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity1.Calc

/-!
# `PartIII-a:T19/2/3/2/1` helpers: joint integrability near the zero entrance

For a causal energy solution `b` (SP 3426-3440: `b ∈ 𝓗` near zero, `L²_loc` in time), the weighted
field `s^σ |b| 1_{|η| ≤ R}` is integrable on `(0, T) × cell` for every `σ > -5/4` (AM-GM against
`s^{-3/2}|b|²` near zero, the energy class away from zero). Also: a.e. slice is in `L²(cell)`,
and the train velocity is jointly measurable.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.V1

open UnforcedLeray.Short.IIIa

theorem lint_prod_eq (I : Set ℝ) (T : Set (ℝ × ℝ)) (f : ℝ × (ℝ × ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ p in I ×ˢ T, f p = ∫⁻ s in I, ∫⁻ x in T, f (s, x) := by
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict,
    lintegral_prod f hf.aemeasurable]

theorem norm_le_vnorm2 (a : Fin 2 → ℂ) (i : Fin 2) : ‖a i‖ ≤ vnorm2 a := by
  unfold vnorm2
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖a j‖ ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

theorem vnorm2_nonneg (a : Fin 2 → ℂ) : 0 ≤ vnorm2 a := Real.sqrt_nonneg _

theorem measurable_vnorm2 {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hm : ∀ i, Measurable fun p => b p i) :
    Measurable fun p => vnorm2 (b p) := by
  unfold vnorm2
  refine Measurable.sqrt ?_
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((hm i).norm).pow_const 2

/-- AM-GM with the age weights: `r^σ a β ≤ r^{-3/2} V² + r^{2σ+3/2} β`. -/
theorem amgm_age {r σ a V β : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (haV : a ≤ V) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) :
    r ^ σ * a * β ≤ r ^ (-3 / 2 : ℝ) * V ^ 2 + r ^ (2 * σ + 3 / 2) * β := by
  set x := r ^ (-3 / 4 : ℝ) * a with hx
  set y := r ^ (σ + 3 / 4) * β with hy
  have hsplit : r ^ (-3 / 4 : ℝ) * r ^ (σ + 3 / 4) = r ^ σ := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have hxy : r ^ σ * a * β = x * y := by
    rw [hx, hy, ← hsplit]; ring
  have hp1 : (r ^ (-3 / 4 : ℝ)) ^ 2 = r ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
  have hp2 : (r ^ (σ + 3 / 4)) ^ 2 = r ^ (2 * σ + 3 / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  have hx2 : x ^ 2 ≤ r ^ (-3 / 2 : ℝ) * V ^ 2 := by
    rw [hx, mul_pow, hp1]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha haV 2) (Real.rpow_nonneg hr.le _)
  have hy2 : y ^ 2 ≤ r ^ (2 * σ + 3 / 2) * β := by
    rw [hy, mul_pow, hp2]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (Real.rpow_nonneg hr.le _)
  rw [hxy]
  nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]

/-- The zero entrance in product-set form: `∫_{(0,δ)×cell} s^{-3/2}|b|² < ∞`. -/
theorem zeroEntrance_lint {c : ℝ} (hc : 0 < c) {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hm : ∀ i, Measurable fun p => b p i) {δ : ℝ}
    (hfin : ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
      ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤) :
    ∫⁻ p in Ioo 0 δ ×ˢ B0579.cell c, ENNReal.ofReal (p.1 ^ (-3 / 2 : ℝ) * vnorm2 (b p) ^ 2) < ⊤ := by
  set g : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (vnorm2 (b p) ^ 2) with hg_def
  have hgm : Measurable g := ((measurable_vnorm2 hm).pow_const 2).ennreal_ofReal
  set S : Set (ℝ × (ℝ × ℝ)) := Ioo (0 : ℝ) δ ×ˢ (univ : Set (ℝ × ℝ)) with hS_def
  have hS : MeasurableSet S := measurableSet_Ioo.prod MeasurableSet.univ
  rw [← lintegral_indicator hS, lintegral_ageμ hc _ (hgm.indicator hS)] at hfin
  set A : Set (ℝ × (ℝ × ℝ)) := Ioo (0 : ℝ) δ ×ˢ B0579.cell c with hA_def
  set B : Set (ℝ × (ℝ × ℝ)) := Ioi (0 : ℝ) ×ˢ qCell c with hB_def
  have hA : MeasurableSet A := measurableSet_Ioo.prod (B0579.measurableSet_cell c)
  have hB : MeasurableSet B := measurableSet_Ioi.prod (by
    rw [qCell_eq_cell, ← cell_eq]; exact B0579.measurableSet_cell c)
  have hAB : A ⊆ B := by
    intro p hp
    refine ⟨hp.1.1, ?_⟩
    rw [qCell_eq_cell, ← cell_eq]; exact hp.2
  set F : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (p.1 ^ (-3 / 2 : ℝ) * vnorm2 (b p) ^ 2)
  have h1 : ∫⁻ p in A, F p = ∫⁻ p in B, A.indicator F p := by
    rw [setLIntegral_indicator hA, inter_eq_left.2 hAB]
  have h2 : ∫⁻ p in B, A.indicator F p ≤
      ∫⁻ p in B, ENNReal.ofReal c * (ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) * S.indicator g p) := by
    refine setLIntegral_mono' hB fun p hpB => ?_
    by_cases hpA : p ∈ A
    · have hpS : p ∈ S := ⟨hpA.1, trivial⟩
      have hp1 : 0 < p.1 := hpA.1.1
      rw [indicator_of_mem hpA, indicator_of_mem hpS]
      simp only [F, hg_def]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc.le]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      field_simp
    · rw [indicator_of_notMem hpA]; exact bot_le
  have h3 : ∫⁻ p in B, ENNReal.ofReal c *
      (ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) * S.indicator g p) =
      ENNReal.ofReal c * ∫⁻ p in B, ENNReal.ofReal (c⁻¹ * p.1 ^ (-3 / 2 : ℝ)) * S.indicator g p :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc ∫⁻ p in A, F p = ∫⁻ p in B, A.indicator F p := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem energyLoc_lint {c ν : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hb : IsCausalEnergySolution c ν μ vel F b G)
    {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ < s₂) :
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun p => ?_) (hb.energyLoc s₁ s₂ h1 h12)
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (sq_nonneg _))

theorem lint_band_Icc (c R a T : ℝ) :
    ∫⁻ p in Icc a T ×ˢ B0579.cell c, ENNReal.ofReal ((Icc (-R) R).indicator 1 p.2.2) < ⊤ := by
  set K : Set (ℝ × (ℝ × ℝ)) := Icc a T ×ˢ B0579.box c R
  have hK : IsCompact K := isCompact_Icc.prod (B0579.isCompact_box c R)
  have hmeas : MeasurableSet (Icc a T ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (B0579.measurableSet_cell c)
  calc ∫⁻ p in Icc a T ×ˢ B0579.cell c, ENNReal.ofReal ((Icc (-R) R).indicator 1 p.2.2)
      ≤ ∫⁻ p in Icc a T ×ˢ B0579.cell c, K.indicator 1 p := by
        refine setLIntegral_mono' hmeas fun p hp => ?_
        by_cases hR : p.2.2 ∈ Icc (-R) R
        · have hpK : p ∈ K := ⟨hp.1, B0579.mem_box_of_mem_cell hp.2 (abs_le.2 hR)⟩
          rw [indicator_of_mem hR, indicator_of_mem hpK]; simp
        · rw [indicator_of_notMem hR]; simp
    _ ≤ ∫⁻ p, K.indicator 1 p := setLIntegral_le_lintegral _ _
    _ = volume K := lintegral_indicator_one hK.measurableSet
    _ < ⊤ := hK.measure_lt_top

theorem lint_rpow_band (c R d e : ℝ) (hd : 0 < d) (he : -1 < e) :
    ∫⁻ p in Ioo 0 d ×ˢ B0579.cell c,
      ENNReal.ofReal (p.1 ^ e) * ENNReal.ofReal ((Icc (-R) R).indicator 1 p.2.2) < ⊤ := by
  have hmeas : MeasurableSet (Ioo 0 d ×ˢ B0579.cell c) :=
    measurableSet_Ioo.prod (B0579.measurableSet_cell c)
  have hbox : MeasurableSet (B0579.box c R) := (B0579.isCompact_box c R).measurableSet
  have hI : ∫⁻ r in Ioo 0 d, ENNReal.ofReal (r ^ e) < ⊤ :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hd).2 he).lintegral_lt_top
  calc ∫⁻ p in Ioo 0 d ×ˢ B0579.cell c,
        ENNReal.ofReal (p.1 ^ e) * ENNReal.ofReal ((Icc (-R) R).indicator 1 p.2.2)
      ≤ ∫⁻ p in Ioo 0 d ×ˢ B0579.cell c,
          ENNReal.ofReal (p.1 ^ e) * (B0579.box c R).indicator 1 p.2 := by
        refine setLIntegral_mono' hmeas fun p hp => ?_
        refine mul_le_mul' le_rfl ?_
        by_cases hR : p.2.2 ∈ Icc (-R) R
        · have hpK : p.2 ∈ B0579.box c R := B0579.mem_box_of_mem_cell hp.2 (abs_le.2 hR)
          rw [indicator_of_mem hR, indicator_of_mem hpK]; simp
        · rw [indicator_of_notMem hR]; simp
    _ ≤ ∫⁻ p in Ioo 0 d ×ˢ (univ : Set (ℝ × ℝ)),
          ENNReal.ofReal (p.1 ^ e) * (B0579.box c R).indicator 1 p.2 :=
        lintegral_mono_set (prod_mono le_rfl (subset_univ _))
    _ = (∫⁻ r in Ioo 0 d, ENNReal.ofReal (r ^ e)) * ∫⁻ x, (B0579.box c R).indicator 1 x := by
        rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict, Measure.restrict_univ]
        exact lintegral_prod_mul
          ((ENNReal.measurable_ofReal.comp (measurable_id.pow_const e)).aemeasurable)
          ((measurable_const.indicator hbox).aemeasurable)
    _ < ⊤ := by
        rw [lintegral_indicator_one hbox]
        exact ENNReal.mul_lt_top hI (B0579.isCompact_box c R).measure_lt_top

/-- **Joint integrability near the zero entrance.** For `σ > -5/4`,
`∫_{(0,T) × cell} s^σ |b_i| 1_{|η| ≤ R} < ∞`. -/
theorem lint_weighted_lt_top {c ν : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hc : 0 < c)
    (hb : IsCausalEnergySolution c ν μ vel F b G) {σ : ℝ} (hσ : -5 / 4 < σ) (T R : ℝ)
    (i : Fin 2) :
    ∫⁻ p in Ioo 0 T ×ˢ B0579.cell c,
      ENNReal.ofReal (p.1 ^ σ * ‖b p i‖ * (Icc (-R) R).indicator 1 p.2.2) < ⊤ := by
  by_cases hT : T ≤ 0
  · have : Ioo (0 : ℝ) T ×ˢ B0579.cell c = ∅ := by
      rw [Ioo_eq_empty (not_lt.2 hT), empty_prod]
    rw [this, Measure.restrict_empty, lintegral_zero_measure]
    exact ENNReal.zero_lt_top
  push Not at hT
  obtain ⟨δ, hδ, hfin⟩ := hb.zeroEntrance
  set d := min δ T with hd_def
  have hd : 0 < d := lt_min hδ hT
  have hdδ : d ≤ δ := min_le_left _ _
  have hdT : d ≤ T := min_le_right _ _
  have hZE := zeroEntrance_lint hc hb.measurable hfin
  have hZE' : ∫⁻ p in Ioo 0 d ×ˢ B0579.cell c,
      ENNReal.ofReal (p.1 ^ (-3 / 2 : ℝ) * vnorm2 (b p) ^ 2) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set (prod_mono (Ioo_subset_Ioo_right hdδ) le_rfl)) hZE
  have hEL := energyLoc_lint hb (half_pos hd) (by linarith : d / 2 < T)
  set β : ℝ × (ℝ × ℝ) → ℝ := fun p => (Icc (-R) R).indicator 1 p.2.2 with hβ_def
  have hβ0 : ∀ p, 0 ≤ β p := fun p => by
    simp only [hβ_def]; by_cases h : p.2.2 ∈ Icc (-R) R <;> simp [h]
  have hβ1 : ∀ p, β p ≤ 1 := fun p => by
    simp only [hβ_def]; by_cases h : p.2.2 ∈ Icc (-R) R <;> simp [h]
  have hβm : Measurable β :=
    (measurable_const.indicator measurableSet_Icc).comp (measurable_snd.comp measurable_snd)
  have hVm := measurable_vnorm2 hb.measurable
  set S₁ := Ioo (0 : ℝ) d ×ˢ B0579.cell c
  set S₂ := Icc (d / 2) T ×ˢ B0579.cell c
  have hS₁ : MeasurableSet S₁ := measurableSet_Ioo.prod (B0579.measurableSet_cell c)
  have hS₂ : MeasurableSet S₂ := measurableSet_Icc.prod (B0579.measurableSet_cell c)
  have hsub : Ioo 0 T ×ˢ B0579.cell c ⊆ S₁ ∪ S₂ := by
    intro p hp
    by_cases h : p.1 < d
    · exact Or.inl ⟨⟨hp.1.1, h⟩, hp.2⟩
    · exact Or.inr ⟨⟨by linarith, hp.1.2.le⟩, hp.2⟩
  set f : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (p.1 ^ σ * ‖b p i‖ * β p)
  -- the piece near zero
  have hf₁ : ∫⁻ p in S₁, f p ≤
      ∫⁻ p in S₁, (ENNReal.ofReal (p.1 ^ (-3 / 2 : ℝ) * vnorm2 (b p) ^ 2) +
        ENNReal.ofReal (p.1 ^ (2 * σ + 3 / 2)) * ENNReal.ofReal (β p)) := by
    refine setLIntegral_mono' hS₁ fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1.1
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hp1.le _), ← ENNReal.ofReal_add
      (mul_nonneg (Real.rpow_nonneg hp1.le _) (sq_nonneg _))
      (mul_nonneg (Real.rpow_nonneg hp1.le _) (hβ0 p))]
    exact ENNReal.ofReal_le_ofReal (amgm_age hp1 (norm_nonneg _) (norm_le_vnorm2 _ i) (hβ0 p)
      (hβ1 p))
  have hf₁' : ∫⁻ p in S₁, (ENNReal.ofReal (p.1 ^ (-3 / 2 : ℝ) * vnorm2 (b p) ^ 2) +
        ENNReal.ofReal (p.1 ^ (2 * σ + 3 / 2)) * ENNReal.ofReal (β p)) < ⊤ := by
    rw [lintegral_add_left]
    · exact ENNReal.add_lt_top.2 ⟨hZE', lint_rpow_band c R d _ hd (by linarith)⟩
    · exact ((measurable_fst.pow_const _).mul (hVm.pow_const 2)).ennreal_ofReal
  -- the piece away from zero
  set C : ℝ := (d / 2) ^ σ + T ^ σ
  have hC : ∀ r ∈ Icc (d / 2) T, r ^ σ ≤ C := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le (half_pos hd) hr.1
    rcases le_or_gt 0 σ with hσ0 | hσ0
    · have := Real.rpow_le_rpow hr0.le hr.2 hσ0
      have := Real.rpow_nonneg (half_pos hd).le σ
      simp only [C]; linarith
    · have := Real.rpow_le_rpow_of_nonpos (half_pos hd) hr.1 hσ0.le
      have := Real.rpow_nonneg hT.le σ
      simp only [C]; linarith
  have hf₂ : ∫⁻ p in S₂, f p ≤
      ∫⁻ p in S₂, ENNReal.ofReal C *
        (ENNReal.ofReal (vnorm2 (b p) ^ 2) + ENNReal.ofReal (β p)) := by
    refine setLIntegral_mono' hS₂ fun p hp => ?_
    have hp1 : 0 < p.1 := lt_of_lt_of_le (half_pos hd) hp.1.1
    have hC0 : 0 ≤ C := le_trans (Real.rpow_nonneg hp1.le σ) (hC p.1 hp.1)
    rw [← ENNReal.ofReal_add (sq_nonneg _) (hβ0 p), ← ENNReal.ofReal_mul hC0]
    refine ENNReal.ofReal_le_ofReal ?_
    have ha := norm_le_vnorm2 (b p) i
    have hab : ‖b p i‖ * β p ≤ vnorm2 (b p) ^ 2 + β p := by
      have h0 := norm_nonneg (b p i)
      nlinarith [hβ0 p, hβ1 p, sq_nonneg (‖b p i‖ - β p)]
    calc p.1 ^ σ * ‖b p i‖ * β p = p.1 ^ σ * (‖b p i‖ * β p) := by ring
      _ ≤ C * (vnorm2 (b p) ^ 2 + β p) :=
        mul_le_mul (hC p.1 hp.1) hab (mul_nonneg (norm_nonneg _) (hβ0 p)) hC0
  have hf₂' : ∫⁻ p in S₂, ENNReal.ofReal C *
      (ENNReal.ofReal (vnorm2 (b p) ^ 2) + ENNReal.ofReal (β p)) < ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left]
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.2 ⟨hEL, lint_band_Icc c R (d / 2) T⟩)
    · exact (hVm.pow_const 2).ennreal_ofReal
  calc ∫⁻ p in Ioo 0 T ×ˢ B0579.cell c, f p ≤ ∫⁻ p in S₁ ∪ S₂, f p := lintegral_mono_set hsub
    _ ≤ (∫⁻ p in S₁, f p) + ∫⁻ p in S₂, f p := lintegral_union_le _ _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt hf₁ hf₁', lt_of_le_of_lt hf₂ hf₂'⟩

/-- **Complex form.** `s^μ' b_i k` is integrable on `(0,T) × cell` when `Re μ' > -5/4` and
`|k| ≤ M 1_{|η| ≤ R}` there. -/
theorem integrableOn_cpow_mul {c ν : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hc : 0 < c)
    (hb : IsCausalEnergySolution c ν μ vel F b G) {μ' : ℂ} (hσ : -5 / 4 < μ'.re) (T : ℝ)
    (i : Fin 2) {k : ℝ × (ℝ × ℝ) → ℂ}
    (hk : AEStronglyMeasurable k (volume.restrict (Ioo 0 T ×ˢ B0579.cell c))) {M R : ℝ}
    (hM : 0 ≤ M)
    (hkb : ∀ p ∈ Ioo 0 T ×ˢ B0579.cell c, ‖k p‖ ≤ M * (Icc (-R) R).indicator 1 p.2.2) :
    IntegrableOn (fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ μ' * (b p i * k p))
      (Ioo 0 T ×ˢ B0579.cell c) := by
  have hmeas : MeasurableSet (Ioo 0 T ×ˢ B0579.cell c) :=
    measurableSet_Ioo.prod (B0579.measurableSet_cell c)
  have hcp : Measurable fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ μ' :=
    (Complex.measurable_ofReal.comp measurable_fst).pow_const μ'
  refine ⟨hcp.aestronglyMeasurable.mul ((hb.measurable i).aestronglyMeasurable.mul hk), ?_⟩
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := M))
    (lint_weighted_lt_top hc hb hσ T R i))
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hmeas fun p hp => ?_
  have hp1 : 0 < p.1 := hp.1.1
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hM]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp1]
  have h1 := hkb p hp
  have h2 : 0 ≤ p.1 ^ μ'.re * ‖b p i‖ := mul_nonneg (Real.rpow_nonneg hp1.le _) (norm_nonneg _)
  calc p.1 ^ μ'.re * (‖b p i‖ * ‖k p‖) = (p.1 ^ μ'.re * ‖b p i‖) * ‖k p‖ := by ring
    _ ≤ (p.1 ^ μ'.re * ‖b p i‖) * (M * (Icc (-R) R).indicator 1 p.2.2) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = M * (p.1 ^ μ'.re * ‖b p i‖ * (Icc (-R) R).indicator 1 p.2.2) := by ring

/-! ## Slices in `L²(cell)` -/

theorem memLp_two_of_lint {c : ℝ} {φ : ℝ × ℝ → ℂ}
    (hφ : AEStronglyMeasurable φ (volume.restrict (B0579.cell c))) {g : ℝ × ℝ → ℝ}
    (hg : ∀ x, ‖φ x‖ ^ 2 ≤ g x) (hfin : ∫⁻ x in B0579.cell c, ENNReal.ofReal (g x) < ⊤) :
    MemLp φ 2 (volume.restrict (B0579.cell c)) := by
  refine ⟨hφ, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  have h2 : ENNReal.toReal 2 = 2 := by norm_num
  rw [h2, ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hg x)

/-- Almost every positive slice of a causal energy solution is in `L²(cell)`. -/
theorem ae_slice_memLp {c ν : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hb : IsCausalEnergySolution c ν μ vel F b G) :
    ∀ᵐ r ∂volume, 0 < r → ∀ i, MemLp (fun x => b (r, x) i) 2 (volume.restrict (B0579.cell c)) := by
  have hgm : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (b p) ^ 2) :=
    ((measurable_vnorm2 hb.measurable).pow_const 2).ennreal_ofReal
  have key : ∀ n : ℕ, ∀ᵐ r ∂volume, r ∈ Icc (((n : ℝ) + 2)⁻¹) ((n : ℝ) + 2) →
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (b (r, x)) ^ 2) < ⊤ := by
    intro n
    have h0 : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := by positivity
    have h1 : ((n : ℝ) + 2)⁻¹ < (n : ℝ) + 2 := by
      have : ((n : ℝ) + 2)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
      linarith [n.cast_nonneg (α := ℝ)]
    have hfin := energyLoc_lint hb h0 h1
    rw [lint_prod_eq _ _ _ hgm] at hfin
    have hm : Measurable fun s : ℝ => ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (b (s, x)) ^ 2) :=
      hgm.lintegral_prod_right'
    have hae := ae_lt_top hm hfin.ne
    rwa [ae_restrict_iff' measurableSet_Icc] at hae
  have hall := ae_all_iff.2 key
  filter_upwards [hall] with r hr hr0 i
  obtain ⟨n, hn⟩ := exists_nat_ge (max r r⁻¹)
  have hrn : r ≤ (n : ℝ) + 2 := by linarith [le_max_left r r⁻¹]
  have hrn' : ((n : ℝ) + 2)⁻¹ ≤ r := by
    rw [inv_le_comm₀ (by positivity) hr0]; linarith [le_max_right r r⁻¹]
  have hfin := hr n ⟨hrn', hrn⟩
  refine memLp_two_of_lint ((hb.measurable i).comp measurable_prodMk_left).aestronglyMeasurable
    (g := fun x => vnorm2 (b (r, x)) ^ 2) (fun x => ?_) hfin
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_vnorm2 _ i) 2

/-! ## The train velocity -/

theorem measurable_trainVel {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (k : Fin 2) :
    Measurable fun p : ℝ × (ℝ × ℝ) => trainVel tr p.1 p.2 k := by
  classical
  have hcont : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 k) {p | 0 ≤ p.1} := by
    have h := tr.isTrain.smooth_v.continuousOn
    exact ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_continuousOn h).mono
      (fun p hp => ⟨hp, trivial⟩)
  have heq : (fun p : ℝ × (ℝ × ℝ) => trainVel tr p.1 p.2 k) =
      {p : ℝ × (ℝ × ℝ) | 0 ≤ p.1}.piecewise (fun p => tr.v p.1 p.2 k) (fun _ => 0) := by
    funext p
    by_cases h : 0 ≤ p.1 <;> simp [trainVel, Set.piecewise, h]
  rw [heq]
  exact hcont.measurable_piecewise continuousOn_const
    (measurableSet_le measurable_const measurable_fst)

theorem trainVel_bound {ν c : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc (0 : ℝ) T, ∀ x : ℝ × ℝ, ∀ k : Fin 2, |trainVel tr s x k| ≤ M := by
  obtain ⟨M, hM⟩ := hbuc.sup_bound hT
  refine ⟨max M 0, le_max_right _ _, fun s hs x k => ?_⟩
  simp only [trainVel, hs.1, ite_true]
  calc |tr.v s x k| = ‖tr.v s x k‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖tr.v s x‖ := PiLp.norm_apply_le _ k
    _ ≤ M := hM s hs x
    _ ≤ max M 0 := le_max_left _ _

end UnforcedLeray.Short.IIIa.V1

end
