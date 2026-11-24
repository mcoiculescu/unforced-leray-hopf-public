import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F4
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Helper for `PartII-b:F2/2/1`: Bochner integrability and time continuity of Duhamel integrals

Using `PartIIbF4Aux.integrableOn_propagator_apply`, proves interval integrability and final-time
continuity `ContinuousOn (fun t => ∫ r in s₀..t, P t r (g r)) (Icc s₀ H)` for any strongly
right-continuous cocycle `P` on `[0, H]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.MildDuhamelAux

/-- Joint evaluation continuity `r ↦ Ac r (v r)` on `Icc s₀ H` from strong continuity and uniform
operator-norm bound of `Ac`. -/
theorem continuousOn_op_apply_of_norm_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {H M_A s₀ : ℝ} {Ac : ℝ → (X →L[ℝ] X)} {v : ℝ → X}
    (hs₀ : s₀ ∈ Icc 0 H)
    (hAc_cont : ∀ y : X, ContinuousOn (fun r => Ac r y) (Icc 0 H))
    (hAc_bd : ∀ r ∈ Icc 0 H, ‖Ac r‖ ≤ M_A)
    (hv : ContinuousOn v (Icc s₀ H)) :
    ContinuousOn (fun r => Ac r (v r)) (Icc s₀ H) := by
  intro r₀ hr₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hv0 : Tendsto (fun r => ‖v r - v r₀‖) (𝓝[Icc s₀ H] r₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (hv r₀ hr₀)
  have hAc0 : Tendsto (fun r => ‖Ac r (v r₀) - Ac r₀ (v r₀)‖) (𝓝[Icc s₀ H] r₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp
      ((hAc_cont (v r₀)).mono (Icc_subset_Icc_left hs₀.1) r₀ hr₀)
  have hmaj0 : Tendsto (fun r => M_A * ‖v r - v r₀‖ + ‖Ac r (v r₀) - Ac r₀ (v r₀)‖)
      (𝓝[Icc s₀ H] r₀) (𝓝 0) := by
    have h := (hv0.const_mul M_A).add hAc0
    rwa [mul_zero, add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj0
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr_0H : r ∈ Icc 0 H := ⟨hs₀.1.trans hr.1, hr.2⟩
  have hsplit : Ac r (v r) - Ac r₀ (v r₀) =
      Ac r (v r - v r₀) + (Ac r (v r₀) - Ac r₀ (v r₀)) := by
    rw [map_sub]
    abel
  rw [hsplit]
  calc ‖Ac r (v r - v r₀) + (Ac r (v r₀) - Ac r₀ (v r₀))‖
      ≤ ‖Ac r (v r - v r₀)‖ + ‖Ac r (v r₀) - Ac r₀ (v r₀)‖ := norm_add_le _ _
    _ ≤ ‖Ac r‖ * ‖v r - v r₀‖ + ‖Ac r (v r₀) - Ac r₀ (v r₀)‖ :=
        add_le_add ((Ac r).le_opNorm _) le_rfl
    _ ≤ M_A * ‖v r - v r₀‖ + ‖Ac r (v r₀) - Ac r₀ (v r₀)‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (hAc_bd r hr_0H) (norm_nonneg _)) le_rfl

/-- Interval Bochner integrability of `r ↦ P t r (g r)` on `[a, b]` (`0 ≤ a ≤ b ≤ t ≤ H`) from
`PartIIbF4Aux.integrableOn_propagator_apply`. -/
theorem intervalIntegrable_propagator_apply
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {H M_P a b t : ℝ} {P : ℝ → ℝ → (X →L[ℝ] X)} {g : ℝ → X}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b ≤ t) (htH : t ≤ H) (hM_P : 0 ≤ M_P)
    (hP_id : ∀ r ∈ Icc 0 H, P r r = ContinuousLinearMap.id ℝ X)
    (hP_coc : ∀ u v w : ℝ, 0 ≤ u → u ≤ v → v ≤ w → w ≤ H → (P w v).comp (P v u) = P w u)
    (hP_cont : ∀ u ∈ Icc 0 H, ∀ y : X, ContinuousOn (fun v => P v u y) (Icc u H))
    (hP_bd : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ H → ‖P v u‖ ≤ M_P)
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun r => P t r (g r)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hg ⊢
  let g_ext : ℝ → X := (Ioc a b).indicator g
  have hg_ext : IntegrableOn g_ext (Ioc 0 t) volume :=
    ((integrable_indicator_iff measurableSet_Ioc).2 hg).integrableOn
  have ht_Icc : t ∈ Icc 0 H := ⟨ha.trans (hab.trans hbt), htH⟩
  have hint0 := PartIIbF4Aux.integrableOn_propagator_apply ht_Icc hM_P
    hP_id hP_coc hP_cont hP_bd hg_ext
  have hsub : Ioc a b ⊆ Ioc 0 t := Ioc_subset_Ioc ha hbt
  refine (hint0.mono_set hsub).congr_fun (fun r hr => ?_) measurableSet_Ioc
  simp [g_ext, hr]

/-- Continuity of `t ↦ ∫ r in s₀..t, P t r (g r)` on `Icc s₀ H` when `g` is continuous on
`Icc s₀ H`. -/
theorem continuousOn_propagator_intervalIntegral
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {H M_P s₀ : ℝ} {P : ℝ → ℝ → (X →L[ℝ] X)} {g : ℝ → X}
    (hs₀ : s₀ ∈ Icc 0 H) (hM_P : 0 ≤ M_P)
    (hP_id : ∀ r ∈ Icc 0 H, P r r = ContinuousLinearMap.id ℝ X)
    (hP_coc : ∀ u v w : ℝ, 0 ≤ u → u ≤ v → v ≤ w → w ≤ H → (P w v).comp (P v u) = P w u)
    (hP_cont : ∀ u ∈ Icc 0 H, ∀ y : X, ContinuousOn (fun v => P v u y) (Icc u H))
    (hP_bd : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ H → ‖P v u‖ ≤ M_P)
    (hg : ContinuousOn g (Icc s₀ H)) :
    ContinuousOn (fun t => ∫ r in s₀..t, P t r (g r)) (Icc s₀ H) := by
  obtain ⟨C_g0, hCg0⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  set C_g : ℝ := max C_g0 0
  have _hCg_nn : 0 ≤ C_g := le_max_right _ _
  have hg_bd : ∀ r ∈ Icc s₀ H, ‖g r‖ ≤ C_g :=
    fun r hr => (hCg0 r hr).trans (le_max_left _ _)
  have hint : ∀ a b t : ℝ, s₀ ≤ a → a ≤ b → b ≤ t → t ≤ H →
      IntervalIntegrable (fun r => P t r (g r)) volume a b := by
    intro a b t ha hab hbt htH
    have hg_ab : IntervalIntegrable g volume a b :=
      (hg.mono (Icc_subset_Icc ha (hbt.trans htH))).intervalIntegrable_of_Icc hab
    exact intervalIntegrable_propagator_apply (hs₀.1.trans ha) hab hbt htH hM_P
      hP_id hP_coc hP_cont hP_bd hg_ab
  have hnorm_ab : ∀ a b t : ℝ, s₀ ≤ a → a ≤ b → b ≤ t → t ≤ H →
      ‖∫ r in a..b, P t r (g r)‖ ≤ (M_P * C_g) * (b - a) := by
    intro a b t ha hab hbt htH
    calc ‖∫ r in a..b, P t r (g r)‖
        ≤ (M_P * C_g) * |b - a| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
          rw [uIoc_of_le hab] at hr
          have hr_sH : r ∈ Icc s₀ H := ⟨ha.trans hr.1.le, hr.2.trans (hbt.trans htH)⟩
          calc ‖P t r (g r)‖ ≤ ‖P t r‖ * ‖g r‖ := (P t r).le_opNorm _
            _ ≤ M_P * C_g :=
              mul_le_mul (hP_bd r t (hs₀.1.trans hr_sH.1) (hr.2.trans hbt) htH)
                (hg_bd r hr_sH) (norm_nonneg _) hM_P
      _ = (M_P * C_g) * (b - a) := by rw [abs_of_nonneg (sub_nonneg.2 hab)]
  intro t₀ ht₀
  set w₀ : X := ∫ r in s₀..t₀, P t₀ r (g r)
  rw [ContinuousWithinAt, ← Icc_union_Icc_eq_Icc ht₀.1 ht₀.2, nhdsWithin_union]
  refine Tendsto.sup ?_ ?_
  · -- Left limit: `t ∈ Icc s₀ t₀`, `t → t₀`
    rcases eq_or_lt_of_le ht₀.1 with h_eq | _hlt
    · subst h_eq
      rw [Icc_self]
      exact continuousWithinAt_singleton
    · rw [tendsto_iff_norm_sub_tendsto_zero]
      set μ_I : Measure ℝ := volume.restrict (Ioc s₀ t₀)
      let F : ℝ → ℝ → ℝ≥0∞ :=
        fun t r => (Iic t).indicator (fun r => ‖P t₀ r (g r) - P t r (g r)‖ₑ) r
      have hF_meas : ∀ᶠ t in 𝓝[Icc s₀ t₀] t₀, AEMeasurable (F t) μ_I := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have h1 : IntegrableOn (fun r => P t₀ r (g r)) (Ioc s₀ t) volume :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1
            (hint s₀ t t₀ le_rfl ht.1 ht.2 ht₀.2)
        have h2 : IntegrableOn (fun r => P t r (g r)) (Ioc s₀ t) volume :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1
            (hint s₀ t t le_rfl ht.1 le_rfl (ht.2.trans ht₀.2))
        have hsub_int : IntegrableOn (fun r => P t₀ r (g r) - P t r (g r)) (Ioc s₀ t) volume :=
          h1.sub h2
        have hind_int : Integrable
            ((Ioc s₀ t).indicator (fun r => P t₀ r (g r) - P t r (g r))) volume :=
          (integrable_indicator_iff measurableSet_Ioc).2 hsub_int
        have haesm_I : AEStronglyMeasurable
            ((Iic t).indicator (fun r => P t₀ r (g r) - P t r (g r))) μ_I := by
          refine hind_int.aestronglyMeasurable.restrict.congr ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          by_cases hrt : r ≤ t
          · have hr_st : r ∈ Ioc s₀ t := ⟨hr.1, hrt⟩
            simp [hr_st, hrt]
          · have hr_nst : r ∉ Ioc s₀ t := fun h => hrt h.2
            simp [hr_nst, hrt]
        have hF_eq : F t = fun r =>
            ‖(Iic t).indicator (fun r => P t₀ r (g r) - P t r (g r)) r‖ₑ := by
          funext r
          by_cases hrt : r ≤ t <;> simp [F, hrt]
        rw [hF_eq]
        exact haesm_I.enorm
      have hF_bd_pt : ∀ t ∈ Icc s₀ t₀,
          ∀ᵐ r ∂μ_I, F t r ≤ ENNReal.ofReal (2 * M_P * C_g) := by
        intro t ht
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        by_cases hrt : r ≤ t
        · simp only [F, Set.indicator_of_mem (mem_Iic.2 hrt), ← ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ?_
          have hr_sH : r ∈ Icc s₀ H := ⟨hr.1.le, hr.2.trans ht₀.2⟩
          calc ‖P t₀ r (g r) - P t r (g r)‖
              ≤ ‖P t₀ r (g r)‖ + ‖P t r (g r)‖ := norm_sub_le _ _
            _ ≤ M_P * C_g + M_P * C_g := by
                refine add_le_add ?_ ?_
                · exact ((P t₀ r).le_opNorm _).trans
                    (mul_le_mul (hP_bd r t₀ (hs₀.1.trans hr_sH.1) hr.2 ht₀.2)
                      (hg_bd r hr_sH) (norm_nonneg _) hM_P)
                · exact ((P t r).le_opNorm _).trans
                    (mul_le_mul (hP_bd r t (hs₀.1.trans hr_sH.1) hrt (ht.2.trans ht₀.2))
                      (hg_bd r hr_sH) (norm_nonneg _) hM_P)
            _ = 2 * M_P * C_g := by ring
        · simp [F, mem_Iic, hrt]
      have hF_bd : ∀ᶠ t in 𝓝[Icc s₀ t₀] t₀,
          ∀ᵐ r ∂μ_I, F t r ≤ ENNReal.ofReal (2 * M_P * C_g) := by
        filter_upwards [self_mem_nhdsWithin] with t ht using hF_bd_pt t ht
      have hF_fin : (∫⁻ _, ENNReal.ofReal (2 * M_P * C_g) ∂μ_I) ≠ ⊤ := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioc_lt_top).ne
      have hF_lim : ∀ᵐ r ∂μ_I, Tendsto (fun t => F t r) (𝓝[Icc s₀ t₀] t₀) (𝓝 0) := by
        have hae_ne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ t₀ :=
          compl_mem_ae_iff.2 (measure_singleton t₀)
        filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hae_ne] with r hr hne
        have hrt₀ : r < t₀ := lt_of_le_of_ne hr.2 hne
        have hr_0H : r ∈ Icc 0 H := ⟨hs₀.1.trans hr.1.le, hr.2.trans ht₀.2⟩
        have hcont_r := (hP_cont r hr_0H (g r)) t₀ ⟨hrt₀.le, ht₀.2⟩
        have hle_nhds : 𝓝[Icc s₀ t₀] t₀ ≤ 𝓝[Icc r H] t₀ := by
          rw [nhdsWithin_le_iff, mem_nhdsWithin]
          refine ⟨Ioi r, isOpen_Ioi, hrt₀, ?_⟩
          rintro t ⟨ht_gt, ht_Icc⟩
          exact ⟨ht_gt.le, ht_Icc.2.trans ht₀.2⟩
        have hP_lim : Tendsto (fun t => P t r (g r)) (𝓝[Icc s₀ t₀] t₀) (𝓝 (P t₀ r (g r))) :=
          hcont_r.tendsto.mono_left hle_nhds
        have hsub0 : Tendsto (fun t => ‖P t₀ r (g r) - P t r (g r)‖ₑ)
            (𝓝[Icc s₀ t₀] t₀) (𝓝 0) := by
          have h1 : Tendsto (fun t => P t₀ r (g r) - P t r (g r)) (𝓝[Icc s₀ t₀] t₀) (𝓝 0) := by
            have h := (tendsto_const_nhds (x := P t₀ r (g r))).sub hP_lim
            rwa [sub_self] at h
          have h2 := (continuous_enorm.tendsto (0 : X)).comp h1
          rwa [enorm_zero] at h2
        refine hsub0.congr' ?_
        have hgt_mem : Ioi r ∈ 𝓝[Icc s₀ t₀] t₀ :=
          nhdsWithin_le_nhds (Ioi_mem_nhds hrt₀)
        filter_upwards [hgt_mem] with t ht
        have hrt : r < t := ht
        simp [F, hrt.le]
      have h_lint : Tendsto (fun t => ∫⁻ r, F t r ∂μ_I) (𝓝[Icc s₀ t₀] t₀) (𝓝 0) := by
        have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ_I)
          (f := fun _ => (0 : ℝ≥0∞)) (fun _ => ENNReal.ofReal (2 * M_P * C_g))
          hF_meas hF_bd hF_fin hF_lim
        simpa using h
      have h_toreal : Tendsto (fun t => (∫⁻ r, F t r ∂μ_I).toReal)
          (𝓝[Icc s₀ t₀] t₀) (𝓝 0) := by
        have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h_lint
        rwa [ENNReal.toReal_zero] at h
      have h_tail : Tendsto (fun t => (M_P * C_g) * (t₀ - t))
          (𝓝[Icc s₀ t₀] t₀) (𝓝 0) := by
        have h1 : Tendsto (fun t => t₀ - t) (𝓝[Icc s₀ t₀] t₀) (𝓝 0) := by
          have h := (tendsto_const_nhds (x := t₀)).sub
            (continuousWithinAt_id (s := Icc s₀ t₀) (x := t₀)).tendsto
          simpa using h
        have h2 := h1.const_mul (M_P * C_g)
        rwa [mul_zero] at h2
      have hmaj0 := h_toreal.add h_tail
      rw [add_zero] at hmaj0
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj0
        (Eventually.of_forall fun _ => norm_nonneg _) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have h1 := hint s₀ t t₀ le_rfl ht.1 ht.2 ht₀.2
      have h2 := hint t t₀ t₀ ht.1 ht.2 le_rfl ht₀.2
      have h3 := hint s₀ t t le_rfl ht.1 le_rfl (ht.2.trans ht₀.2)
      have hw0_split : w₀ =
          (∫ r in s₀..t, P t₀ r (g r)) + (∫ r in t..t₀, P t₀ r (g r)) :=
        (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
      have hdiff_eq : (∫ r in s₀..t, P t r (g r)) - w₀ =
          (∫ r in s₀..t, (P t r (g r) - P t₀ r (g r))) -
            (∫ r in t..t₀, P t₀ r (g r)) := by
        dsimp [w₀] at hw0_split ⊢
        rw [hw0_split, intervalIntegral.integral_sub h3 h1]
        abel
      have hfirst_le : ‖∫ r in s₀..t, (P t r (g r) - P t₀ r (g r))‖ ≤
          (∫⁻ r, F t r ∂μ_I).toReal := by
        rw [intervalIntegral.integral_of_le ht.1]
        have henorm := enorm_integral_le_lintegral_enorm
          (μ := volume.restrict (Ioc s₀ t)) (fun r => P t r (g r) - P t₀ r (g r))
        have hlint_eq : (∫⁻ r in Ioc s₀ t, ‖P t r (g r) - P t₀ r (g r)‖ₑ) =
            ∫⁻ r, F t r ∂μ_I := by
          dsimp [μ_I, F]
          rw [lintegral_indicator measurableSet_Iic,
            Measure.restrict_restrict measurableSet_Iic]
          have hset : Iic t ∩ Ioc s₀ t₀ = Ioc s₀ t := by
            ext r
            simp only [mem_inter_iff, mem_Iic, mem_Ioc]
            exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h1, h2, h1.trans ht.2⟩⟩
          rw [hset]
          refine lintegral_congr fun r => ?_
          rw [← ofReal_norm, ← ofReal_norm, norm_sub_rev]
        rw [hlint_eq] at henorm
        have hfin_t : (∫⁻ r, F t r ∂μ_I) ≠ ⊤ :=
          ne_top_of_le_ne_top hF_fin (lintegral_mono_ae (hF_bd_pt t ht))
        have htr := ENNReal.toReal_mono hfin_t henorm
        rwa [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] at htr
      rw [hdiff_eq]
      calc ‖(∫ r in s₀..t, (P t r (g r) - P t₀ r (g r))) - (∫ r in t..t₀, P t₀ r (g r))‖
          ≤ ‖∫ r in s₀..t, (P t r (g r) - P t₀ r (g r))‖ +
              ‖∫ r in t..t₀, P t₀ r (g r)‖ := norm_sub_le _ _
        _ ≤ (∫⁻ r, F t r ∂μ_I).toReal + (M_P * C_g) * (t₀ - t) :=
            add_le_add hfirst_le (hnorm_ab t t₀ t₀ ht.1 ht.2 le_rfl ht₀.2)
  · -- Right limit: `t ∈ Icc t₀ H`, `t → t₀`
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht₀_0H : t₀ ∈ Icc 0 H := ⟨hs₀.1.trans ht₀.1, ht₀.2⟩
    have hcont_w0 : Tendsto (fun t => ‖P t t₀ w₀ - w₀‖) (𝓝[Icc t₀ H] t₀) (𝓝 0) := by
      have h1 := ((hP_cont t₀ ht₀_0H w₀) t₀ ⟨le_rfl, ht₀.2⟩).tendsto
      rw [hP_id t₀ ht₀_0H, ContinuousLinearMap.id_apply] at h1
      exact tendsto_iff_norm_sub_tendsto_zero.mp h1
    have h_tail : Tendsto (fun t => (M_P * C_g) * (t - t₀)) (𝓝[Icc t₀ H] t₀) (𝓝 0) := by
      have h1 : Tendsto (fun t => t - t₀) (𝓝[Icc t₀ H] t₀) (𝓝 0) := by
        have h := (continuousWithinAt_id (s := Icc t₀ H) (x := t₀)).tendsto.sub
          (tendsto_const_nhds (x := t₀))
        simpa using h
      have h2 := h1.const_mul (M_P * C_g)
      rwa [mul_zero] at h2
    have hmaj0 := hcont_w0.add h_tail
    rw [add_zero] at hmaj0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj0
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h1 := hint s₀ t₀ t le_rfl ht₀.1 ht.1 ht.2
    have h2 := hint t₀ t t ht₀.1 ht.1 le_rfl ht.2
    have h0 := hint s₀ t₀ t₀ le_rfl ht₀.1 le_rfl ht₀.2
    have hsplit : (∫ r in s₀..t, P t r (g r)) =
        (∫ r in s₀..t₀, P t r (g r)) + (∫ r in t₀..t, P t r (g r)) :=
      (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    have hcoc_eq : (∫ r in s₀..t₀, P t r (g r)) = P t t₀ w₀ := by
      have hcongr : (∫ r in s₀..t₀, P t r (g r)) =
          ∫ r in s₀..t₀, P t t₀ (P t₀ r (g r)) := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le ht₀.1] at hr
        have hcoc := hP_coc r t₀ t (hs₀.1.trans hr.1) hr.2 ht.1 ht.2
        rw [← ContinuousLinearMap.comp_apply, hcoc]
      rw [hcongr, (P t t₀).intervalIntegral_comp_comm h0]
    have hdiff_eq : (∫ r in s₀..t, P t r (g r)) - w₀ =
        (P t t₀ w₀ - w₀) + (∫ r in t₀..t, P t r (g r)) := by
      rw [hsplit, hcoc_eq]
      abel
    rw [hdiff_eq]
    calc ‖(P t t₀ w₀ - w₀) + (∫ r in t₀..t, P t r (g r))‖
        ≤ ‖P t t₀ w₀ - w₀‖ + ‖∫ r in t₀..t, P t r (g r)‖ := norm_add_le _ _
      _ ≤ ‖P t t₀ w₀ - w₀‖ + (M_P * C_g) * (t - t₀) :=
          add_le_add le_rfl (hnorm_ab t₀ t t ht₀.1 ht.1 le_rfl ht.2)

end UnforcedLeray.Short.IIb.MildDuhamelAux
