import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.DuhamelAbstract.Regularity

/-!
# Leaf A helper: joint strong continuity of a Duhamel evolution on one block

Helper for `PartIII-a:T21/c3/2/1/2/1` (`DuhamelVoCAbstract`, SP 2962-2982).

* `U_min_uniform`: `s ↦ U(t, min s t) x` is continuous uniformly in `t ∈ [0, B]`;
* `continuousOn_U_min_left`: `t ↦ U(t, min s t) x` is continuous on `[0, B]`
  (dominated convergence in the Duhamel identity);
* `continuousOn_U_min`: `(t, s) ↦ U(t, min s t) x` is jointly continuous on `[0, B]²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.DuhamelAbstractSub

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {B M K CU : ℝ} {F : ℝ → ℝ → H →L[ℂ] H} {A : ℝ → H →L[ℂ] H} {U : ℝ → ℝ → H →L[ℂ] H}

/-- `s ↦ U(t, min s t) x` is continuous on `[0, B]`, uniformly in `t ∈ [0, B]`. -/
theorem U_min_uniform
    (hU : UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B (fun _ => F) (fun _ => A)
      (fun _ => U))
    (hM : 0 ≤ M) (hF : ∀ t s, 0 ≤ s → s ≤ t → t ≤ B → ‖F t s‖ ≤ M)
    (hK : 0 ≤ K) (hA : ∀ r, 0 ≤ r → r ≤ B → ‖A r‖ ≤ K)
    (hCU : ∀ t s, 0 ≤ s → s ≤ t → t ≤ B → ‖U t s‖ ≤ CU)
    (hFc : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 x) (tri B)) (x : H) :
    ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) B, ∀ s' ∈ Icc (0 : ℝ) B, |s - s'| < δ →
      ∀ t ∈ Icc (0 : ℝ) B, ‖U t (min s t) x - U t (min s' t) x‖ < ε := by
  intro ε hε
  set E := Real.exp ((2 * (M * K) + 1) * B) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set κ := M * K * CU * ‖x‖ with hκ
  have huc := (isCompact_tri B).uniformContinuousOn_of_continuous (hFc x)
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := huc (ε / (8 * E)) (by positivity)
  have key : ∀ s ∈ Icc (0 : ℝ) B, ∀ s' ∈ Icc (0 : ℝ) B, s ≤ s' →
      s' - s < min δ₀ (ε / (8 * E * (|κ| + 1))) →
      ∀ t ∈ Icc (0 : ℝ) B, ‖U t (min s t) x - U t (min s' t) x‖ < ε := by
    intro s hs s' hs' hss' hd t ht
    have hω : ∀ t, 0 ≤ t → t ≤ B → ‖F t (min s t) x - F t (min s' t) x‖ ≤ ε / (8 * E) := by
      intro t h0 h1
      rw [← dist_eq_norm]
      refine hδ₀' (t, min s t) ⟨le_min hs.1 h0, min_le_right _ _, h1⟩ (t, min s' t)
        ⟨le_min hs'.1 h0, min_le_right _ _, h1⟩ ?_
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      refine max_le hδ₀.le ?_
      have hmin : |min s t - min s' t| ≤ s' - s := by
        rw [abs_le]
        constructor
        · rcases le_total s' t with h | h
          · rw [min_eq_left (hss'.trans h), min_eq_left h]; linarith
          · rw [min_eq_right h]
            rcases le_total s t with h' | h'
            · rw [min_eq_left h']; linarith
            · rw [min_eq_right h']; linarith
        · rcases le_total s t with h | h
          · rw [min_eq_left h]
            rcases le_total s' t with h' | h'
            · rw [min_eq_left h']; linarith
            · rw [min_eq_right h']; linarith
          · rw [min_eq_right h, min_eq_right (h.trans hss')]; linarith
      linarith [hd.trans_le (min_le_left _ _)]
    have h := norm_U_min_sub_le hU hM hF hK hA hCU x hs.1 hss' hs'.2 hω t ht.1 ht.2
    rw [← hE, ← hκ] at h
    have hD : (|κ| + 1) * (s' - s) ≤ ε / (8 * E) := by
      have h1 := hd.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ (by positivity)] at h1
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hκD : κ * (s' - s) ≤ ε / (8 * E) :=
      le_trans (mul_le_mul_of_nonneg_right ((le_abs_self κ).trans (by linarith))
        (by linarith)) hD
    have h3 : 2 * (ε / (8 * E) + κ * (s' - s)) * E ≤ 2 * (ε / (8 * E) + ε / (8 * E)) * E := by
      gcongr
    have h4 : 2 * (ε / (8 * E) + ε / (8 * E)) * E = ε / 2 := by
      field_simp
      ring
    linarith
  refine ⟨min δ₀ (ε / (8 * E * (|κ| + 1))), lt_min hδ₀ (by positivity), ?_⟩
  intro s hs s' hs' hd t ht
  rcases le_total s s' with h | h
  · refine key s hs s' hs' h ?_ t ht
    rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hd
    exact hd
  · rw [norm_sub_rev]
    refine key s' hs' s hs h ?_ t ht
    rw [abs_of_nonneg (by linarith)] at hd
    exact hd

/-- `t ↦ U(t, min s t) x` is continuous on `[0, B]` (dominated convergence in the Duhamel
identity). -/
theorem continuousOn_U_min_left
    (hU : UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B (fun _ => F) (fun _ => A)
      (fun _ => U))
    (hM : 0 ≤ M) (hF : ∀ t s, 0 ≤ s → s ≤ t → t ≤ B → ‖F t s‖ ≤ M)
    (hK : 0 ≤ K) (hA : ∀ r, 0 ≤ r → r ≤ B → ‖A r‖ ≤ K)
    (hCU : ∀ t s, 0 ≤ s → s ≤ t → t ≤ B → ‖U t s‖ ≤ CU)
    (hFc : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 x) (tri B)) (x : H) {s : ℝ}
    (hs : 0 ≤ s) (hsB : s ≤ B) :
    ContinuousOn (fun t => U t (min s t) x) (Icc 0 B) := by
  have hB0 : 0 ≤ B := hs.trans hsB
  have hCU0 : 0 ≤ CU := (norm_nonneg _).trans (hCU 0 0 le_rfl le_rfl hB0)
  have hrep : ∀ t ∈ Icc (0 : ℝ) B, U t (min s t) x = F t (min s t) x +
      ∫ r in Ioc s B, (Ioc s t).indicator (fun r => F t r (A r (U r s x))) r := by
    intro t ht
    rcases le_or_gt s t with hst | hts
    · rw [min_eq_left hst, hU.duhamel () s t hst (by linarith [ht.2]) x,
        intervalIntegral.integral_of_le hst, setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_right.2 (Ioc_subset_Ioc_right ht.2)]
    · rw [min_eq_right hts.le]
      have hd := hU.duhamel () t t le_rfl (by linarith [ht.2]) x
      rw [intervalIntegral.integral_same, add_zero] at hd
      rw [hd, Set.Ioc_eq_empty (not_lt.2 hts.le)]
      simp
  have hc1 : ContinuousOn (fun t => F t (min s t) x) (Icc 0 B) :=
    (hFc x).comp (continuous_id.prodMk (continuous_const.min continuous_id)).continuousOn
      (fun t ht => ⟨le_min hs ht.1, min_le_right _ _, ht.2⟩)
  have hfin : volume (Ioc s B) ≠ ⊤ := by simp
  haveI : IsFiniteMeasure (volume.restrict (Ioc s B)) := isFiniteMeasure_restrict.2 hfin
  have hc2 : ContinuousOn (fun t => ∫ r in Ioc s B,
      (Ioc s t).indicator (fun r => F t r (A r (U r s x))) r) (Icc 0 B) := by
    intro t₀ ht₀
    refine continuousWithinAt_of_dominated (bound := fun _ => M * K * CU * ‖x‖) ?_ ?_
      (integrable_const _) ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rcases le_or_gt s t with hst | hts
      · exact ((aestronglyMeasurable_indicator_iff measurableSet_Ioc).2
          (hU.integrable () s t hst (by linarith [ht.2]) x).1.aestronglyMeasurable).restrict
      · rw [Set.Ioc_eq_empty (not_lt.2 hts.le), Set.indicator_empty]
        exact aestronglyMeasurable_const
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine ae_of_all _ fun r => ?_
      by_cases hr : r ∈ Ioc s t
      · rw [Set.indicator_of_mem hr]
        exact norm_FAU_le (hF t r (hs.trans hr.1.le) hr.2 ht.2)
          (hA r (hs.trans hr.1.le) (hr.2.trans ht.2)) (hCU r s hs hr.1.le (hr.2.trans ht.2))
          hM hK x
      · rw [Set.indicator_of_notMem hr, norm_zero]
        positivity
    · have hne : ∀ᵐ r ∂(volume.restrict (Ioc s B)), r ≠ t₀ :=
        ae_restrict_of_ae (by rw [ae_iff]; simp)
      filter_upwards [hne] with r hr
      rcases lt_or_gt_of_ne hr with hlt | hgt
      · by_cases hsr : s < r
        · have hcont : ContinuousWithinAt (fun t => F t r (A r (U r s x))) (Icc 0 B) t₀ := by
            have hpair : ContinuousWithinAt (fun t : ℝ => (t, r)) (Icc r B) t₀ :=
              (continuous_id.prodMk continuous_const).continuousWithinAt
            have h1 : ContinuousWithinAt (fun t => F t r (A r (U r s x))) (Icc r B) t₀ :=
              ContinuousWithinAt.comp (g := fun p : ℝ × ℝ => F p.1 p.2 (A r (U r s x)))
                (f := fun t : ℝ => (t, r)) (x := t₀) (s := Icc r B) (t := tri B)
                (hFc (A r (U r s x)) (t₀, r) ⟨hs.trans hsr.le, hlt.le, ht₀.2⟩) hpair
                (fun t ht => ⟨hs.trans hsr.le, ht.1, ht.2⟩)
            refine h1.mono_of_mem_nhdsWithin ?_
            filter_upwards [self_mem_nhdsWithin,
              mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlt)] with t ht ht'
            exact ⟨le_of_lt ht', ht.2⟩
          refine hcont.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlt)] with t ht
            exact Set.indicator_of_mem (show r ∈ Ioc s t from ⟨hsr, le_of_lt ht⟩) _
          · exact Set.indicator_of_mem (show r ∈ Ioc s t₀ from ⟨hsr, hlt.le⟩) _
        · have h0 : (fun t => (Ioc s t).indicator (fun r => F t r (A r (U r s x))) r) =
              fun _ => 0 := by
            funext t
            exact Set.indicator_of_notMem (fun h => hsr h.1) _
          rw [h0]
          exact continuousWithinAt_const
      · refine (continuousWithinAt_const (b := (0 : H))).congr_of_eventuallyEq ?_ ?_
        · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hgt)] with t ht
          exact Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 ht)) _
        · exact Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 hgt)) _
  exact (hc1.add hc2).congr hrep

/-- `(t, s) ↦ U(t, min s t) x` is jointly continuous on `[0, B]²`. -/
theorem continuousOn_U_min
    (hU : UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B (fun _ => F) (fun _ => A)
      (fun _ => U))
    (hM : 0 ≤ M) (hF : ∀ t s, 0 ≤ s → s ≤ t → t ≤ B → ‖F t s‖ ≤ M)
    (hK : 0 ≤ K) (hA : ∀ r, 0 ≤ r → r ≤ B → ‖A r‖ ≤ K)
    (hCU : ∀ t s, 0 ≤ s → s ≤ t → t ≤ B → ‖U t s‖ ≤ CU)
    (hFc : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 x) (tri B)) (x : H) :
    ContinuousOn (fun p : ℝ × ℝ => U p.1 (min p.2 p.1) x) (Icc 0 B ×ˢ Icc 0 B) := by
  rintro ⟨t₀, s₀⟩ ⟨ht₀, hs₀⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h1⟩ := U_min_uniform hU hM hF hK hA hCU hFc x (ε / 2) (by positivity)
  have h2 := continuousOn_U_min_left hU hM hF hK hA hCU hFc x hs₀.1 hs₀.2 t₀ ht₀
  rw [Metric.continuousWithinAt_iff] at h2
  obtain ⟨δ₂, hδ₂, h2⟩ := h2 (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {p} hp hd => ?_⟩
  rw [Prod.dist_eq, max_lt_iff] at hd
  have hd1 : |p.2 - s₀| < δ₁ := by
    rw [← Real.dist_eq]
    exact hd.2.trans_le (min_le_left _ _)
  have hd2 : dist p.1 t₀ < δ₂ := hd.1.trans_le (min_le_right _ _)
  calc dist (U p.1 (min p.2 p.1) x) (U t₀ (min s₀ t₀) x)
      ≤ dist (U p.1 (min p.2 p.1) x) (U p.1 (min s₀ p.1) x) +
          dist (U p.1 (min s₀ p.1) x) (U t₀ (min s₀ t₀) x) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add ?_ (h2 hp.1 hd2)
        rw [dist_eq_norm]
        exact h1 p.2 hp.2 s₀ hs₀ hd1 p.1 hp.1
    _ = ε := by ring

end UnforcedLeray.Short.IIIa.DuhamelAbstractSub
