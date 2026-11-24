import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2

/-!
# `PartIII-a:T21/2/7/2/1/2`, task `endExtCont`: continuity of the extension to the end age

Proves `EndExtCont` (the calculus leaf of `Sub/PartIII-a_T21_2_7_2_1_2.lean`, SP 3060-3071): a field
`C^∞` on `(t, s) × ℝ²` with bounded jets near the end age `t` extends continuously to `[t, s) × ℝ²`
by `endExt`. Away from `r = t` the extension is `h` itself. At `r = t` the first jet bound makes
`h` Lipschitz on `(t, t + d) × ball 0 R`, so each slice `r ↦ h(r, x)` has a limit as `r → t+`, and
these limits are Lipschitz in `x`; the continuity estimate is then elementary.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A Lipschitz family of functions of `r ∈ (t, t + δ)` with complete target has a limit at `t+`. -/
theorem lipLimit_of {F : Type} [NormedAddCommGroup F] [CompleteSpace F] {t δ K : ℝ} (hK : 0 ≤ K)
    (hδ : 0 < δ) {f : ℝ → F}
    (hf : ∀ r ∈ Ioo t (t + δ), ∀ r' ∈ Ioo t (t + δ), dist (f r) (f r') ≤ K * |r - r'|) :
    ∃ L : F, Tendsto f (𝓝[>] t) (𝓝 L) := by
  have hc : Cauchy ((𝓝[>] t).map f) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
    obtain ⟨η, hη0, hηδ, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ η * (2 * (K + 1)) ≤ ε :=
      ⟨min δ (ε / (2 * (K + 1))), lt_min hδ (div_pos hε (by linarith)), min_le_left _ _,
        (le_div_iff₀ (by linarith)).1 (min_le_right _ _)⟩
    refine ⟨f '' Ioo t (t + η), mem_map.2 (mem_of_superset (Ioo_mem_nhdsGT (by linarith))
      (subset_preimage_image f _)), ?_⟩
    rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    have hr1 : r ∈ Ioo t (t + δ) := ⟨hr.1, by linarith [hr.2]⟩
    have hr1' : r' ∈ Ioo t (t + δ) := ⟨hr'.1, by linarith [hr'.2]⟩
    have hd : |r - r'| < η := abs_sub_lt_iff.2 ⟨by linarith [hr.2, hr'.1], by linarith [hr'.2, hr.1]⟩
    have h1 := hf r hr1 r' hr1'
    have h2 : K * |r - r'| ≤ K * η := mul_le_mul_of_nonneg_left hd.le hK
    nlinarith
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hc
  exact ⟨L, hL⟩

/-- Continuity of the extension at a point `(t, x₀)` of the end age. -/
theorem endExt_contWithin_end {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {t s : ℝ} (hts : t < s) {h : ℝ × (ℝ × ℝ) → F} (hh : ContDiffOn ℝ ∞ h (Ioo t s ×ˢ univ))
    (hb : EndJetBdd t h) (x0 : ℝ × ℝ) :
    ContinuousWithinAt (endExt t h) (Ico t s ×ˢ univ) (t, x0) := by
  have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
  obtain ⟨δ, hδ, C, hC⟩ := hb 1 (‖x0‖ + 1)
  obtain ⟨K, hK, hCK⟩ : ∃ K : ℝ, 0 ≤ K ∧ C ≤ K := ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨d, hd0, hdδ, hds⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ δ ∧ d ≤ s - t :=
    ⟨min δ (s - t), lt_min hδ (by linarith), min_le_left _ _, min_le_right _ _⟩
  -- Lipschitz bound for `h` on the convex set `(t, t + d) × ball 0 R`.
  have hlip : ∀ y ∈ Ioo t (t + d) ×ˢ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1),
      ∀ y' ∈ Ioo t (t + d) ×ˢ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1),
      dist (h y) (h y') ≤ K * dist y y' := by
    intro y hy y' hy'
    have hconv : Convex ℝ (Ioo t (t + d) ×ˢ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1)) :=
      (convex_Ioo _ _).prod (convex_ball _ _)
    have hdiff : ∀ z ∈ Ioo t (t + d) ×ˢ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1), DifferentiableAt ℝ h z := by
      intro z hz
      have hzU : z ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) :=
        ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, mem_univ _⟩
      exact (hh.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hzU)
    have hbd : ∀ z ∈ Ioo t (t + d) ×ˢ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1), ‖fderiv ℝ h z‖ ≤ K := by
      intro z hz
      have hr : z.1 ∈ Ioo t (t + δ) := ⟨hz.1.1, by linarith [hz.1.2]⟩
      have h1 := hC z.1 hr z.2 (mem_ball_zero_iff.1 hz.2).le
      rw [norm_iteratedFDeriv_one, Prod.mk.eta] at h1
      linarith
    have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbd hconv hy hy'
    rw [dist_comm (h y), dist_eq_norm, dist_comm y, dist_eq_norm]
    exact this
  -- Along a horizontal line: the slices are Lipschitz in `r`.
  have hdr : ∀ r ∈ Ioo t (t + d), ∀ r' ∈ Ioo t (t + d), ∀ x ∈ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1),
      dist (h (r, x)) (h (r', x)) ≤ K * |r - r'| := by
    intro r hr r' hr' x hx
    refine (hlip (r, x) ⟨hr, hx⟩ (r', x) ⟨hr', hx⟩).trans (mul_le_mul_of_nonneg_left ?_ hK)
    rw [Prod.dist_eq]
    exact max_le (Real.dist_eq r r').le (by simp)
  -- Across the slices: the slices are Lipschitz in `x`.
  have hdx : ∀ r ∈ Ioo t (t + d), ∀ x ∈ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1),
      ∀ x' ∈ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1), dist (h (r, x)) (h (r, x')) ≤ K * dist x x' := by
    intro r hr x hx x' hx'
    refine (hlip (r, x) ⟨hr, hx⟩ (r, x') ⟨hr, hx'⟩).trans (mul_le_mul_of_nonneg_left ?_ hK)
    rw [Prod.dist_eq]
    exact max_le (by simp) le_rfl
  -- The limits of the slices at the end age.
  have hex : ∀ x ∈ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1), ∃ L : F,
      Tendsto (fun r => h (r, x)) (𝓝[>] t) (𝓝 L) :=
    fun x hx => lipLimit_of hK hd0 (fun r hr r' hr' => hdr r hr r' hr' x hx)
  choose! L hL using hex
  have hE1 : ∀ x ∈ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1), endExt t h (t, x) = L x := by
    intro x hx
    have hT := tendsto_nhds_limUnder (⟨L x, hL x hx⟩ : ∃ a, Tendsto (fun r => h (r, x)) (𝓝[>] t)
      (𝓝 a))
    unfold endExt
    rw [if_pos rfl]
    exact (tendsto_nhds_unique (hL x hx) hT).symm
  have hE2 : ∀ r ∈ Ioo t (t + d), ∀ x ∈ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1),
      dist (h (r, x)) (L x) ≤ K * (r - t) := by
    intro r hr x hx
    refine le_of_tendsto (tendsto_const_nhds.dist (hL x hx)) ?_
    filter_upwards [Ioo_mem_nhdsGT hr.1] with r' hr'
    have h1 := hdr r hr r' ⟨hr'.1, by linarith [hr'.2, hr.2]⟩ x hx
    have h2 : |r - r'| = r - r' := abs_of_nonneg (by linarith [hr'.2])
    rw [h2] at h1
    have h3 : K * (r - r') ≤ K * (r - t) := mul_le_mul_of_nonneg_left (by linarith [hr'.1]) hK
    linarith
  have hE3 : ∀ x ∈ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1), ∀ x' ∈ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1),
      dist (L x) (L x') ≤ K * dist x x' := by
    intro x hx x' hx'
    refine le_of_tendsto ((hL x hx).dist (hL x' hx')) ?_
    filter_upwards [Ioo_mem_nhdsGT (show t < t + d by linarith)] with r hr
    exact hdx r hr x hx x' hx'
  -- The continuity estimate.
  refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
  obtain ⟨η, hη0, hη1, hηd, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η ≤ d ∧ η * (4 * (K + 1)) ≤ ε :=
    ⟨min (min 1 d) (ε / (4 * (K + 1))), lt_min (lt_min one_pos hd0) (div_pos hε (by linarith)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (le_div_iff₀ (by linarith)).1 (min_le_right _ _)⟩
  have hKη : K * η ≤ ε / 4 := by nlinarith
  refine ⟨η, hη0, fun p hp hpd => ?_⟩
  have hp1 : dist p.1 t ≤ dist p (t, x0) := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hp2 : dist p.2 x0 ≤ dist p (t, x0) := by rw [Prod.dist_eq]; exact le_max_right _ _
  rw [Real.dist_eq] at hp1
  have hr0 : t ≤ p.1 := hp.1.1
  have hA : |p.1 - t| < η := lt_of_le_of_lt hp1 hpd
  have hnn : 0 ≤ p.1 - t := by linarith
  have hA2 : p.1 - t < η := by rw [abs_of_nonneg hnn] at hA; exact hA
  have hdist2 : dist p.2 x0 < η := lt_of_le_of_lt hp2 hpd
  have hnorm : ‖p.2‖ < ‖x0‖ + 1 := by
    have h1 : dist p.2 x0 = ‖p.2 - x0‖ := dist_eq_norm _ _
    have h2 := norm_sub_norm_le p.2 x0
    linarith
  have hxb : p.2 ∈ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1) := mem_ball_zero_iff.2 hnorm
  have hx0b : x0 ∈ Metric.ball (0 : ℝ × ℝ) (‖x0‖ + 1) := mem_ball_zero_iff.2 (by linarith)
  rw [hE1 x0 hx0b]
  by_cases hpt : p.1 = t
  · have hp' : p = (t, p.2) := Prod.ext hpt rfl
    rw [hp', hE1 p.2 hxb]
    have e := hE3 p.2 hxb x0 hx0b
    have hKb : K * dist p.2 x0 ≤ K * η := mul_le_mul_of_nonneg_left hdist2.le hK
    linarith
  · have hEp : endExt t h p = h p := by
      unfold endExt
      rw [if_neg hpt]
    rw [hEp]
    have hrt : p.1 ∈ Ioo t (t + d) := ⟨lt_of_le_of_ne hr0 (Ne.symm hpt), by linarith⟩
    have e2 := hE2 p.1 hrt p.2 hxb
    rw [Prod.mk.eta] at e2
    have e3 := hE3 p.2 hxb x0 hx0b
    have htri := dist_triangle (h p) (L p.2) (L x0)
    have hKa : K * (p.1 - t) ≤ K * η := mul_le_mul_of_nonneg_left hA2.le hK
    have hKb : K * dist p.2 x0 ≤ K * η := mul_le_mul_of_nonneg_left hdist2.le hK
    linarith

/-- **Continuity of the extension** (calculus): a field `C^∞` on `(t, s) × ℝ²` with bounded jets
near `t` (complete target) extends continuously to `[t, s) × ℝ²`. -/
theorem endExtCont : UnforcedLeray.Short.IIIa.EndExtCont := by
  intro F _ _ _ t s hts h hh hb p hp
  by_cases hpt : p.1 = t
  · have hp' : p = (t, p.2) := Prod.ext hpt rfl
    rw [hp']
    exact endExt_contWithin_end hts hh hb p.2
  · have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
    have hU' : p ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) :=
      ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm hpt), hp.1.2⟩, mem_univ _⟩
    have hcont : ContinuousAt h p := hh.continuousOn.continuousAt (hU.mem_nhds hU')
    have heq : h =ᶠ[𝓝 p] endExt t h := by
      filter_upwards [hU.mem_nhds hU'] with q hq
      have hqt : q.1 ≠ t := hq.1.1.ne'
      unfold endExt
      rw [if_neg hqt]
    exact (hcont.congr heq).continuousWithinAt

end UnforcedLeray.Short.IIIa
