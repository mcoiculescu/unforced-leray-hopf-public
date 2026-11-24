import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_2.Dil

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.PlanarModesHelp

open UnforcedLeray.Short.IIb

lemma norm_sc (a : ℝ) (x : B0579.Plane) : ‖sc a x‖ = ‖x‖ / Real.sqrt a := by
  unfold sc
  rw [norm_smul, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  ring

lemma dl_bound (A R C : ℝ) (ψ : B0579.Plane → ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C)
    (hR : ∀ x, ψ x ≠ 0 → ‖x‖ ≤ R) (hR0 : 0 ≤ R) (a : ℝ) (ha : 1 ≤ a) (haA : a ≤ A) (x : B0579.Plane) :
    ‖dl a ψ x‖ ≤ (Metric.closedBall (0 : B0579.Plane) (R * Real.sqrt A)).indicator (fun _ => C) x := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 (by linarith)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  by_cases hx : x ∈ Metric.closedBall (0 : B0579.Plane) (R * Real.sqrt A)
  · rw [Set.indicator_of_mem hx]
    unfold dl
    rw [norm_mul, Real.norm_of_nonneg (by positivity)]
    have : a ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by norm_num)
    calc a ^ (-2 : ℝ) * ‖ψ (sc a x)‖ ≤ 1 * C :=
          mul_le_mul this (hC _) (norm_nonneg _) zero_le_one
      _ = C := one_mul _
  · rw [Set.indicator_of_notMem hx]
    have : ψ (sc a x) = 0 := by
      by_contra hne
      have h1 := hR _ hne
      rw [norm_sc, div_le_iff₀ hs] at h1
      apply hx
      rw [Metric.mem_closedBall, dist_zero_right]
      have : Real.sqrt a ≤ Real.sqrt A := Real.sqrt_le_sqrt haA
      nlinarith
    unfold dl; rw [this]; simp

lemma continuous_dl_apply (ψ : B0579.Plane → ℝ) (hψ : Continuous ψ) (x : B0579.Plane) (a0 : ℝ) (ha0 : 0 < a0) :
    ContinuousAt (fun a => dl a ψ x) a0 := by
  unfold dl sc
  have h1 : ContinuousAt (fun a : ℝ => a ^ (-2 : ℝ)) a0 :=
    Real.continuousAt_rpow_const _ _ (Or.inl ha0.ne')
  have h2 : ContinuousAt (fun a : ℝ => ψ ((Real.sqrt a)⁻¹ • x)) a0 := by
    have h3 : ContinuousAt (fun a : ℝ => (Real.sqrt a)⁻¹ • x) a0 :=
      ContinuousAt.smul (ContinuousAt.inv₀ (Real.continuous_sqrt.continuousAt)
        (Real.sqrt_pos.2 ha0).ne') continuousAt_const
    exact hψ.continuousAt.comp h3
  exact h1.mul h2

lemma continuous_dl_x (ψ : B0579.Plane → ℝ) (hψ : Continuous ψ) (a : ℝ) : Continuous (dl a ψ) := by
  unfold dl sc
  exact continuous_const.mul (hψ.comp (continuous_const_smul _))

lemma tendsto_dl_cont (m A : ℝ) (hm : 0 ≤ m) {ψ : B0579.Plane → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (a0 : ℝ) (ha0 : a0 ∈ Icc 1 A) :
    Tendsto (fun a => ∫⁻ x, ‖dl a ψ x - dl a0 ψ x‖ₑ ^ (2 : ℝ) ∂planeMeasure m)
      (𝓝[Icc 1 A] a0) (𝓝 0) := by
  have := isLocFin m hm
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hc
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : B0579.Plane)
  have hR' : ∀ x, ψ x ≠ 0 → ‖x‖ ≤ max R 0 := by
    intro x hx
    have : x ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.2 hx)
    have := hR this
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set E : Set B0579.Plane := Metric.closedBall 0 (max R 0 * Real.sqrt A) with hE
  have hEfin : planeMeasure m E < ∞ := measure_closedBall_lt_top
  have hlim := tendsto_lintegral_filter_of_dominated_convergence
    (μ := planeMeasure m) (l := 𝓝[Icc 1 A] a0)
    (F := fun a x => ‖dl a ψ x - dl a0 ψ x‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
    (E.indicator (fun _ => ENNReal.ofReal (2 * C) ^ (2 : ℝ)))
    (Eventually.of_forall (fun a => by
      have := ((continuous_dl_x ψ hψ a).sub (continuous_dl_x ψ hψ a0)).measurable
      exact (this.enorm.pow_const _ ) ))
    ?_ ?_ ?_
  · simpa using hlim
  · filter_upwards [self_mem_nhdsWithin] with a ha
    refine Eventually.of_forall (fun x => ?_)
    have h1 := dl_bound A (max R 0) C ψ hC hR' (le_max_right _ _) a ha.1 ha.2 x
    have h2 := dl_bound A (max R 0) C ψ hC hR' (le_max_right _ _) a0 ha0.1 ha0.2 x
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      rw [Set.indicator_of_mem hx] at h1 h2
      have : ‖dl a ψ x - dl a0 ψ x‖ ≤ 2 * C := by
        calc _ ≤ ‖dl a ψ x‖ + ‖dl a0 ψ x‖ := norm_sub_le _ _
          _ ≤ C + C := add_le_add h1 h2
          _ = 2 * C := by ring
      exact ENNReal.rpow_le_rpow (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal this)
        (by norm_num)
    · rw [Set.indicator_of_notMem hx]
      rw [Set.indicator_of_notMem hx] at h1 h2
      have h1' : dl a ψ x = 0 := norm_le_zero_iff.1 h1
      have h2' : dl a0 ψ x = 0 := norm_le_zero_iff.1 h2
      rw [h1', h2']; simp
  · rw [lintegral_indicator_const measurableSet_closedBall]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hEfin.ne
  · refine Eventually.of_forall (fun x => ?_)
    have h1 : Tendsto (fun a => dl a ψ x - dl a0 ψ x) (𝓝[Icc 1 A] a0) (𝓝 0) := by
      have := (continuous_dl_apply ψ hψ x a0 (by linarith [ha0.1])).tendsto.sub_const (dl a0 ψ x)
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).comp (continuous_enorm (E := ℝ))).tendsto 0
    simp only [Function.comp, enorm_zero] at h2
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    exact h2.comp h1

/-- The class in `Xm m` of the dilated function, for `a ∈ [1, A]` (zero elsewhere). -/
def lpDl (m A : ℝ) (hm : 0 ≤ m) {g : B0579.Plane → ℝ} (hg : MemLp g 2 (planeMeasure m))
    (a : ℝ) : Xm m :=
  if h : 1 ≤ a ∧ a ≤ A then (memLp_dl m a A hm h.1 h.2 hg).toLp (dl a g) else 0

lemma coeFn_lpDl (m A : ℝ) (hm : 0 ≤ m) {g : B0579.Plane → ℝ} (hg : MemLp g 2 (planeMeasure m))
    (a : ℝ) (ha : a ∈ Icc 1 A) :
    (lpDl m A hm hg a : B0579.Plane → ℝ) =ᵐ[planeMeasure m] dl a g := by
  unfold lpDl
  rw [dif_pos (show 1 ≤ a ∧ a ≤ A from ha)]
  exact MemLp.coeFn_toLp _

lemma norm_lpDl_sub (m A : ℝ) (hm : 0 ≤ m) {g₁ g₂ : B0579.Plane → ℝ}
    (hg₁ : MemLp g₁ 2 (planeMeasure m)) (hg₂ : MemLp g₂ 2 (planeMeasure m))
    (a b : ℝ) (ha : a ∈ Icc 1 A) (hb : b ∈ Icc 1 A) :
    ‖lpDl m A hm hg₁ a - lpDl m A hm hg₂ b‖ =
      (eLpNorm (dl a g₁ - dl b g₂) 2 (planeMeasure m)).toReal := by
  unfold lpDl
  rw [dif_pos (show 1 ≤ a ∧ a ≤ A from ha), dif_pos (show 1 ≤ b ∧ b ≤ A from hb), ← MemLp.toLp_sub, Lp.norm_toLp]

lemma continuousOn_lpDl_cc (m A : ℝ) (hm : 0 ≤ m) {ψ : B0579.Plane → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hψm : MemLp ψ 2 (planeMeasure m)) :
    ContinuousOn (lpDl m A hm hψm) (Icc 1 A) := by
  intro a0 ha0
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  have h1 := tendsto_dl_cont m A hm hψ hc a0 ha0
  have h0 : Tendsto (fun t : ℝ≥0∞ => t ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  have h2 : Tendsto (fun t : ℝ≥0∞ => (t ^ (1 / 2 : ℝ)).toReal) (𝓝 0) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    rw [ENNReal.toReal_zero] at this
    exact this
  refine (h2.comp h1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [dist_eq_norm, norm_lpDl_sub m A hm hψm hψm a a0 ha ha0, eLpNorm_two_eq]
  rfl


theorem continuousOn_lpDl (m A : ℝ) (hm : 0 ≤ m) (hA : 1 ≤ A) {g : B0579.Plane → ℝ}
    (hg : MemLp g 2 (planeMeasure m)) : ContinuousOn (lpDl m A hm hg) (Icc 1 A) := by
  have := isLocFin m hm
  have hex : ∀ n : ℕ, ∃ ψ : B0579.Plane → ℝ, HasCompactSupport ψ ∧
      eLpNorm (g - ψ) 2 (planeMeasure m) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧
      Continuous ψ ∧ MemLp ψ 2 (planeMeasure m) := fun n =>
    hg.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num)
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
  choose ψ hψc hψe hψcont hψm using hex
  have hA0 : 0 < A := by linarith
  set K0 : ℝ := (A ^ (m + 1)) ^ (1 / 2 : ℝ) with hK0
  have hK0nn : 0 ≤ K0 := by positivity
  have hunif : TendstoUniformlyOn (fun n => lpDl m A hm (hψm n)) (lpDl m A hm hg) atTop (Icc 1 A) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht : Tendsto (fun n : ℕ => K0 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul K0
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn a ha
    rw [dist_eq_norm, norm_lpDl_sub m A hm hg (hψm n) a a ha ha, ← dl_sub]
    have hb := eLpNorm_dl_le m a A hm ha.1 ha.2 (g - ψ n)
    have hK : ENNReal.ofReal (A ^ (m + 1)) ^ (1 / 2 : ℝ) = ENNReal.ofReal K0 := by
      rw [hK0, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    have hfin : eLpNorm (g - ψ n) 2 (planeMeasure m) ≠ ∞ := (hψe n).trans_lt ENNReal.ofReal_lt_top |>.ne
    have h3 : eLpNorm (dl a (g - ψ n)) 2 (planeMeasure m) ≤
        ENNReal.ofReal K0 * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      rw [hK] at hb
      exact hb.trans (mul_le_mul' le_rfl (hψe n))
    have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h3
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0nn,
      ENNReal.toReal_ofReal (by positivity)] at h4
    exact lt_of_le_of_lt h4 hn
  exact hunif.continuousOn (Eventually.of_forall
    (fun n => continuousOn_lpDl_cc m A hm (hψcont n) (hψc n) (hψm n))).frequently


lemma norm_lpDl_le (m A : ℝ) (hm : 0 ≤ m) (hA : 1 ≤ A) {g : B0579.Plane → ℝ}
    (hg : MemLp g 2 (planeMeasure m)) (a : ℝ) (ha : a ∈ Icc 1 A) :
    ‖lpDl m A hm hg a‖ ≤ (A ^ (m + 1)) ^ (1 / 2 : ℝ) * (eLpNorm g 2 (planeMeasure m)).toReal := by
  have hA0 : 0 < A := by linarith
  unfold lpDl
  rw [dif_pos (show 1 ≤ a ∧ a ≤ A from ha), Lp.norm_toLp]
  have hb := eLpNorm_dl_le m a A hm ha.1 ha.2 g
  have hK : ENNReal.ofReal (A ^ (m + 1)) ^ (1 / 2 : ℝ) = ENNReal.ofReal ((A ^ (m + 1)) ^ (1 / 2 : ℝ)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  rw [hK] at hb
  have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.2.ne) hb
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h4

end UnforcedLeray.Short.IIb.PlanarModesHelp
