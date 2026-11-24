import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenTransportCont.Meas

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.IIb.FrozenTransportContHelp

open PartIIbF23Sub

theorem flow_contOn (Sig : ℝ) (x : B0579.Plane) :
    ContinuousOn (fun q : ℝ × ℝ => frozenRadialFlow q.1 q.2 x) (Icc 0 Sig ×ˢ univ) := by
  have hpos : ∀ q ∈ (Icc 0 Sig ×ˢ (univ : Set ℝ)), 0 < 1 + q.1 := fun q hq => by
    have := hq.1.1; linarith
  have hω : ContinuousOn (fun q : ℝ × ℝ => frozenOmega q.1 x) (Icc 0 Sig ×ˢ univ) := by
    have : (fun q : ℝ × ℝ => frozenOmega q.1 x) = fun q : ℝ × ℝ => ((1 + q.1) ^ 2)⁻¹ *
      Real.exp (-(((x.1 / Real.sqrt (1 + q.1)) ^ 2 + (x.2 / Real.sqrt (1 + q.1)) ^ 2) / 4)) :=
      funext fun q => frozenOmega_eq q.1 x
    rw [this]
    have h1 : ∀ q ∈ (Icc 0 Sig ×ˢ (univ : Set ℝ)), Real.sqrt (1 + q.1) ≠ 0 := fun q hq =>
      (Real.sqrt_pos.2 (hpos q hq)).ne'
    have h2 : ∀ q ∈ (Icc 0 Sig ×ˢ (univ : Set ℝ)), (1 + q.1) ^ 2 ≠ 0 := fun q hq =>
      (pow_pos (hpos q hq) 2).ne'
    refine ContinuousOn.mul (ContinuousOn.inv₀ (by fun_prop) h2) ?_
    refine Real.continuous_exp.comp_continuousOn ?_
    refine ContinuousOn.neg (ContinuousOn.div_const (ContinuousOn.add ?_ ?_) _)
    · exact ContinuousOn.pow (ContinuousOn.div continuousOn_const (by fun_prop) h1) 2
    · exact ContinuousOn.pow (ContinuousOn.div continuousOn_const (by fun_prop) h1) 2
  unfold frozenRadialFlow
  simp only
  have := hω
  fun_prop

/-- Continuity of `(σ, τ) ↦ T σ τ h` for `h` a.e. equal to a continuous compactly supported `g`. -/
theorem smooth_contOn (m Sig : ℝ) (T : ℝ → ℝ → (Xm m →L[ℝ] Xm m)) (hT : IsFrozenRadialTransport m Sig T)
    (g : B0579.Plane → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) (h : Xm m)
    (hh : (h : B0579.Plane → ℝ) =ᵐ[planeMeasure m] g) :
    ContinuousOn (fun q : ℝ × ℝ => T q.1 q.2 h) (Icc 0 Sig ×ˢ univ) := by
  intro q0 hq0
  set S : Set (ℝ × ℝ) := Icc 0 Sig ×ˢ univ with hS
  set μ := planeMeasure m with hμ
  have key : ∀ q ∈ S, (T q.1 q.2 h : B0579.Plane → ℝ) =ᵐ[μ] fun x => g (frozenRadialFlow q.1 q.2 x) := by
    intro q hq
    have hσ : 0 ≤ 1 + q.1 := by have := hq.1.1; linarith
    exact (hT.flow q.1 hq.1 q.2 h).trans ((flow_qmp m q.1 hσ q.2).ae_eq_comp hh)
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hgc.isCompact.isBounded
  set B : Set B0579.Plane := Metric.closedBall 0 (2 * |R| + 1) with hB
  have hBfin : μ B < ⊤ := (isCompact_closedBall _ _).measure_lt_top
  have hsupp : ∀ (q : ℝ × ℝ) (x : B0579.Plane), g (frozenRadialFlow q.1 q.2 x) ≠ 0 → x ∈ B := by
    intro q x hx
    have h1 : frozenRadialFlow q.1 q.2 x ∈ tsupport g := subset_tsupport _ (Function.mem_support.2 hx)
    have h2 := hR _ h1
    have hsq := flow_sq q.1 q.2 x
    have a1 : |(frozenRadialFlow q.1 q.2 x).1| ≤ |R| := by
      have := (norm_fst_le (frozenRadialFlow q.1 q.2 x)).trans h2
      exact (Real.norm_eq_abs _ ▸ this).trans (le_abs_self R)
    have a2 : |(frozenRadialFlow q.1 q.2 x).2| ≤ |R| := by
      have := (norm_snd_le (frozenRadialFlow q.1 q.2 x)).trans h2
      exact (Real.norm_eq_abs _ ▸ this).trans (le_abs_self R)
    have s1 : (frozenRadialFlow q.1 q.2 x).1 ^ 2 ≤ |R| ^ 2 := sq_le_sq' (abs_le.1 a1).1 (abs_le.1 a1).2
    have s2 : (frozenRadialFlow q.1 q.2 x).2 ^ 2 ≤ |R| ^ 2 := sq_le_sq' (abs_le.1 a2).1 (abs_le.1 a2).2
    have hR0 : 0 ≤ |R| := abs_nonneg R
    have b1 : |x.1| ≤ 2 * |R| + 1 := by
      apply abs_le_of_sq_le_sq' _ (by positivity) |>.elim (fun a b => abs_le.2 ⟨a, b⟩)
      nlinarith [sq_nonneg x.2]
    have b2 : |x.2| ≤ 2 * |R| + 1 := by
      apply abs_le_of_sq_le_sq' _ (by positivity) |>.elim (fun a b => abs_le.2 ⟨a, b⟩)
      nlinarith [sq_nonneg x.1]
    rw [hB, mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le b1 b2
  -- the dominated convergence
  set F : ℝ × ℝ → B0579.Plane → ℝ≥0∞ := fun q x =>
    ‖g (frozenRadialFlow q.1 q.2 x) - g (frozenRadialFlow q0.1 q0.2 x)‖ₑ ^ (2 : ℝ) with hF
  have hI : Tendsto (fun q => ∫⁻ x, F q x ∂μ) (𝓝[S] q0) (𝓝 (∫⁻ x, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (fun x => B.indicator (fun _ => (ENNReal.ofReal (2 * M)) ^ (2 : ℝ)) x) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun q => ?_
      have c1 : Continuous fun x => g (frozenRadialFlow q.1 q.2 x) :=
        hg.comp (contDiff_flow q.1 q.2).continuous
      have c2 : Continuous fun x => g (frozenRadialFlow q0.1 q0.2 x) :=
        hg.comp (contDiff_flow q0.1 q0.2).continuous
      exact ((c1.sub c2).measurable.enorm).pow_const _
    · refine Eventually.of_forall fun q => Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx]
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        have := norm_sub_le (g (frozenRadialFlow q.1 q.2 x)) (g (frozenRadialFlow q0.1 q0.2 x))
        have h3 := (hM (frozenRadialFlow q.1 q.2 x))
        have h4 := (hM (frozenRadialFlow q0.1 q0.2 x))
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · rw [indicator_of_notMem hx]
        have e1 : g (frozenRadialFlow q.1 q.2 x) = 0 := by
          by_contra hne; exact hx (hsupp q x hne)
        have e2 : g (frozenRadialFlow q0.1 q0.2 x) = 0 := by
          by_contra hne; exact hx (hsupp q0 x hne)
        simp [hF, e1, e2]
    · rw [lintegral_indicator_const measurableSet_closedBall]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        hBfin.ne
    · refine Eventually.of_forall fun x => ?_
      have hc : ContinuousWithinAt (fun q : ℝ × ℝ => g (frozenRadialFlow q.1 q.2 x)) S q0 :=
        hg.continuousAt.comp_continuousWithinAt (flow_contOn Sig x q0 hq0)
      have hd : Tendsto (fun q : ℝ × ℝ => g (frozenRadialFlow q.1 q.2 x) - g (frozenRadialFlow q0.1 q0.2 x))
          (𝓝[S] q0) (𝓝 0) := by
        have := hc.tendsto.sub_const (g (frozenRadialFlow q0.1 q0.2 x))
        simpa using this
      have h0 := (continuous_enorm.tendsto (0 : ℝ)).comp hd
      rw [enorm_zero] at h0
      have h5 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h0
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h5
      exact h5
  simp only [lintegral_zero] at hI
  have hE : Tendsto (fun q => (∫⁻ x, F q x ∂μ) ^ (1 / (2 : ℝ))) (𝓝[S] q0) (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hI
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    exact this
  have hE2 : Tendsto (fun q => ((∫⁻ x, F q x ∂μ) ^ (1 / (2 : ℝ))).toReal) (𝓝[S] q0) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
    rw [ENNReal.toReal_zero] at this
    exact this
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine hE2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [Lp.dist_def]
  congr 1
  rw [eLpNorm_congr_ae (((key q hq).sub (key q0 hq0)).trans (by rfl)),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp [hF]

end UnforcedLeray.Short.IIb.FrozenTransportContHelp
