import UnforcedLeray.Units.B0418.Continuity
import UnforcedLeray.Analysis.Heat.AveragingEvolution
import UnforcedLeray.Analysis.Heat.ConvolutionWeakDerivative

/-!
# B0418 helper: the heat generator on smooth compactly supported fields in `L^p`

Blueprint unit B0418 (`paper/main.tex` lines 7419--7420: "Differentiation verifies the
generator, initially for smooth functions"). For `h ∈ C_c^∞(ℝ³; ℝ³)` this file proves

* `∂_t (e^{tΔ}h)(x) = (e^{tΔ}Δh)(x)` for `t > 0` (time derivative of the Gaussian, then two
  integrations by parts, both from the library);
* the pointwise approximate identity `e^{sΔ}g(x) → g(x)` (`s → 0`) for continuous
  compactly supported `g`;
* the fundamental theorem of calculus `e^{τΔ}h - h = ∫_0^τ e^{sΔ}Δh ds` pointwise;
* `τ⁻¹(e^{τΔ}h - h) → Δh` in `L^p`, `1 ≤ p < ∞` (Minkowski in `s` and strong continuity).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.B0418

variable {p : ℝ≥0∞}

/-- The coordinate vector Laplacian `Δh = ∑ᵢ ∂ᵢ∂ᵢh` of a vector field. -/
def vecLaplacian (h : SpatialField) (x : Space) : Space :=
  ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ h y (coordinateVector i)) x (coordinateVector i)

theorem contDiff_dirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ ∞ f) (a : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ f y a) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem contDiff_one_of_infty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 f :=
  hf.of_le (by exact_mod_cast le_top)

theorem vecLaplacian_eq_zero {h : SpatialField} {x : Space} (hx : x ∉ tsupport h) :
    vecLaplacian h x = 0 := by
  unfold vecLaplacian
  apply Finset.sum_eq_zero
  intro i _
  have h1 : x ∉ tsupport (fun y => fderiv ℝ h y (coordinateVector i)) :=
    fun hm => hx (tsupport_fderiv_apply_subset ℝ _ hm)
  rw [fderiv_of_notMem_tsupport ℝ h1, ContinuousLinearMap.zero_apply]

theorem hasCompactSupport_vecLaplacian {h : SpatialField} (hc : HasCompactSupport h) :
    HasCompactSupport (vecLaplacian h) :=
  hc.mono' (fun x hx => by
    by_contra hn
    exact hx (vecLaplacian_eq_zero hn))

theorem continuous_vecLaplacian {h : SpatialField} (hs : ContDiff ℝ ∞ h) :
    Continuous (vecLaplacian h) := by
  unfold vecLaplacian
  exact continuous_finsetSum _ (fun i _ =>
    (contDiff_dirDeriv (contDiff_dirDeriv hs _) _).continuous)

/-- `∂_t (e^{tΔ}h)(x) = (e^{tΔ}Δh)(x)` for `t > 0` and `h ∈ C_c^∞`. -/
theorem average_hasDerivAt_vecLaplacian {t : ℝ} (ht : 0 < t) {h : SpatialField}
    (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (x : Space) :
    HasDerivAt (fun s => Heat.average s h x) (Heat.average t (vecLaplacian h) x) t := by
  have hL2 : MemLp h 2 volume := hs.continuous.memLp_of_hasCompactSupport hc
  have hd := Heat.average_hasDerivAt_laplacianKernel ht hL2 x
  suffices he : (∫ y, Heat.laplacian (Heat.kernel t) y • h (x - y)) =
      Heat.average t (vecLaplacian h) x by
    rw [he] at hd
    exact hd
  set k := Heat.kernel t with hkdef
  have hk : ContDiff ℝ ∞ k := Heat.Gaussian.kernel_smooth (4 * t)
  have hq : HasCompactSupport (fun y => h (x - y)) := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hsub : Continuous (fun y : Space => x - y) := continuous_const.sub continuous_id
  have hcoord : ∀ i : Fin 3,
      Heat.convolution (fun y => fderiv ℝ (fun z => fderiv ℝ k z (coordinateVector i)) y
          (coordinateVector i)) h x =
        Heat.convolution k (fun y => fderiv ℝ (fun z => fderiv ℝ h z (coordinateVector i)) y
          (coordinateVector i)) x := by
    intro i
    have hDh : ContDiff ℝ ∞ (fun z => fderiv ℝ h z (coordinateVector i)) :=
      contDiff_dirDeriv hs _
    have hDk : ContDiff ℝ ∞ (fun z => fderiv ℝ k z (coordinateVector i)) :=
      contDiff_dirDeriv hk _
    have h1 := Heat.convolution_derivative_compact (fun z => fderiv ℝ k z (coordinateVector i))
      (contDiff_one_of_infty hDk) h hc (contDiff_one_of_infty hs) (coordinateVector i) x
    have h2 := Heat.convolution_derivative_compact k (contDiff_one_of_infty hk)
      (fun z => fderiv ℝ h z (coordinateVector i)) (hc.fderiv_apply ℝ (coordinateVector i))
      (contDiff_one_of_infty hDh) (coordinateVector i) x
    exact h1.symm.trans h2.symm
  have hint1 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun y =>
      fderiv ℝ (fun z => fderiv ℝ k z (coordinateVector i)) y (coordinateVector i) •
        h (x - y)) := by
    intro i _
    exact ((contDiff_dirDeriv (contDiff_dirDeriv hk _) _).continuous.smul
      (hs.continuous.comp hsub)).integrable_of_hasCompactSupport hq.smul_left
  have hint2 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun y =>
      k y • fderiv ℝ (fun z => fderiv ℝ h z (coordinateVector i)) (x - y)
        (coordinateVector i)) := by
    intro i _
    have hcs : HasCompactSupport (fun y => fderiv ℝ (fun z => fderiv ℝ h z (coordinateVector i))
        (x - y) (coordinateVector i)) :=
      ((hc.fderiv_apply ℝ (coordinateVector i)).fderiv_apply ℝ
        (coordinateVector i)).comp_homeomorph (Homeomorph.subLeft x)
    exact (hk.continuous.smul ((contDiff_dirDeriv (contDiff_dirDeriv hs _) _).continuous.comp
      hsub)).integrable_of_hasCompactSupport hcs.smul_left
  calc (∫ y, Heat.laplacian k y • h (x - y))
      = ∫ y, ∑ i : Fin 3, fderiv ℝ (fun z => fderiv ℝ k z (coordinateVector i)) y
          (coordinateVector i) • h (x - y) := by
        congr 1
        funext y
        rw [Heat.laplacian, Finset.sum_smul]
    _ = ∑ i : Fin 3, ∫ y, fderiv ℝ (fun z => fderiv ℝ k z (coordinateVector i)) y
          (coordinateVector i) • h (x - y) := integral_finsetSum _ hint1
    _ = ∑ i : Fin 3, ∫ y, k y • fderiv ℝ (fun z => fderiv ℝ h z (coordinateVector i)) (x - y)
          (coordinateVector i) := Finset.sum_congr rfl (fun i _ => hcoord i)
    _ = ∫ y, ∑ i : Fin 3, k y • fderiv ℝ (fun z => fderiv ℝ h z (coordinateVector i)) (x - y)
          (coordinateVector i) := (integral_finsetSum _ hint2).symm
    _ = Heat.average t (vecLaplacian h) x := by
        unfold Heat.average vecLaplacian
        congr 1
        funext y
        rw [Finset.smul_sum]

theorem tendsto_sqrt_four_mul : Tendsto (fun t : ℝ => Real.sqrt (4 * t)) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun t : ℝ => Real.sqrt (4 * t)) :=
    Real.continuous_sqrt.comp (continuous_const.mul continuous_id)
  have := hc.tendsto (0 : ℝ)
  simpa using this

/-- Pointwise approximate identity: `e^{sΔ}g(x) → g(x)` as `s → 0`, for continuous
compactly supported `g`. -/
theorem tendsto_flow_apply {g : SpatialField} (hg : Continuous g) (hgc : HasCompactSupport g)
    (x : Space) : Tendsto (fun s => Heat.flow g s x) (𝓝 0) (𝓝 (g x)) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hL : MemLp g 2 volume := hg.memLp_of_hasCompactSupport hgc
  let Ψ : ℝ → ℝ≥0∞ := fun c =>
    ∫⁻ w, ENNReal.ofReal (Heat.Gaussian.kernel 1 w) * ‖g (x - c • w) - g x‖ₑ
  have hΨ : Tendsto Ψ (𝓝 0) (𝓝 0) := by
    have hlim := tendsto_lintegral_filter_of_dominated_convergence
      (μ := (volume : Measure Space)) (l := 𝓝 (0 : ℝ))
      (F := fun c w => ENNReal.ofReal (Heat.Gaussian.kernel 1 w) * ‖g (x - c • w) - g x‖ₑ)
      (f := fun _ => 0)
      (fun w => ENNReal.ofReal (Heat.Gaussian.kernel 1 w) * ENNReal.ofReal (2 * M))
      ?_ ?_ ?_ ?_
    · simpa [Ψ] using hlim
    · refine Eventually.of_forall (fun c => ?_)
      exact (ENNReal.measurable_ofReal.comp
        (Heat.Gaussian.kernel_smooth 1).continuous.measurable).mul
        ((hg.comp (continuous_const.sub (continuous_id.const_smul c))).sub
          continuous_const).enorm.measurable
    · refine Eventually.of_forall (fun c => Eventually.of_forall (fun w => ?_))
      gcongr
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      calc ‖g (x - c • w) - g x‖ ≤ ‖g (x - c • w)‖ + ‖g x‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hM _) (hM _)
        _ = 2 * M := by ring
    · rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_unitGaussian, one_mul]
      exact ENNReal.ofReal_ne_top
    · refine Eventually.of_forall (fun w => ?_)
      have h1 : Tendsto (fun c : ℝ => g (x - c • w) - g x) (𝓝 0) (𝓝 0) := by
        have hc : Continuous (fun c : ℝ => g (x - c • w) - g x) :=
          (hg.comp (continuous_const.sub (continuous_id.smul continuous_const))).sub
            continuous_const
        have := hc.tendsto 0
        simpa using this
      have h2 := (continuous_enorm.tendsto (0 : Space)).comp h1
      rw [enorm_zero] at h2
      have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)
        (a := ENNReal.ofReal (Heat.Gaussian.kernel 1 w))
      rw [mul_zero] at h3
      exact h3
  have hb : ∀ s, ‖Heat.flow g s x - g x‖ₑ ≤ Ψ (Real.sqrt (4 * s)) := by
    intro s
    by_cases hs : 0 < s
    · rw [Heat.flow_pos g hs]
      have hrep : Heat.average s g x - g x = ∫ z, Heat.kernel s z • (g (x - z) - g x) := by
        simp only [smul_sub]
        rw [integral_sub (heat_integrand_integrable hs (p := 2) (by norm_num) (by norm_num) hL x)
          ((Heat.kernel_integrable hs).smul_const (g x)), integral_smul_const,
          Heat.integral_kernel hs, one_smul]
        rfl
      rw [hrep]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      calc (∫⁻ z, ‖Heat.kernel s z • (g (x - z) - g x)‖ₑ)
          = ∫⁻ z, ENNReal.ofReal (Heat.kernel s z) * (fun z => ‖g (x - z) - g x‖ₑ) z := by
            apply lintegral_congr
            intro z
            rw [enorm_smul, Real.enorm_eq_ofReal (Heat.kernel_nonneg hs z)]
        _ = Ψ (Real.sqrt (4 * s)) := lintegral_kernel_mul_eq hs _
    · rw [Heat.flow_nonpos g (not_lt.mp hs), sub_self, enorm_zero]
      exact zero_le
  have hT : Tendsto (fun s => ‖Heat.flow g s x - g x‖ₑ) (𝓝 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hΨ.comp tendsto_sqrt_four_mul)
      (fun _ => zero_le) hb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT
  rw [ENNReal.toReal_zero] at this
  exact this.congr (fun s => by simp only [Function.comp_apply, toReal_enorm])

/-- Fundamental theorem of calculus for the heat flow of a `C_c^∞` field. -/
theorem flow_sub_eq_integral {τ : ℝ} (hτ : 0 < τ) {h : SpatialField} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (x : Space) :
    Heat.flow h τ x - h x = ∫ s in (0 : ℝ)..τ, Heat.flow (vecLaplacian h) s x := by
  have hLc := continuous_vecLaplacian hs
  have hLs := hasCompactSupport_vecLaplacian hc
  have hderiv' : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun s => Heat.flow h s x) (Heat.flow (vecLaplacian h) s x) s := by
    intro s hpos
    rw [Heat.flow_pos _ hpos]
    apply (average_hasDerivAt_vecLaplacian hpos hs hc x).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hpos] with s' hs''
    rw [Heat.flow_pos _ hs'']
  have hcont0 : ∀ g : SpatialField, Continuous g → HasCompactSupport g →
      ContinuousAt (fun s => Heat.flow g s x) 0 := by
    intro g hg hgc
    have := tendsto_flow_apply hg hgc x
    rw [ContinuousAt, Heat.flow_zero]
    exact this
  have hcont : ContinuousOn (fun s => Heat.flow h s x) (Icc 0 τ) := by
    intro s hs'
    rcases hs'.1.eq_or_lt with h0 | hpos
    · rw [← h0]
      exact (hcont0 h hs.continuous hc).continuousWithinAt
    · exact (hderiv' s hpos).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun s => Heat.flow (vecLaplacian h) s x) volume 0 τ := by
    apply ContinuousOn.intervalIntegrable
    intro s hs'
    rw [uIcc_of_le hτ.le] at hs'
    rcases hs'.1.eq_or_lt with h0 | hpos
    · rw [← h0]
      exact (hcont0 _ hLc hLs).continuousWithinAt
    · have hL2 : MemLp (vecLaplacian h) 2 volume := hLc.memLp_of_hasCompactSupport hLs
      have hca : ContinuousAt (fun s => Heat.average s (vecLaplacian h) x) s :=
        (Heat.average_time_continuousOn hL2 x).continuousAt (Ioi_mem_nhds hpos)
      have : ContinuousAt (fun s => Heat.flow (vecLaplacian h) s x) s := by
        apply hca.congr
        filter_upwards [lt_mem_nhds hpos] with s' hs''
        rw [Heat.flow_pos _ hs'']
      exact this.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.le hcont
    (fun s hs' => hderiv' s hs'.1) hint, Heat.flow_zero]

/-- Joint measurability of `(x, s) ↦ e^{sΔ}g(x)` for continuous `g`. -/
theorem measurable_flow_uncurry {g : SpatialField} (hg : Continuous g) :
    Measurable (fun q : Space × ℝ => Heat.flow g q.2 q.1) := by
  have he : (fun q : Space × ℝ => Heat.flow g q.2 q.1) =
      fun q => if 0 < q.2 then Heat.average q.2 g q.1 else g q.1 := by
    funext q
    by_cases hq : 0 < q.2
    · rw [Heat.flow_pos _ hq, ite_eq_left hq]
    · rw [Heat.flow_nonpos _ (not_lt.mp hq), ite_eq_right hq]
  rw [he]
  have hk : Measurable (fun r : (Space × ℝ) × Space => Heat.kernel r.1.2 r.2) := by
    unfold Heat.kernel Heat.Gaussian.kernel Heat.Gaussian.normalization
    fun_prop
  have hint : StronglyMeasurable
      (fun r : (Space × ℝ) × Space => Heat.kernel r.1.2 r.2 • g (r.1.1 - r.2)) :=
    (hk.smul (hg.measurable.comp (measurable_fst.fst.sub measurable_snd))).stronglyMeasurable
  have hA : Measurable (fun q : Space × ℝ => Heat.average q.2 g q.1) :=
    (StronglyMeasurable.integral_prod_right' (ν := (volume : Measure Space)) hint).measurable
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) hA
    (hg.measurable.comp measurable_fst)

/-- The heat generator on `C_c^∞` fields in `L^p`: `τ⁻¹(e^{τΔ}h - h) → Δh`. -/
theorem tendsto_heat_generator (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞)) {h : SpatialField}
    (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    Tendsto (fun τ => eLpNorm (fun x => τ⁻¹ • (Heat.flow h τ x - h x) - vecLaplacian h x)
      p volume) (𝓝[>] 0) (𝓝 0) := by
  set g := vecLaplacian h with hgdef
  have hgc : Continuous g := continuous_vecLaplacian hs
  have hgs : HasCompactSupport g := hasCompactSupport_vecLaplacian hc
  have hgL : MemLp g p volume := hgc.memLp_of_hasCompactSupport hgs
  have hcont := tendsto_flow_sub hp1 hp hgL
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.mp hcont) ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  filter_upwards [Ioo_mem_nhdsGT hδ] with τ hτ
  have hτ0 : 0 < τ := hτ.1
  have hGm : Measurable (fun q : Space × ℝ => Heat.flow g q.2 q.1 - g q.1) :=
    (measurable_flow_uncurry hgc).sub (hgc.measurable.comp measurable_fst)
  have hrep : (fun x => τ⁻¹ • (Heat.flow h τ x - h x) - g x) =
      τ⁻¹ • fun x => ∫ s in Ioc (0 : ℝ) τ, (Heat.flow g s x - g x) := by
    funext x
    rw [Pi.smul_apply, ← intervalIntegral.integral_of_le hτ0.le, flow_sub_eq_integral hτ0 hs hc x]
    have hint : IntervalIntegrable (fun s => Heat.flow g s x) volume 0 τ := by
      apply ContinuousOn.intervalIntegrable
      intro s hs'
      rw [uIcc_of_le hτ0.le] at hs'
      rcases hs'.1.eq_or_lt with h0' | hpos
      · rw [← h0']
        have := tendsto_flow_apply hgc hgs x
        have h' : ContinuousAt (fun s => Heat.flow g s x) 0 := by
          rw [ContinuousAt, Heat.flow_zero]
          exact this
        exact h'.continuousWithinAt
      · have hL2 : MemLp g 2 volume := hgc.memLp_of_hasCompactSupport hgs
        have hca : ContinuousAt (fun s => Heat.average s g x) s :=
          (Heat.average_time_continuousOn hL2 x).continuousAt (Ioi_mem_nhds hpos)
        have : ContinuousAt (fun s => Heat.flow g s x) s := by
          apply hca.congr
          filter_upwards [lt_mem_nhds hpos] with s' hs''
          rw [Heat.flow_pos _ hs'']
        exact this.continuousWithinAt
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, smul_sub, smul_smul,
      inv_mul_cancel₀ hτ0.ne', one_smul]
  rw [hrep, eLpNorm_const_smul]
  have hjoint : AEStronglyMeasurable
      (Function.uncurry fun x s => Heat.flow g s x - g x)
      ((volume : Measure Space).prod (volume.restrict (Ioc (0 : ℝ) τ))) :=
    hGm.aestronglyMeasurable
  have hM := NonUniqueEuler.Conv.eLpNorm_integral_le
    (F := fun x s => Heat.flow g s x - g x) hjoint hp1 hp
  have hbound : (∫⁻ s in Ioc (0 : ℝ) τ, eLpNorm (fun x => Heat.flow g s x - g x) p volume) ≤
      ε * ENNReal.ofReal τ := by
    calc (∫⁻ s in Ioc (0 : ℝ) τ, eLpNorm (fun x => Heat.flow g s x - g x) p volume)
        ≤ ∫⁻ _s in Ioc (0 : ℝ) τ, ε := by
          apply setLIntegral_mono measurable_const
          intro s hs'
          have hs'' : dist s 0 < δ := by
            rw [Real.dist_eq, sub_zero, abs_of_pos hs'.1]
            exact lt_of_le_of_lt hs'.2 hτ.2
          exact hball hs''
      _ = ε * ENNReal.ofReal τ := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  calc ‖τ⁻¹‖ₑ * eLpNorm (fun x => ∫ s in Ioc (0 : ℝ) τ, (Heat.flow g s x - g x)) p volume
      ≤ ‖τ⁻¹‖ₑ * (ε * ENNReal.ofReal τ) := by
        gcongr
        exact hM.trans hbound
    _ = ε := by
        rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hτ0.le), mul_comm ε, ← mul_assoc,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hτ0.le), inv_mul_cancel₀ hτ0.ne',
          ENNReal.ofReal_one, one_mul]

end UnforcedLeray.B0418
