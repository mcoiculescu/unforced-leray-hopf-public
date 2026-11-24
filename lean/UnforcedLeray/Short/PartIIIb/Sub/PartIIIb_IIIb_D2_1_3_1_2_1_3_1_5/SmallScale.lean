import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

/-!
# Small scale limit of the phase pairing

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480.  For `h ∈ Y_2` and a phase test `Θ`, `⟪Θ * b_{(s)}, h⟫ → ⟪Θ, h⟫`
as `s → 0+`, for a kernel `b` with `∫ b = 1`.

Route: `Θ * b_{(s)} → Θ` pointwise (approximate identity, `dist_convolution_le'`), uniform
bound `‖Θ * b_{(s)}‖ ≤ M ∫‖b‖`, `y`-support uniformly bounded, and `h` locally integrable on the
phase cell (`locInt_of_isInYr`); dominated convergence on the phase measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF)

/-- Scaling of a kernel with support radius bound. -/
theorem sm_dilK_zero {b : Space → ℝ} {C : ℝ} (hC : ∀ z, C < ‖z‖ → b z = 0) {s : ℝ} (hs : 0 < s)
    (z : Space) (hz : s * C < ‖z‖) : dilK b s z = 0 := by
  unfold dilK
  have h1 : C < ‖s⁻¹ • z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs), inv_mul_eq_div]
    exact (lt_div_iff₀ hs).2 (by linarith)
  rw [hC _ h1, mul_zero]

theorem sm_dilK_integral {b : Space → ℝ} (hint : ∫ z, b z = 1) {s : ℝ} (hs : 0 < s) :
    ∫ z, dilK b s z = 1 := by
  unfold dilK
  rw [integral_const_mul]
  have := Measure.integral_comp_smul (μ := volume) b s⁻¹
  rw [this, hint, finrank_euclideanSpace_fin]
  rw [smul_eq_mul, mul_one, abs_of_pos (by positivity)]
  field_simp

theorem sm_dilK_norm_integral {b : Space → ℝ} {s : ℝ} (hs : 0 < s) :
    ∫ z, ‖dilK b s z‖ = ∫ z, ‖b z‖ := by
  have hpt : ∀ z, ‖dilK b s z‖ = (s⁻¹) ^ 3 * ‖b (s⁻¹ • z)‖ := by
    intro z
    unfold dilK
    rw [norm_mul, norm_pow, norm_inv, Real.norm_eq_abs, abs_of_pos hs]
  simp_rw [hpt]
  rw [integral_const_mul]
  have := Measure.integral_comp_smul (μ := volume) (fun z => ‖b z‖) s⁻¹
  rw [this, finrank_euclideanSpace_fin, abs_of_pos (by positivity), smul_eq_mul]
  field_simp

theorem sm_dilK_kerOK {b : Space → ℝ} (hb : KerOK b) {s : ℝ} (hs : 0 < s) :
    KerOK (dilK b s) := by
  refine ⟨?_, ?_⟩
  · unfold dilK
    exact contDiff_const.mul (hb.1.comp (contDiff_const_smul s⁻¹))
  · unfold dilK
    exact (hb.2.comp_smul (inv_ne_zero hs.ne')).mul_left

/-- Smoothness of the convolution in `y` (copy of the `ConvTest` argument). -/
theorem sm_smooth (P : ℝ) (κ : Space → ℝ) (Θ : ℝ × Space → CVec3) (hκ : KerOK κ)
    (hΘ : UnforcedLeray.PhaseSpace.IsPhaseTest P Θ) :
    ContDiff ℝ ∞ (convY κ Θ) := by
  obtain ⟨R, hR⟩ := hΘ.bounded_support
  have hf : LocallyIntegrable κ volume := hκ.1.continuous.locallyIntegrable
  have hgs : ∀ p : ℝ, ∀ x : Space, p ∈ (univ : Set ℝ) → x ∉ Metric.closedBall (0 : Space) R →
      (fun (τ : ℝ) (z : Space) => Θ (τ, z)) p x = 0 := by
    intro p x _ hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hR p x hx
  have hg : ContDiffOn ℝ ∞ (Function.uncurry fun (τ : ℝ) (z : Space) => Θ (τ, z))
      (univ ×ˢ univ) := by
    exact hΘ.smooth.contDiffOn
  have key := MeasureTheory.contDiffOn_convolution_right_with_param
    (μ := volume) (f := κ)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3)
    (s := univ) (k := Metric.closedBall (0 : Space) R)
    isOpen_univ (isCompact_closedBall _ _) hgs hf hg
  have heq : convY κ Θ = fun q : ℝ × Space =>
      (convolution κ ((fun (τ : ℝ) (z : Space) => Θ (τ, z)) q.1)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3) volume) q.2 := by
    funext x
    simp only [convY, convolution, ContinuousLinearMap.lsmul_apply, Complex.coe_smul]
  rw [heq]
  rw [Set.univ_prod_univ] at key
  exact contDiffOn_univ.mp key

theorem sm_convY_eq (κ : Space → ℝ) (Θ : ℝ × Space → CVec3) (τ : ℝ) (y : Space) :
    convY κ Θ (τ, y) =
      (convolution κ (fun w => Θ (τ, w)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3)
        volume) y := by
  simp only [convY, convolution_def, ContinuousLinearMap.lsmul_apply, Complex.coe_smul]

/-- Pointwise approximate identity: `Θ * b_{(s)} → Θ` at each point. -/
theorem sm_tendsto (b : Space → ℝ) (hb : KerOK b) (hint : ∫ z, b z = 1)
    (Θ : ℝ × Space → CVec3) (hΘ : Continuous Θ) (τ : ℝ) (y : Space) :
    Tendsto (fun s => convY (dilK b s) Θ (τ, y)) (𝓝[>] 0) (𝓝 (Θ (τ, y))) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb.2.isCompact.isBounded
  set L : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3 := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  set N : ℝ := ∫ z, ‖b z‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg (fun z => norm_nonneg _)
  set K : ℝ := ‖L‖ * N + 1 with hKdef
  have hK : 0 < K := by positivity
  have hCb : ∀ z, |C| < ‖z‖ → b z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h =>
      absurd (hC z h) (not_le.2 (lt_of_le_of_lt (le_abs_self C) hz)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont : ContinuousAt (fun w : Space => Θ (τ, w)) y :=
    (hΘ.comp (continuous_const.prodMk continuous_id)).continuousAt
  obtain ⟨δ, hδ, hδΘ⟩ := Metric.continuousAt_iff.1 hcont (ε / (2 * K)) (by positivity)
  have hlt : (0 : ℝ) < δ / (|C| + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hlt] with s hs
  obtain ⟨hs0, hs1⟩ := hs
  have hsδ : s * (|C| + 1) < δ := (lt_div_iff₀ (by positivity : (0:ℝ) < |C| + 1)).1 hs1
  have hKs := sm_dilK_kerOK hb hs0
  have hint_s : Integrable (dilK b s) volume :=
    hKs.1.continuous.integrable_of_hasCompactSupport hKs.2
  have hsupp : Function.support (dilK b s) ⊆ Metric.ball (0 : Space) (s * (|C| + 1)) := by
    intro z hz
    rw [Function.mem_support] at hz
    rw [mem_ball_zero_iff]
    by_contra hcon
    push Not at hcon
    apply hz
    have e : s * (|C| + 1) = s * |C| + s := by ring
    exact sm_dilK_zero hCb hs0 z (by linarith)
  have hmg : AEStronglyMeasurable (fun w : Space => Θ (τ, w)) volume :=
    (hΘ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hball : ∀ x ∈ Metric.ball y (s * (|C| + 1)),
      dist (Θ (τ, x)) (Θ (τ, y)) ≤ ε / (2 * K) := by
    intro x hx
    rw [Metric.mem_ball] at hx
    exact (hδΘ (hx.trans hsδ)).le
  have hdist := dist_convolution_le' (μ := volume) (L := L) (f := dilK b s)
    (g := fun w => Θ (τ, w)) (x₀ := y) (R := s * (|C| + 1)) (z₀ := Θ (τ, y))
    (ε := ε / (2 * K)) (by positivity) hint_s hsupp hmg hball
  have hI : ∫ t, L (dilK b s t) (Θ (τ, y)) ∂volume = Θ (τ, y) := by
    simp only [hLdef, ContinuousLinearMap.lsmul_apply]
    rw [integral_smul_const, sm_dilK_integral hint hs0, one_smul]
  have hNs : ∫ x, ‖dilK b s x‖ = N := sm_dilK_norm_integral hs0
  rw [hI, hNs] at hdist
  rw [sm_convY_eq]
  calc dist ((convolution (dilK b s) (fun w => Θ (τ, w)) L volume) y) (Θ (τ, y))
      ≤ (‖L‖ * N) * (ε / (2 * K)) := hdist
    _ ≤ K * (ε / (2 * K)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

theorem sm_support_radius {b : Space → ℝ} (hb : KerOK b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, C < ‖z‖ → b z = 0 := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb.2.isCompact.isBounded
  refine ⟨|C|, abs_nonneg _, fun z hz => image_eq_zero_of_notMem_tsupport (fun h =>
    absurd (hC z h) (not_le.2 (lt_of_le_of_lt (le_abs_self C) hz)))⟩

theorem sm_muP_eq (P : ℝ) : muP P = volume.restrict (Ioc 0 P ×ˢ (univ : Set Space)) := by
  unfold muP
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem sm_theta_bound (P : ℝ) (Θ : ℝ × Space → CVec3)
    (hΘ : UnforcedLeray.PhaseSpace.IsPhaseTest P Θ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Icc (0 : ℝ) P, ∀ w : Space, ‖Θ (τ, w)‖ ≤ M := by
  obtain ⟨R, hR⟩ := hΘ.bounded_support
  obtain ⟨M0, hM0⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) R)).exists_bound_of_continuousOn
    hΘ.smooth.continuous.continuousOn
  refine ⟨max M0 0, le_max_right _ _, fun τ hτ w => ?_⟩
  by_cases hw : ‖w‖ ≤ R
  · exact (hM0 (τ, w) (mem_prod.2 ⟨hτ, by simpa using hw⟩)).trans (le_max_left _ _)
  · rw [hR τ w (not_le.1 hw)]
    simp

theorem sm_convY_norm_le (b : Space → ℝ) (hb : KerOK b) (Θ : ℝ × Space → CVec3) (x : ℝ × Space)
    (M : ℝ) (hM : ∀ w : Space, ‖Θ (x.1, w)‖ ≤ M) {s : ℝ} (hs : 0 < s) :
    ‖convY (dilK b s) Θ x‖ ≤ M * ∫ z, ‖b z‖ := by
  unfold convY
  have hKs := sm_dilK_kerOK hb hs
  have hint : Integrable (fun z => ‖dilK b s z‖) volume :=
    (hKs.1.continuous.integrable_of_hasCompactSupport hKs.2).norm
  calc ‖∫ z, (dilK b s z : ℂ) • Θ (x.1, x.2 - z)‖
      ≤ ∫ z, M * ‖dilK b s z‖ := by
        refine norm_integral_le_of_norm_le (hint.const_mul M) (Eventually.of_forall fun z => ?_)
        calc ‖(dilK b s z : ℂ) • Θ (x.1, x.2 - z)‖ = ‖dilK b s z‖ * ‖Θ (x.1, x.2 - z)‖ := by
              rw [norm_smul, Complex.norm_real]
          _ ≤ ‖dilK b s z‖ * M := mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
          _ = M * ‖dilK b s z‖ := mul_comm _ _
    _ = M * ∫ z, ‖b z‖ := by
        rw [integral_const_mul, sm_dilK_norm_integral hs]

theorem sm_convY_zero {b : Space → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hCb : ∀ z, C < ‖z‖ → b z = 0)
    {R : ℝ} (Θ : ℝ × Space → CVec3) (hR : ∀ τ y, R < ‖y‖ → Θ (τ, y) = 0)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (x : ℝ × Space) (hx : R + C < ‖x.2‖) :
    convY (dilK b s) Θ x = 0 := by
  have hz : ∀ z : Space, (dilK b s z : ℂ) • Θ (x.1, x.2 - z) = 0 := by
    intro z
    by_cases h1 : ‖z‖ ≤ C
    · have h2 : R < ‖x.2 - z‖ := by
        have := norm_add_le (x.2 - z) z
        rw [sub_add_cancel] at this
        linarith
      rw [hR x.1 (x.2 - z) h2, smul_zero]
    · have h3 : s * C ≤ C := mul_le_of_le_one_left hC0 hs1
      have hz2 : dilK b s z = 0 :=
        sm_dilK_zero hCb hs z (lt_of_le_of_lt h3 (not_le.1 h1))
      rw [hz2, Complex.ofReal_zero, zero_smul]
  unfold convY
  simp only [hz, integral_zero]

theorem sm_h_integrableOn {P : ℝ} (hP : 0 < P) (h : ℝ × Space → CVec3)
    (hh : UnforcedLeray.Short.IIb.IsInYr P 2 h) (Rt : ℝ) :
    IntegrableOn (fun z => ‖h z‖) {z : ℝ × Space | ‖z.2‖ ≤ Rt} (muP P) := by
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) Rt) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hloc := locInt_of_isInYr hP hh
  have h1 : IntegrableOn (fun z => ‖h z‖) (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) Rt) volume :=
    (hloc.integrableOn_isCompact hK).norm
  have hT : MeasurableSet {z : ℝ × Space | ‖z.2‖ ≤ Rt} :=
    (isClosed_le (continuous_snd.norm) continuous_const).measurableSet
  rw [sm_muP_eq P]
  unfold IntegrableOn
  rw [Measure.restrict_restrict hT]
  refine IntegrableOn.mono_set h1 ?_
  intro z hz
  obtain ⟨hzT, hzA⟩ := hz
  have hzA' := mem_prod.1 hzA
  exact mem_prod.2 ⟨⟨le_of_lt hzA'.1.1, hzA'.1.2⟩, by simpa using hzT⟩

theorem sm_pointwise_zero_theta (Θ : ℝ × Space → CVec3) {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → Θ (τ, y) = 0) (z : ℝ × Space) (hz : R < ‖z.2‖) : Θ z = 0 := by
  have := hR z.1 z.2 hz
  simpa using this

theorem smallScale : UnforcedLeray.Short.PartIIIb.Concrete.SmallScale := by
  intro P hP h hh b hb hint Θ hΘ
  obtain ⟨R, hR⟩ := hΘ.bounded_support
  obtain ⟨C, hC0, hCb⟩ := sm_support_radius hb
  obtain ⟨M, hM0, hM⟩ := sm_theta_bound P Θ hΘ
  set N : ℝ := ∫ z, ‖b z‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg (fun z => norm_nonneg _)
  set Cg : ℝ := M * N + M with hCg
  have hCg0 : 0 ≤ Cg := by rw [hCg]; nlinarith [mul_nonneg hM0 hN0]
  set T : Set (ℝ × Space) := {z | ‖z.2‖ ≤ R + C} with hTdef
  have hTm : MeasurableSet T :=
    (isClosed_le (continuous_snd.norm) continuous_const).measurableSet
  set G : ℝ × Space → ℝ := T.indicator (fun z => Cg * ‖h z‖) with hGdef
  have hGint : Integrable G (muP P) :=
    (integrable_indicator_iff hTm).2 ((sm_h_integrableOn hP h hh (R + C)).const_mul Cg)
  have hae : ∀ᵐ z ∂(muP P), z.1 ∈ Ioc (0 : ℝ) P := by
    rw [sm_muP_eq P]
    exact (ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)).mono
      (fun z hz => hz.1)
  have hmeash : AEStronglyMeasurable h volume := hh.meas
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have hF_aesm : ∀ s : ℝ, 0 < s → AEStronglyMeasurable
      (fun z : ℝ × Space => dotL (convY (dilK b s) Θ z) (h z)) (muP P) := by
    intro s hs
    have hc : Continuous (convY (dilK b s) Θ) :=
      (sm_smooth P (dilK b s) Θ (sm_dilK_kerOK hb hs) hΘ).continuous
    exact (dotL.aestronglyMeasurable_comp₂ hc.aestronglyMeasurable hmeash).mono_ac (muP_ac P)
  have hF_bound : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ z ∂(muP P),
      ‖dotL (convY (dilK b s) Θ z) (h z)‖ ≤ G z := by
    intro s hs hs1
    filter_upwards [hae] with z hz
    by_cases hzT : z ∈ T
    · rw [hGdef, Set.indicator_of_mem hzT]
      calc ‖dotL (convY (dilK b s) Θ z) (h z)‖ ≤ ‖convY (dilK b s) Θ z‖ * ‖h z‖ :=
            dotL_norm_le _ _
        _ ≤ (M * N) * ‖h z‖ := mul_le_mul_of_nonneg_right
            (sm_convY_norm_le b hb Θ z M (fun w => hM z.1 (Ioc_subset_Icc_self hz) w) hs)
            (norm_nonneg _)
        _ ≤ Cg * ‖h z‖ := mul_le_mul_of_nonneg_right (by rw [hCg]; linarith) (norm_nonneg _)
    · have hfar : R + C < ‖z.2‖ := by
        simp only [hTdef, Set.mem_setOf_eq, not_le] at hzT
        exact hzT
      rw [hGdef, Set.indicator_of_notMem hzT, sm_convY_zero hC0 hCb Θ hR hs hs1 z hfar]
      simp
  have hF_int : ∀ s : ℝ, 0 < s → s ≤ 1 →
      Integrable (fun z : ℝ × Space => dotL (convY (dilK b s) Θ z) (h z)) (muP P) :=
    fun s hs hs1 => Integrable.mono' hGint (hF_aesm s hs) (hF_bound s hs hs1)
  have hF0_aesm : AEStronglyMeasurable (fun z : ℝ × Space => dotL (Θ z) (h z)) (muP P) :=
    (dotL.aestronglyMeasurable_comp₂ hΘ.smooth.continuous.aestronglyMeasurable hmeash).mono_ac
      (muP_ac P)
  have hF0_bound : ∀ᵐ z ∂(muP P), ‖dotL (Θ z) (h z)‖ ≤ G z := by
    filter_upwards [hae] with z hz
    by_cases hzT : z ∈ T
    · rw [hGdef, Set.indicator_of_mem hzT]
      calc ‖dotL (Θ z) (h z)‖ ≤ ‖Θ z‖ * ‖h z‖ := dotL_norm_le _ _
        _ ≤ M * ‖h z‖ := mul_le_mul_of_nonneg_right (hM z.1 (Ioc_subset_Icc_self hz) z.2)
            (norm_nonneg _)
        _ ≤ Cg * ‖h z‖ := mul_le_mul_of_nonneg_right (by rw [hCg]; nlinarith [mul_nonneg hM0 hN0])
            (norm_nonneg _)
    · have hfar : R < ‖z.2‖ := by
        simp only [hTdef, Set.mem_setOf_eq, not_le] at hzT
        linarith
      rw [hGdef, Set.indicator_of_notMem hzT, sm_pointwise_zero_theta Θ hR z hfar]
      simp
  have hlim : ∀ᵐ z ∂(muP P), Tendsto (fun s => dotL (convY (dilK b s) Θ z) (h z))
      (𝓝[>] 0) (𝓝 (dotL (Θ z) (h z))) := by
    refine ae_of_all _ (fun z => ?_)
    exact ((dotL.flip (h z)).continuous.tendsto (Θ z)).comp
      (sm_tendsto b hb hint Θ hΘ.continuous z.1 z.2)
  have hFm : ∀ᶠ s in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun z : ℝ × Space => dotL (convY (dilK b s) Θ z) (h z)) (muP P) := by
    filter_upwards [hev] with s hs
    exact hF_aesm s hs.1
  have hbd : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᵐ z ∂(muP P),
      ‖dotL (convY (dilK b s) Θ z) (h z)‖ ≤ G z := by
    filter_upwards [hev] with s hs
    exact hF_bound s hs.1 hs.2.le
  have hDCT := tendsto_integral_filter_of_dominated_convergence G hFm hbd hGint hlim
  have hpair : ∀ᶠ s in 𝓝[>] (0 : ℝ), pairF P (convY (dilK b s) Θ) h =
      (P⁻¹ : ℝ) • ∫ z, dotL (convY (dilK b s) Θ z) (h z) ∂(muP P) := by
    filter_upwards [hev] with s hs
    exact pair_eq_integral P _ h (hF_int s hs.1 hs.2.le)
  have hp0 : pairF P Θ h = (P⁻¹ : ℝ) • ∫ z, dotL (Θ z) (h z) ∂(muP P) :=
    pair_eq_integral P Θ h (Integrable.mono' hGint hF0_aesm hF0_bound)
  rw [hp0]
  exact Tendsto.congr' (hpair.mono fun s hs => hs.symm) (hDCT.const_smul (P⁻¹ : ℝ))

end UnforcedLeray.Short.PartIIIb.Concrete
