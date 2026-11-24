import UnforcedLeray.Units.B0418.HeatLp
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# B0418 helper: strong continuity of translations, dilations and heat flow on `L^p`

Blueprint unit B0418 (`paper/main.tex` lines 7411--7427, "It is strongly continuous"),
proof outline: "Strong continuity follows from strong continuity of the heat semigroup
and of dilations" (blueprint infrastructure INF04, INF07). For `1 ≤ p < ∞` this file proves

* continuity at the identity of composition operators (translations `x ↦ x - z`,
  dilations `x ↦ b • x`) on `L^p(ℝ³; ℝ³)`, by density of continuous compactly
  supported fields (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`) and dominated
  convergence;
* strong continuity at time zero of the literal heat flow `Heat.flow` on `L^p`, by
  Minkowski's integral inequality and the Gaussian change of variables.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UnforcedLeray.B0418

variable {p : ℝ≥0∞}

/-- Exact `L^p` transport of a dilation in three dimensions (any `p ≠ ∞`). -/
theorem eLpNorm_comp_dilation (hp : p ≠ ∞) {b : ℝ} (hb : b ≠ 0) (u : SpatialField) :
    eLpNorm (fun x : Space => u (b • x)) p volume =
      (ENNReal.ofReal |(b ^ 3)⁻¹|) ^ (1 / p).toReal * eLpNorm u p volume := by
  change eLpNorm (u ∘ fun x : Space => b • x) p volume = _
  rw [← (SpatialScaling.dilation_measurableEmbedding hb).eLpNorm_map_measure,
    SpatialScaling.map_dilation hb, eLpNorm_smul_measure_of_ne_top hp]
  rfl

/-- Continuous compactly supported fields: composition operators converging pointwise to
the identity, with uniform support control, converge strongly in `L^p`. -/
theorem tendsto_eLpNorm_comp_sub_of_compact {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated]
    (φ : ι → Space → Space) (hφc : ∀ᶠ i in l, Continuous (φ i))
    (hφ : ∀ x, Tendsto (fun i => φ i x) l (𝓝 x))
    (hsupp : ∀ R : ℝ, ∃ R' : ℝ, ∀ᶠ i in l, ∀ x, ‖φ i x‖ ≤ R → ‖x‖ ≤ R')
    {g : SpatialField} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    Tendsto (fun i => eLpNorm (fun x => g (φ i x) - g x) p volume) l (𝓝 0) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : Space)
  obtain ⟨R', hR'⟩ := hsupp R
  have hzero : ∀ y, R < ‖y‖ → g y = 0 := by
    intro y hy
    by_contra hne
    have h1 := hR (subset_tsupport g hne)
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  have hp0 : p ≠ 0 := ne_zero_of_one_le hp1
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  have hlim : Tendsto (fun i => ∫⁻ x, ‖g (φ i x) - g x‖ₑ ^ p.toReal) l
      (𝓝 (∫⁻ _x : Space, (0 : ℝ≥0∞))) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      ((Metric.closedBall (0 : Space) (max R R')).indicator
        (fun _ => (ENNReal.ofReal (2 * M)) ^ p.toReal)) ?_ ?_ ?_ ?_
    · filter_upwards [hφc] with i hi
      exact ((hg.comp hi).sub hg).enorm.measurable.pow_const _
    · filter_upwards [hR'] with i hi
      refine Eventually.of_forall (fun x => ?_)
      by_cases hx : ‖x‖ ≤ max R R'
      · rw [Set.indicator_of_mem (by simpa using hx)]
        gcongr
        rw [← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        calc ‖g (φ i x) - g x‖ ≤ ‖g (φ i x)‖ + ‖g x‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hM _) (hM _)
          _ = 2 * M := by ring
      · rw [Set.indicator_of_notMem (by simpa using hx)]
        have h1 : R' < ‖x‖ := lt_of_le_of_lt (le_max_right _ _) (not_le.mp hx)
        have h2 : R < ‖x‖ := lt_of_le_of_lt (le_max_left _ _) (not_le.mp hx)
        have h3 : R < ‖φ i x‖ := by
          by_contra h
          exact absurd (hi x (not_lt.mp h)) (not_le.mpr h1)
        rw [hzero _ h3, hzero _ h2, sub_zero, enorm_zero, ENNReal.zero_rpow_of_pos hpr]
    · rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpr.le ENNReal.ofReal_ne_top)
        measure_closedBall_lt_top.ne
    · refine Eventually.of_forall (fun x => ?_)
      have h1 : Tendsto (fun i => g (φ i x) - g x) l (𝓝 0) := by
        have := ((hg.tendsto x).comp (hφ x)).sub_const (g x)
        simpa using this
      have h2 := (continuous_enorm.tendsto (0 : Space)).comp h1
      rw [enorm_zero] at h2
      have h3 := ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0).comp h2
      rw [ENNReal.zero_rpow_of_pos hpr] at h3
      exact h3
  rw [lintegral_zero] at hlim
  have h4 := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by positivity)] at h4

/-- Density upgrade: uniformly bounded composition operators converging pointwise to the
identity converge strongly on all of `L^p`, `1 ≤ p < ∞`. -/
theorem tendsto_eLpNorm_comp_sub {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (φ : ι → Space → Space) (hφc : ∀ᶠ i in l, Continuous (φ i))
    (hφ : ∀ x, Tendsto (fun i => φ i x) l (𝓝 x))
    (hsupp : ∀ R : ℝ, ∃ R' : ℝ, ∀ᶠ i in l, ∀ x, ‖φ i x‖ ≤ R → ‖x‖ ≤ R')
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ᶠ i in l, ∀ u : SpatialField, MemLp u p volume →
      MemLp (fun x => u (φ i x)) p volume ∧
        eLpNorm (fun x => u (φ i x)) p volume ≤ C * eLpNorm u p volume)
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) {h : SpatialField} (hh : MemLp h p volume) :
    Tendsto (fun i => eLpNorm (fun x => h (φ i x) - h x) p volume) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr0
  set δ : ℝ := r / (2 * (C.toReal + 1)) with hδ
  have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g, hgc, hgh, hgcont, hgm⟩ :=
    hh.exists_hasCompactSupport_eLpNorm_sub_le hp (ε := ENNReal.ofReal δ)
      (by simpa using hδ0)
  have hT := tendsto_eLpNorm_comp_sub_of_compact φ hφc hφ hsupp hgcont hgc hp1 hp
  have hev := (ENNReal.tendsto_nhds_zero.mp hT) (ENNReal.ofReal (r / 2))
    (by simpa using hr)
  filter_upwards [hev, hbound] with i hi hb
  have hA := hb (h - g) (hh.sub hgm)
  have hdec : (fun x => h (φ i x) - h x) =
      (fun x => (h - g) (φ i x)) + ((fun x => g (φ i x) - g x) + (g - h)) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  have hgh' : eLpNorm (g - h) p volume ≤ ENNReal.ofReal δ := by
    rw [eLpNorm_sub_comm]
    exact hgh
  have hmB : AEStronglyMeasurable (fun x => g (φ i x) - g x) volume :=
    (hb g hgm).1.aestronglyMeasurable.sub hgm.aestronglyMeasurable
  have hkey : C * ENNReal.ofReal δ + (ENNReal.ofReal (r / 2) + ENNReal.ofReal δ) =
      ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal hC, ← ENNReal.ofReal_mul hC0,
      ← ENNReal.ofReal_add (by positivity) hδ0.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    rw [hδ]
    field_simp
    ring
  calc eLpNorm (fun x => h (φ i x) - h x) p volume
      ≤ eLpNorm (fun x => (h - g) (φ i x)) p volume +
          eLpNorm ((fun x => g (φ i x) - g x) + (g - h)) p volume := by
        rw [hdec]
        exact eLpNorm_add_le hA.1.aestronglyMeasurable
          (hmB.add (hgm.aestronglyMeasurable.sub hh.aestronglyMeasurable)) hp1
    _ ≤ eLpNorm (fun x => (h - g) (φ i x)) p volume +
          (eLpNorm (fun x => g (φ i x) - g x) p volume + eLpNorm (g - h) p volume) := by
        gcongr
        exact eLpNorm_add_le hmB (hgm.aestronglyMeasurable.sub hh.aestronglyMeasurable) hp1
    _ ≤ C * ENNReal.ofReal δ + (ENNReal.ofReal (r / 2) + ENNReal.ofReal δ) := by
        gcongr
        exact hA.2.trans (by gcongr)
    _ = ENNReal.ofReal r := hkey
    _ ≤ ε := hrε.le

/-- Strong continuity of translations on `L^p`, `1 ≤ p < ∞`. -/
theorem tendsto_translation (hp1 : 1 ≤ p) (hp : p ≠ ∞) {h : SpatialField}
    (hh : MemLp h p volume) :
    Tendsto (fun z : Space => eLpNorm (fun x => h (x - z) - h x) p volume) (𝓝 0) (𝓝 0) := by
  refine tendsto_eLpNorm_comp_sub (fun z x => x - z) ?_ ?_ ?_ 1 ENNReal.one_ne_top ?_ hp1 hp hh
  · exact Eventually.of_forall (fun z => continuous_id.sub continuous_const)
  · intro x
    have := (tendsto_id (x := 𝓝 (0 : Space))).const_sub x
    simpa using this
  · intro R
    refine ⟨R + 1, ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : Space) one_pos] with z hz x hx
    rw [Metric.mem_ball, dist_zero_right] at hz
    calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith
  · refine Eventually.of_forall (fun z u hu => ⟨?_, ?_⟩)
    · exact hu.comp_measurePreserving (measurePreserving_sub_right (volume : Measure Space) z)
    · rw [one_mul]
      exact (eLpNorm_comp_measurePreserving hu.aestronglyMeasurable
        (measurePreserving_sub_right (volume : Measure Space) z)).le

/-- Strong continuity of dilations at the identity on `L^p`, `1 ≤ p < ∞`. -/
theorem tendsto_dilation (hp1 : 1 ≤ p) (hp : p ≠ ∞) {h : SpatialField}
    (hh : MemLp h p volume) :
    Tendsto (fun b : ℝ => eLpNorm (fun x => h (b • x) - h x) p volume) (𝓝 1) (𝓝 0) := by
  have hnear : ∀ᶠ b : ℝ in 𝓝 1, 1 / 2 < b :=
    lt_mem_nhds (by norm_num)
  refine tendsto_eLpNorm_comp_sub (fun b x => b • x) ?_ ?_ ?_
    ((ENNReal.ofReal 8) ^ (1 / p).toReal)
    (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) ?_ hp1 hp hh
  · exact Eventually.of_forall (fun b => continuous_id.const_smul b)
  · intro x
    have := (tendsto_id (x := 𝓝 (1 : ℝ))).smul_const x
    simpa using this
  · intro R
    refine ⟨2 * |R|, ?_⟩
    filter_upwards [hnear] with b hb x hx
    rw [norm_smul, Real.norm_of_nonneg (by linarith)] at hx
    have h1 : 1 / 2 * ‖x‖ ≤ b * ‖x‖ := mul_le_mul_of_nonneg_right hb.le (norm_nonneg _)
    have h2 := le_abs_self R
    linarith
  · filter_upwards [hnear] with b hb u hu
    have hb0 : b ≠ 0 := by intro h0; rw [h0] at hb; norm_num at hb
    refine ⟨SpatialScaling.memLp_comp_dilation hu hb0, ?_⟩
    rw [eLpNorm_comp_dilation hp hb0]
    gcongr
    have hbp : 0 < b := by linarith
    rw [abs_of_pos (by positivity)]
    have : (1 / 2 : ℝ) ^ 3 ≤ b ^ 3 := by gcongr
    calc (b ^ 3)⁻¹ ≤ ((1 / 2 : ℝ) ^ 3)⁻¹ := by gcongr
      _ = 8 := by norm_num

/-! ### Strong continuity of the heat flow -/

/-- The `L^p` translation modulus `y ↦ ‖h(· - y) - h‖_p`. -/
def transModulus (p : ℝ≥0∞) (h : SpatialField) (y : Space) : ℝ≥0∞ :=
  eLpNorm (fun x => h (x - y) - h x) p volume

theorem measurable_transModulus (hp1 : 1 ≤ p) (hp : p ≠ ∞) {h : SpatialField}
    (hh : StronglyMeasurable h) : Measurable (transModulus p h) := by
  unfold transModulus
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_zero_of_one_le hp1) hp]
  refine Measurable.pow_const ?_ _
  exact Measurable.lintegral_prod_right'
    (f := fun z : Space × Space => ‖h (z.2 - z.1) - h z.2‖ₑ ^ p.toReal)
    (((hh.measurable.comp (measurable_snd.sub measurable_fst)).sub
      (hh.measurable.comp measurable_snd)).enorm.pow_const _)

theorem transModulus_le (hp1 : 1 ≤ p) {h : SpatialField}
    (hh : AEStronglyMeasurable h volume) (y : Space) :
    transModulus p h y ≤ 2 * eLpNorm h p volume := by
  unfold transModulus
  have hmp := measurePreserving_sub_right (volume : Measure Space) y
  calc eLpNorm (fun x => h (x - y) - h x) p volume
      ≤ eLpNorm (fun x => h (x - y)) p volume + eLpNorm h p volume :=
        eLpNorm_sub_le (hh.comp_measurePreserving hmp) hh hp1
    _ = 2 * eLpNorm h p volume := by
        change eLpNorm (h ∘ fun x => x - y) p volume + _ = _
        rw [eLpNorm_comp_measurePreserving hh hmp, two_mul]

/-- Minkowski bound of the heat increment by the translation modulus. -/
theorem eLpNorm_flow_sub_le {t : ℝ} (ht : 0 < t) (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {h : SpatialField} (hhm : StronglyMeasurable h) (hh : MemLp h p volume) :
    eLpNorm (Heat.flow h t - h) p volume ≤
      ∫⁻ y, ENNReal.ofReal (Heat.kernel t y) * transModulus p h y := by
  have hrep : Heat.flow h t - h = fun x => ∫ y, Heat.kernel t y • (h (x - y) - h x) := by
    funext x
    rw [Pi.sub_apply, Heat.flow_pos h ht]
    simp only [smul_sub]
    rw [integral_sub (heat_integrand_integrable ht hp1 hp hh x)
      ((Heat.kernel_integrable ht).smul_const (h x)), integral_smul_const,
      Heat.integral_kernel ht, one_smul]
    rfl
  rw [hrep]
  have hjoint : AEStronglyMeasurable
      (Function.uncurry fun x y => Heat.kernel t y • (h (x - y) - h x))
      ((volume : Measure Space).prod volume) := by
    apply StronglyMeasurable.aestronglyMeasurable
    exact ((Heat.Gaussian.kernel_smooth (4 * t)).continuous.comp
      continuous_snd).stronglyMeasurable.smul
      ((hhm.comp_measurable (measurable_fst.sub measurable_snd)).sub
        (hhm.comp_measurable measurable_fst))
  refine (NonUniqueEuler.Conv.eLpNorm_integral_le hjoint hp1 hp).trans (le_of_eq ?_)
  apply lintegral_congr
  intro y
  change eLpNorm (Heat.kernel t y • (fun x => h (x - y) - h x)) p volume = _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (Heat.kernel_nonneg ht y)]
  rfl

/-- Gaussian change of variables in the Minkowski bound: the heat kernel at time `t`
is the unit Gaussian dilated by `c = √(4t)`. -/
theorem lintegral_kernel_mul_eq {t : ℝ} (ht : 0 < t) (ω : Space → ℝ≥0∞) :
    ∫⁻ y, ENNReal.ofReal (Heat.kernel t y) * ω y =
      ∫⁻ w, ENNReal.ofReal (Heat.Gaussian.kernel 1 w) * ω (Real.sqrt (4 * t) • w) := by
  set c := Real.sqrt (4 * t) with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = 4 * t := Real.sq_sqrt (by positivity)
  have hcne : c ≠ 0 := hc0.ne'
  let G : Space → ℝ≥0∞ := fun y => ENNReal.ofReal (Heat.kernel t y) * ω y
  have hmap := (SpatialScaling.dilation_measurableEmbedding hcne).lintegral_map
    (μ := (volume : Measure Space)) G
  rw [SpatialScaling.map_dilation hcne, lintegral_smul_measure] at hmap
  have hG : (fun w : Space => G (c • w)) = fun w =>
      ENNReal.ofReal |(c ^ 3)⁻¹| *
        (ENNReal.ofReal (Heat.Gaussian.kernel 1 w) * ω (c • w)) := by
    funext w
    simp only [G]
    rw [Heat.kernel, ← hc2, Heat.Gaussian.kernel_squareScale hc0,
      abs_of_pos (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
  rw [hG, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hmap
  have h0 : ENNReal.ofReal |(c ^ 3)⁻¹| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  exact (ENNReal.mul_right_inj h0 ENNReal.ofReal_ne_top).mp (by simpa [smul_eq_mul] using hmap)

theorem lintegral_unitGaussian :
    ∫⁻ w : Space, ENNReal.ofReal (Heat.Gaussian.kernel 1 w) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Heat.Gaussian.kernel_integrable one_pos)
    (Eventually.of_forall (fun w => Heat.Gaussian.kernel_nonneg one_pos w)),
    Heat.Gaussian.integral_kernel one_pos, ENNReal.ofReal_one]

/-- Strong continuity of the literal heat flow at time zero on `L^p`, `1 ≤ p < ∞`. -/
theorem tendsto_flow_sub (hp1 : 1 ≤ p) (hp : p ≠ ∞) {h : SpatialField}
    (hh : MemLp h p volume) :
    Tendsto (fun t => eLpNorm (Heat.flow h t - h) p volume) (𝓝 0) (𝓝 0) := by
  set h' := hh.1.mk h with hh'def
  have hae : h =ᵐ[volume] h' := hh.1.ae_eq_mk
  have hh' : MemLp h' p volume := hh.ae_eq hae
  have hm' : StronglyMeasurable h' := hh.1.stronglyMeasurable_mk
  have heq : ∀ t, eLpNorm (Heat.flow h t - h) p volume =
      eLpNorm (Heat.flow h' t - h') p volume := by
    intro t
    apply eLpNorm_congr_ae
    have hflow : Heat.flow h t =ᵐ[volume] Heat.flow h' t := by
      by_cases ht : 0 < t
      · rw [Heat.flow_pos _ ht, Heat.flow_pos _ ht, Heat.average_congr_ae hae t]
      · rw [Heat.flow_nonpos _ (not_lt.mp ht), Heat.flow_nonpos _ (not_lt.mp ht)]
        exact hae
    exact hflow.sub hae
  simp_rw [heq]
  let Φ : ℝ → ℝ≥0∞ := fun c =>
    ∫⁻ w, ENNReal.ofReal (Heat.Gaussian.kernel 1 w) * transModulus p h' (c • w)
  have hΦ : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have hlim := tendsto_lintegral_filter_of_dominated_convergence
      (μ := (volume : Measure Space)) (l := 𝓝 (0 : ℝ))
      (F := fun c w => ENNReal.ofReal (Heat.Gaussian.kernel 1 w) * transModulus p h' (c • w))
      (f := fun _ => 0)
      (fun w => ENNReal.ofReal (Heat.Gaussian.kernel 1 w) * (2 * eLpNorm h' p volume))
      ?_ ?_ ?_ ?_
    · simpa [Φ] using hlim
    · refine Eventually.of_forall (fun c => ?_)
      exact (ENNReal.measurable_ofReal.comp
        (Heat.Gaussian.kernel_smooth 1).continuous.measurable).mul
        ((measurable_transModulus hp1 hp hm').comp (measurable_const_smul c))
    · refine Eventually.of_forall (fun c => Eventually.of_forall (fun w => ?_))
      gcongr
      exact transModulus_le hp1 hm'.aestronglyMeasurable _
    · rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hh'.2.ne),
        lintegral_unitGaussian, one_mul]
      exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top hh'.2.ne
    · refine Eventually.of_forall (fun w => ?_)
      have h1 : Tendsto (fun c : ℝ => c • w) (𝓝 0) (𝓝 0) := by
        have := (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const w
        simpa using this
      have h2 := (tendsto_translation hp1 hp hh').comp h1
      have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)
        (a := ENNReal.ofReal (Heat.Gaussian.kernel 1 w))
      rw [mul_zero] at h3
      exact h3
  have hsq : Tendsto (fun t : ℝ => Real.sqrt (4 * t)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => Real.sqrt (4 * t)) :=
      Real.continuous_sqrt.comp (continuous_const.mul continuous_id)
    have := hc.tendsto (0 : ℝ)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hΦ.comp hsq)
    (fun _ => zero_le) (fun t => ?_)
  by_cases ht : 0 < t
  · exact (eLpNorm_flow_sub_le ht hp1 hp hm' hh').trans_eq
      (lintegral_kernel_mul_eq ht _)
  · rw [Heat.flow_nonpos _ (not_lt.mp ht), sub_self, eLpNorm_zero]
    exact zero_le

end UnforcedLeray.B0418
