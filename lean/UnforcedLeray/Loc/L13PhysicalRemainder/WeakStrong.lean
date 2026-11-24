import UnforcedLeray.Loc.L13PhysicalRemainder.Dilation

/-!
# Step L13, helpers: from the similarity weak equation to the physical strong equation

Support for `Loc/L13PhysicalRemainder.lean` (step L13 `PhysicalRemainderStep`,
`paper/main.tex` lines 525–547, blueprint units B1026, B1028, B1029).

* `IsSimilarityWeakSolution h S R F`: the remainder equation
  `∂_τR = hΔR + ½R + ½y·∇R + F` (lines 517–522, the linear part `𝓛₀` of line 293) in weak form
  at every phase of `S`: for every vector test `φ`,
  `d/dτ ⟨R(τ), φ⟩ = ⟨hΔR(τ) + F(τ), φ⟩ - ⟨R(τ), φ⟩ - ½⟨R(τ), (y·∇)φ⟩`
  (the adjoint of `½y·∇ + ½` is `-1 - ½y·∇`, as in `Package.linearBackgroundIntegrand`).
* The physical fields of lines 525–531: `ρ(t) = D(-log t) R(log t)` in `H²` and
  `N(t) = t⁻¹ D(-log t) F(log t)`, i.e. `t^{-1/2}R(·/√t, log t)` and
  `t^{-3/2}F(·/√t, log t)`.
* `physical_hasDerivAt_of_similarity`: a similarity weak solution on `(-∞,τ₀)` gives the
  strong physical equation `∂_tρ = hΔρ + N` in `L²` on `(0, e^{τ₀})` (lines 546–547). The
  proof differentiates `⟨ρ(t), φ⟩ = t ⟨R(log t), φ(√t·)⟩`; the `L²` derivative of the dilated
  test, `½ (y·∇)(φ(√t·))`, cancels the drift term. A weakly differentiable `L²` path whose
  weak derivative is a continuous `L²` path is strongly differentiable (`hasDerivAt_of_weak`).

The `L²` derivative of dilated tests adapts `B0418.tendsto_dilation_generator`

`L^p` limits to the two-sided `L²` derivative.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L13

open SobolevGraph
open UnforcedLeray.Loc.L02 (dil dilH2 coeFn_dil norm_dil_apply_le dil_mem_solenoidal)

/-! ## The `L²` derivative of a dilated test -/

theorem contDiff_one_of_infty' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 1 f :=
  hf.of_le (by exact_mod_cast le_top)

/-- `(y·∇)φ(y) = Dφ(y) y`. -/
def radialDeriv (φ : Space → Space) : SpatialField := fun y => fderiv ℝ φ y y

/-- The dilated test `φ(e^{τ/2}·)` as an `L²` class. -/
def testDilation (φ : Space → Space) (τ : ℝ) : L2Space :=
  toL2 (fun y => φ (Real.exp (τ / 2) • y))

theorem isVectorTest_radialDeriv {φ : Space → Space} (hφ : IsVectorTest φ) :
    IsVectorTest (radialDeriv φ) := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.smooth.fderiv_right (by simp)
    exact h1.clm_apply contDiff_id
  · apply HasCompactSupport.intro hφ.compact.isCompact
    intro y hy
    simp only [radialDeriv]
    rw [fderiv_of_notMem_tsupport ℝ hy]
    simp

/-- `r⁻¹ (φ(e^{r/2}y) - φ(y)) → ½ Dφ(y) y` in `L²` as `r → 0`, `r ≠ 0`. -/
theorem tendsto_testDilation_slope {φ : Space → Space} (hφ : IsVectorTest φ) :
    Tendsto (fun r : ℝ => eLpNorm (fun y => r⁻¹ • (φ (Real.exp (r / 2) • y) - φ y) -
      (1 / 2 : ℝ) • fderiv ℝ φ y y) 2 volume) (𝓝[≠] 0) (𝓝 0) := by
  have hs := hφ.smooth
  have hc := hφ.compact
  have hdiff : Differentiable ℝ φ := (contDiff_one_of_infty' hs).differentiable one_ne_zero
  have hcf : Continuous (fderiv ℝ φ) := (contDiff_one_of_infty' hs).continuous_fderiv one_ne_zero
  obtain ⟨L, hL⟩ := hcf.bounded_above_of_compact_support (hc.fderiv ℝ)
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Space)
  set L' := max L 0
  set R' := 2 * max R 0
  have hR'0 : 0 ≤ R' := by positivity
  have hzero : ∀ y : Space, R < ‖y‖ → y ∉ tsupport φ := by
    intro y hy hm
    have h1 := hR hm
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  have hlip : ∀ u v : Space, ‖φ u - φ v‖ ≤ L' * ‖u - v‖ := by
    intro u v
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff x)
      (fun x _ => (hL x).trans (le_max_left _ _)) (mem_univ v) (mem_univ u)
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hpr : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hd0 : HasDerivAt (fun r : ℝ => Real.exp (r / 2)) (Real.exp (0 / 2) * (1 / 2)) 0 :=
    (Real.hasDerivAt_exp _).comp 0 ((hasDerivAt_id 0).div_const 2)
  have hb : Tendsto (fun r : ℝ => r⁻¹ * (Real.exp (r / 2) - 1)) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have h := hasDerivAt_iff_tendsto_slope_zero.mp hd0
    simpa using h
  have hbev : ∀ᶠ r in 𝓝[≠] (0 : ℝ), |r⁻¹ * (Real.exp (r / 2) - 1)| < 1 := by
    have : Tendsto (fun r : ℝ => |r⁻¹ * (Real.exp (r / 2) - 1)|) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
      have := hb.abs
      rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    exact this.eventually (gt_mem_nhds (by norm_num))
  have hhalf : ∀ᶠ r in 𝓝[≠] (0 : ℝ), (1 / 2 : ℝ) < Real.exp (r / 2) := by
    have hcont : Tendsto (fun r : ℝ => Real.exp (r / 2)) (𝓝[≠] 0) (𝓝 1) := by
      have hc' : Continuous (fun r : ℝ => Real.exp (r / 2)) :=
        Real.continuous_exp.comp (continuous_id.div_const 2)
      have := (hc'.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
      simpa using this
    exact hcont.eventually (lt_mem_nhds (by norm_num))
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  have hlim : Tendsto (fun r : ℝ => ∫⁻ y, ‖r⁻¹ • (φ (Real.exp (r / 2) • y) - φ y) -
      (1 / 2 : ℝ) • fderiv ℝ φ y y‖ₑ ^ (2 : ℝ≥0∞).toReal) (𝓝[≠] 0)
      (𝓝 (∫⁻ _y : Space, (0 : ℝ≥0∞))) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      ((Metric.closedBall (0 : Space) R').indicator
        (fun _ => (ENNReal.ofReal (2 * L' * R')) ^ (2 : ℝ≥0∞).toReal)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall (fun r => ?_)
      have hA : Continuous (fun y : Space => φ (Real.exp (r / 2) • y)) :=
        hs.continuous.comp (continuous_const_smul _)
      have hB : Continuous (fun y : Space => fderiv ℝ φ y y) := hcf.clm_apply continuous_id
      have hc1 : Continuous (fun y : Space => r⁻¹ • (φ (Real.exp (r / 2) • y) - φ y) -
          (1 / 2 : ℝ) • fderiv ℝ φ y y) :=
        ((hA.sub hs.continuous).const_smul r⁻¹).sub (hB.const_smul (1 / 2 : ℝ))
      exact hc1.enorm.measurable.pow_const _
    · filter_upwards [hbev, hhalf] with r hbr hhr
      refine Eventually.of_forall (fun y => ?_)
      by_cases hy : ‖y‖ ≤ R'
      · rw [Set.indicator_of_mem (by simpa using hy)]
        gcongr
        rw [← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        have h1 : ‖r⁻¹ • (φ (Real.exp (r / 2) • y) - φ y)‖ ≤ L' * R' := by
          rw [norm_smul, Real.norm_eq_abs]
          have h2 := hlip (Real.exp (r / 2) • y) y
          have h3 : ‖Real.exp (r / 2) • y - y‖ = |Real.exp (r / 2) - 1| * ‖y‖ := by
            rw [show Real.exp (r / 2) • y - y = (Real.exp (r / 2) - 1) • y by
              rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
          rw [h3] at h2
          calc |r⁻¹| * ‖φ (Real.exp (r / 2) • y) - φ y‖
              ≤ |r⁻¹| * (L' * (|Real.exp (r / 2) - 1| * ‖y‖)) :=
                mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
            _ = L' * |r⁻¹ * (Real.exp (r / 2) - 1)| * ‖y‖ := by rw [abs_mul]; ring
            _ ≤ L' * 1 * R' :=
                mul_le_mul (mul_le_mul_of_nonneg_left hbr.le (le_max_right _ _)) hy
                  (norm_nonneg _) (by positivity)
            _ = L' * R' := by ring
        have h4 : ‖(1 / 2 : ℝ) • fderiv ℝ φ y y‖ ≤ L' * R' := by
          rw [norm_smul]
          have h5 : ‖fderiv ℝ φ y y‖ ≤ L' * R' :=
            ((fderiv ℝ φ y).le_opNorm y).trans
              (mul_le_mul ((hL y).trans (le_max_left _ _)) hy (norm_nonneg _) (le_max_right _ _))
          calc ‖(1 / 2 : ℝ)‖ * ‖fderiv ℝ φ y y‖ ≤ 1 * (L' * R') := by
                gcongr
                norm_num
            _ = L' * R' := one_mul _
        calc ‖r⁻¹ • (φ (Real.exp (r / 2) • y) - φ y) - (1 / 2 : ℝ) • fderiv ℝ φ y y‖
            ≤ ‖r⁻¹ • (φ (Real.exp (r / 2) • y) - φ y)‖ + ‖(1 / 2 : ℝ) • fderiv ℝ φ y y‖ :=
              norm_sub_le _ _
          _ ≤ L' * R' + L' * R' := add_le_add h1 h4
          _ = 2 * L' * R' := by ring
      · rw [Set.indicator_of_notMem (by simpa using hy)]
        have hRle : R ≤ max R 0 := le_max_left _ _
        have hR0 : 0 ≤ max R 0 := le_max_right _ _
        have hy' : R < ‖y‖ := by
          have : R' < ‖y‖ := not_le.mp hy
          linarith
        have hy0 : y ∉ tsupport φ := hzero y hy'
        have hly : R < ‖Real.exp (r / 2) • y‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          have : R' < ‖y‖ := not_le.mp hy
          nlinarith
        rw [image_eq_zero_of_notMem_tsupport (hzero _ hly),
          image_eq_zero_of_notMem_tsupport hy0, fderiv_of_notMem_tsupport ℝ hy0]
        simp only [sub_self, smul_zero, ContinuousLinearMap.zero_apply, enorm_zero]
        rw [ENNReal.zero_rpow_of_pos hpr]
    · rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpr.le ENNReal.ofReal_ne_top)
        measure_closedBall_lt_top.ne
    · refine Eventually.of_forall (fun y => ?_)
      have hd1 : HasDerivAt (fun r : ℝ => Real.exp (r / 2) • y)
          ((Real.exp (0 / 2) * (1 / 2)) • y) 0 := hd0.smul_const y
      have hd2 := (hdiff (Real.exp (0 / 2) • y)).hasFDerivAt.comp_hasDerivAt 0 hd1
      have hd3 : HasDerivAt (fun r : ℝ => φ (Real.exp (r / 2) • y))
          (fderiv ℝ φ y ((1 / 2 : ℝ) • y)) 0 := by
        have e1 : Real.exp (0 / 2) • y = y := by simp
        have e2 : (Real.exp (0 / 2) * (1 / 2)) • y = (1 / 2 : ℝ) • y := by simp
        rw [e1, e2] at hd2
        exact hd2
      have hsl := hasDerivAt_iff_tendsto_slope_zero.mp hd3
      have hsl' : Tendsto (fun r : ℝ => r⁻¹ • (φ (Real.exp (r / 2) • y) - φ y))
          (𝓝[≠] 0) (𝓝 (fderiv ℝ φ y ((1 / 2 : ℝ) • y))) := by
        simpa using hsl
      have h1 := hsl'.sub_const ((1 / 2 : ℝ) • fderiv ℝ φ y y)
      rw [map_smul, sub_self] at h1
      have h2 := (continuous_enorm.tendsto (0 : Space)).comp h1
      rw [enorm_zero] at h2
      have h3 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal)).tendsto 0).comp h2
      rw [ENNReal.zero_rpow_of_pos hpr] at h3
      exact h3
  rw [lintegral_zero] at hlim
  have h4 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0).comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by positivity)] at h4

/-- The `L²` derivative of the dilated test at `τ = 0`. -/
theorem hasDerivAt_testDilation_zero {φ : Space → Space} (hφ : IsVectorTest φ) :
    HasDerivAt (testDilation φ) ((1 / 2 : ℝ) • toL2 (radialDeriv φ)) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hm0 : MemLp φ 2 volume := isVectorTest_memLp hφ
  have hmr : MemLp (radialDeriv φ) 2 volume := isVectorTest_memLp (isVectorTest_radialDeriv hφ)
  have hmd : ∀ r : ℝ, MemLp (fun y => φ (Real.exp (r / 2) • y)) 2 volume := fun r =>
    SpatialScaling.memLp_comp_dilation hm0 (Real.exp_pos _).ne'
  have hlim := tendsto_testDilation_slope hφ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ r : ℝ, ‖r⁻¹ • (testDilation φ (0 + r) - testDilation φ 0) -
      (1 / 2 : ℝ) • toL2 (radialDeriv φ)‖ =
      (eLpNorm (fun y => r⁻¹ • (φ (Real.exp (r / 2) • y) - φ y) -
        (1 / 2 : ℝ) • fderiv ℝ φ y y) 2 volume).toReal := by
    intro r
    have hz : testDilation φ 0 = toL2 φ := by
      unfold testDilation
      congr 1
      funext y
      simp
    have hm : MemLp (fun y => r⁻¹ • (φ (Real.exp (r / 2) • y) - φ y) -
        (1 / 2 : ℝ) • fderiv ℝ φ y y) 2 volume :=
      (((hmd r).sub hm0).const_smul r⁻¹).sub (hmr.const_smul (1 / 2 : ℝ))
    have he : r⁻¹ • (testDilation φ (0 + r) - testDilation φ 0) -
        (1 / 2 : ℝ) • toL2 (radialDeriv φ) =
        toL2 (fun y => r⁻¹ • (φ (Real.exp (r / 2) • y) - φ y) -
          (1 / 2 : ℝ) • fderiv ℝ φ y y) := by
      rw [hz, zero_add, testDilation]
      have e1 : (fun y => r⁻¹ • (φ (Real.exp (r / 2) • y) - φ y) -
          (1 / 2 : ℝ) • fderiv ℝ φ y y) =
          r⁻¹ • ((fun y => φ (Real.exp (r / 2) • y)) - φ) +
            (-(1 / 2 : ℝ)) • radialDeriv φ := by
        funext y
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, radialDeriv,
          neg_smul, sub_eq_add_neg]
      rw [e1, toL2_add' (((hmd r).sub hm0).const_smul _) (hmr.const_smul _),
        toL2_smul' _ ((hmd r).sub hm0), toL2_smul' _ hmr]
      rw [show (fun y => φ (Real.exp (r / 2) • y)) - φ =
          (fun y => φ (Real.exp (r / 2) • y)) + (-1 : ℝ) • φ by
            funext y; simp [sub_eq_add_neg]]
      rw [toL2_add' (hmd r) (hm0.const_smul _), toL2_smul' _ hm0]
      simp only [neg_smul, one_smul, smul_add, smul_neg, sub_eq_add_neg]
    rw [he, toL2_of_memLp hm, Lp.norm_toLp]
  simp_rw [heq]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  simpa [Function.comp_def] using this

/-- The `L²` derivative of the dilated test at every `τ`:
`∂_τ φ(e^{τ/2}·) = ½ (y·∇)(φ(e^{τ/2}·))`. -/
theorem hasDerivAt_testDilation {φ : Space → Space} (hφ : IsVectorTest φ) (τ : ℝ) :
    HasDerivAt (testDilation φ)
      ((1 / 2 : ℝ) • toL2 (radialDeriv (fun y => φ (Real.exp (τ / 2) • y)))) τ := by
  have hφτ := isVectorTest_comp_smul hφ (Real.exp_pos (τ / 2)).ne'
  have h0 := hasDerivAt_testDilation_zero hφτ
  have hshift : (fun x : ℝ => testDilation (fun y => φ (Real.exp (τ / 2) • y)) (x - τ)) =
      testDilation φ := by
    funext x
    unfold testDilation
    congr 1
    funext y
    dsimp only
    rw [smul_smul, ← Real.exp_add]
    ring_nf
  rw [← hshift]
  have h0' : HasDerivAt (testDilation (fun y => φ (Real.exp (τ / 2) • y)))
      ((1 / 2 : ℝ) • toL2 (radialDeriv (fun y => φ (Real.exp (τ / 2) • y)))) (τ - τ) := by
    rw [sub_self]
    exact h0
  have := h0'.scomp τ (h := fun x : ℝ => x - τ) ((hasDerivAt_id' τ).sub_const τ)
  simpa [Function.comp_def] using this

/-! ## A product rule with one weakly differentiable factor -/

/-- If `a` is continuous at `t`, `b` is differentiable at `t`, and `s ↦ ⟨a(s), b(t)⟩` has
derivative `A` at `t`, then `s ↦ ⟨a(s), b(s)⟩` has derivative `A + ⟨a(t), b'(t)⟩`. -/
theorem hasDerivAt_inner_of_weak {a b : ℝ → L2Space} {t A : ℝ} {b' : L2Space}
    (ha : ContinuousAt a t) (hb : HasDerivAt b b' t)
    (hA : HasDerivAt (fun s => inner ℝ (a s) (b t)) A t) :
    HasDerivAt (fun s => inner ℝ (a s) (b s)) (A + inner ℝ (a t) b') t := by
  set q := dslope b t
  have hq : ContinuousAt q t := continuousAt_dslope_same.mpr hb.differentiableAt
  have hqt : q t = b' := by
    simp only [q, dslope_same, hb.deriv]
  set k : ℝ → ℝ := fun s => inner ℝ (a s) (q s)
  have hk : ContinuousAt k t := ha.inner hq
  have hkd : HasDerivAt (fun s => (s - t) * k s) (k t) t := by
    rw [hasDerivAt_iff_tendsto_slope]
    have h1 : Tendsto k (𝓝[≠] t) (𝓝 (k t)) := hk.tendsto.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s - t ≠ 0 := sub_ne_zero.mpr hs
    simp only [slope_def_field, sub_self, zero_mul, sub_zero]
    field_simp
  have hsum := hA.add hkd
  have hfun : (fun s => inner ℝ (a s) (b s)) =
      fun s => inner ℝ (a s) (b t) + (s - t) * k s := by
    funext s
    have hds := sub_smul_dslope b t s
    simp only [k, q]
    rw [← real_inner_smul_right, hds, inner_sub_right]
    ring
  rw [hfun]
  have hkt : k t = inner ℝ (a t) b' := by simp only [k, hqt]
  rw [← hkt]
  exact hsum

/-! ## From weak to strong derivatives -/

/-- A path in `L²` whose pairings with all vector tests have the pairings of a continuous `L²`
path as derivatives, on an open interval, is strongly differentiable there. -/
theorem hasDerivAt_of_weak {ρ G : ℝ → L2Space} {a b : ℝ} (hG : ContinuousOn G (Ioo a b))
    (hw : ∀ φ, IsVectorTest φ → ∀ t ∈ Ioo a b,
      HasDerivAt (fun s => inner ℝ (ρ s) (toL2 φ)) (inner ℝ (G t) (toL2 φ)) t) :
    ∀ t ∈ Ioo a b, HasDerivAt ρ (G t) t := by
  intro t ht
  have hrep : ∀ s ∈ Ioo a b, ρ s = ρ t + ∫ r in t..s, G r := by
    intro s hs
    have hsub : uIcc t s ⊆ Ioo a b := by
      intro x hx
      exact ⟨by
        rcases (Set.mem_uIcc.mp hx) with h | h
        · exact lt_of_lt_of_le ht.1 h.1
        · exact lt_of_lt_of_le hs.1 h.1, by
        rcases (Set.mem_uIcc.mp hx) with h | h
        · exact lt_of_le_of_lt h.2 hs.2
        · exact lt_of_le_of_lt h.2 ht.2⟩
    have hGi : IntervalIntegrable G volume t s :=
      (hG.mono hsub).intervalIntegrable
    have : ρ s - ρ t - ∫ r in t..s, G r = 0 := by
      apply eq_zero_of_forall_vectorTest
      intro φ hφ
      have hcont : ContinuousOn (fun r => inner ℝ (G r) (toL2 φ)) (uIcc t s) :=
        (hG.mono hsub).inner continuousOn_const
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun r => inner ℝ (ρ r) (toL2 φ)) (f' := fun r => inner ℝ (G r) (toL2 φ))
        (fun x hx => hw φ hφ x (hsub hx)) hcont.intervalIntegrable
      have hcomm : (∫ r in t..s, inner ℝ (G r) (toL2 φ)) =
          inner ℝ (∫ r in t..s, G r) (toL2 φ) := by
        have h1 := ((innerSL ℝ (toL2 φ)).intervalIntegral_comp_comm hGi)
        simp only [innerSL_apply_apply] at h1
        calc (∫ r in t..s, inner ℝ (G r) (toL2 φ)) = ∫ r in t..s, inner ℝ (toL2 φ) (G r) := by
              congr 1
              funext r
              exact real_inner_comm _ _
          _ = inner ℝ (toL2 φ) (∫ r in t..s, G r) := h1
          _ = _ := real_inner_comm _ _
      rw [inner_sub_left, inner_sub_left, ← hcomm, hftc]
      ring
    rw [sub_sub, sub_eq_zero] at this
    exact this
  have hev : (fun s => ρ t + ∫ r in t..s, G r) =ᶠ[𝓝 t] ρ := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (hrep s hs).symm
  have hGi : IntervalIntegrable G volume t t := IntervalIntegrable.refl
  have hmeas : StronglyMeasurableAtFilter G (𝓝 t) :=
    hG.stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hd := intervalIntegral.integral_hasDerivAt_right hGi hmeas
    (hG.continuousAt (Ioo_mem_nhds ht.1 ht.2))
  exact (hd.const_add (ρ t)).congr_of_eventuallyEq hev.symm

/-! ## The similarity weak equation and its physical form -/

/-- The remainder equation `∂_τR = hΔR + ½R + ½y·∇R + F` (lines 517–522) in weak form at
every phase `τ ∈ S`: for every vector test `φ`,
`d/dτ ⟨R(τ), φ⟩ = ⟨hΔR(τ) + F(τ), φ⟩ - ⟨R(τ), φ⟩ - ½⟨R(τ), (y·∇)φ⟩`. -/
def IsSimilarityWeakSolution (h : ℝ) (S : Set ℝ) (R : ℝ → H2) (F : ℝ → L2Space) : Prop :=
  ∀ φ : Space → Space, IsVectorTest φ → ∀ τ ∈ S,
    HasDerivAt (fun σ => inner ℝ (R σ).value (toL2 φ))
      (inner ℝ (h • H2.laplace (R τ) + F τ) (toL2 φ) - inner ℝ (R τ).value (toL2 φ) -
        (1 / 2 : ℝ) * inner ℝ (R τ).value (toL2 (radialDeriv φ))) τ

theorem IsSimilarityWeakSolution.add {h : ℝ} {S : Set ℝ} {R₁ R₂ : ℝ → H2}
    {F₁ F₂ : ℝ → L2Space} (h₁ : IsSimilarityWeakSolution h S R₁ F₁)
    (h₂ : IsSimilarityWeakSolution h S R₂ F₂) :
    IsSimilarityWeakSolution h S (fun τ => R₁ τ + R₂ τ) (fun τ => F₁ τ + F₂ τ) := by
  intro φ hφ τ hτ
  have h12 := (h₁ φ hφ τ hτ).add (h₂ φ hφ τ hτ)
  have hv : ∀ G₁ G₂ : H2, (G₁ + G₂).value = G₁.value + G₂.value := fun _ _ => rfl
  have hl : ∀ G₁ G₂ : H2, H2.laplace (G₁ + G₂) = H2.laplace G₁ + H2.laplace G₂ :=
    fun G₁ G₂ => map_add H2.laplaceCLM G₁ G₂
  refine (h12.congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)).congr_deriv ?_
  · dsimp only
    rw [hv, inner_add_left]
    rfl
  · dsimp only
    rw [hv, hl]
    simp only [smul_add, inner_add_left]
    ring

theorem IsSimilarityWeakSolution.smul {h : ℝ} {S : Set ℝ} {R : ℝ → H2} {F : ℝ → L2Space}
    (hR : IsSimilarityWeakSolution h S R F) (c : ℝ) :
    IsSimilarityWeakSolution h S (fun τ => c • R τ) (fun τ => c • F τ) := by
  intro φ hφ τ hτ
  have hc := (hR φ hφ τ hτ).const_mul c
  have hv : ∀ G : H2, (c • G).value = c • G.value := fun _ => rfl
  have hl : ∀ G : H2, H2.laplace (c • G) = c • H2.laplace G :=
    fun G => map_smul H2.laplaceCLM c G
  refine (hc.congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)).congr_deriv ?_
  · dsimp only
    rw [hv, real_inner_smul_left]
  · dsimp only
    rw [hv, hl]
    simp only [smul_smul, inner_add_left, real_inner_smul_left]
    ring

theorem IsSimilarityWeakSolution.mono {h : ℝ} {S S' : Set ℝ} {R : ℝ → H2} {F : ℝ → L2Space}
    (hR : IsSimilarityWeakSolution h S R F) (hS : S' ⊆ S) :
    IsSimilarityWeakSolution h S' R F :=
  fun φ hφ τ hτ => hR φ hφ τ (hS hτ)

theorem IsSimilarityWeakSolution.congr_forcing {h : ℝ} {S : Set ℝ} {R : ℝ → H2}
    {F F' : ℝ → L2Space} (hR : IsSimilarityWeakSolution h S R F) (hF : ∀ τ ∈ S, F τ = F' τ) :
    IsSimilarityWeakSolution h S R F' := by
  intro φ hφ τ hτ
  rw [← hF τ hτ]
  exact hR φ hφ τ hτ

/-- The physical remainder `ρ(t) = D(-log t) R(log t) = t^{-1/2} R(·/√t, log t)` in `H²`. -/
def physicalOf (R : ℝ → H2) (t : ℝ) : H2 := dilH2 (-Real.log t) (R (Real.log t))

/-- The physical forcing `N(t) = t⁻¹ D(-log t) F(log t) = t^{-3/2} F(·/√t, log t)`. -/
def physicalForcing (F : ℝ → L2Space) (t : ℝ) : L2Space :=
  t⁻¹ • dil (-Real.log t) (F (Real.log t))

/-- The change of variables: a similarity weak solution on `(-∞, τ₀)` gives the physical weak
derivative `d/dt ⟨ρ(t), φ⟩ = ⟨hΔρ(t) + N(t), φ⟩` on `(0, e^{τ₀})`. -/
theorem physical_weak_of_similarity {h τ₀ : ℝ} {R : ℝ → H2} {F : ℝ → L2Space}
    (hR : ContinuousOn (fun τ => (R τ).value) (Iio τ₀))
    (hw : IsSimilarityWeakSolution h (Iio τ₀) R F)
    {φ : Space → Space} (hφ : IsVectorTest φ) {t : ℝ} (ht : 0 < t) (htT : t < Real.exp τ₀) :
    HasDerivAt (fun s => inner ℝ (physicalOf R s).value (toL2 φ))
      (inner ℝ (h • H2.laplace (physicalOf R t) + physicalForcing F t) (toL2 φ)) t := by
  set τ := Real.log t with hτdef
  have hτ : τ < τ₀ := by
    have := Real.log_lt_log ht htT
    rwa [Real.log_exp] at this
  have hτt : Real.exp τ = t := Real.exp_log ht
  have hφτ : IsVectorTest (fun y => φ (Real.exp (τ / 2) • y)) :=
    isVectorTest_comp_smul hφ (Real.exp_pos _).ne'
  -- the pairing in similarity variables
  set f : ℝ → ℝ := fun σ => Real.exp σ * inner ℝ (R σ).value (testDilation φ σ) with hfdef
  have hpair : ∀ s : ℝ, 0 < s →
      inner ℝ (physicalOf R s).value (toL2 φ) = f (Real.log s) := by
    intro s hs
    simp only [physicalOf, dilH2_value, hfdef, testDilation]
    rw [dil_neg_inner_toL2 _ _ (isVectorTest_memLp hφ)]
  -- the derivative of `f` at `τ`
  have hpr : HasDerivAt (fun σ => inner ℝ (R σ).value (testDilation φ σ))
      ((inner ℝ (h • H2.laplace (R τ) + F τ) (toL2 (fun y => φ (Real.exp (τ / 2) • y))) -
        inner ℝ (R τ).value (toL2 (fun y => φ (Real.exp (τ / 2) • y))) -
        (1 / 2 : ℝ) * inner ℝ (R τ).value
          (toL2 (radialDeriv (fun y => φ (Real.exp (τ / 2) • y))))) +
        inner ℝ (R τ).value ((1 / 2 : ℝ) •
          toL2 (radialDeriv (fun y => φ (Real.exp (τ / 2) • y))))) τ := by
    apply hasDerivAt_inner_of_weak
    · exact hR.continuousAt (Iio_mem_nhds hτ)
    · exact hasDerivAt_testDilation hφ τ
    · exact hw _ hφτ τ hτ
  have hf : HasDerivAt f (Real.exp τ * inner ℝ (h • H2.laplace (R τ) + F τ)
      (toL2 (fun y => φ (Real.exp (τ / 2) • y)))) τ := by
    have h2 := (Real.hasDerivAt_exp τ).mul hpr
    refine h2.congr_deriv ?_
    rw [real_inner_smul_right]
    simp only [testDilation]
    ring
  have hcomp := hf.comp t (Real.hasDerivAt_log ht.ne')
  have hev : (f ∘ Real.log) =ᶠ[𝓝 t]
      fun s => inner ℝ (physicalOf R s).value (toL2 φ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hpair s hs).symm
  refine (hcomp.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  -- identify the derivative
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    physicalForcing, physicalOf, laplace_dilH2, real_inner_smul_left, real_inner_smul_left,
    dil_neg_inner_toL2 _ _ (isVectorTest_memLp hφ),
    dil_neg_inner_toL2 _ _ (isVectorTest_memLp hφ)]
  simp only [← hτdef, hτt, Real.exp_neg]
  field_simp

/-- The physical strong equation from the similarity weak equation, given continuity of the
physical right-hand side. -/
theorem physical_hasDerivAt_of_similarity {h τ₀ : ℝ} {R : ℝ → H2} {F : ℝ → L2Space}
    (hR : ContinuousOn (fun τ => (R τ).value) (Iio τ₀))
    (hw : IsSimilarityWeakSolution h (Iio τ₀) R F)
    (hG : ContinuousOn (fun t => h • H2.laplace (physicalOf R t) + physicalForcing F t)
      (Ioo 0 (Real.exp τ₀))) :
    ∀ t ∈ Ioo 0 (Real.exp τ₀), HasDerivAt (fun s => (physicalOf R s).value)
      (h • H2.laplace (physicalOf R t) + physicalForcing F t) t :=
  hasDerivAt_of_weak hG (fun φ hφ t ht => physical_weak_of_similarity hR hw hφ ht.1 ht.2)

end UnforcedLeray.Blueprint.L13
