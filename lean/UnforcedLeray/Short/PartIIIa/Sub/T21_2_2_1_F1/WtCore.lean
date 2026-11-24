import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.ChangeVar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Equiv

/-!
# Part III-a, `PartIII-a:T21/2/2/1/3/org`: the fixed-cell energy along an `X_{-m,c}`-continuous path

Source of record: `the November 2 reference manuscript` (SP), lines 3036-3037, 3044
("the equivalent periodic weight"), 3060-3071.

`wtF0(a, x) = p_{c/√a}⁻¹(x/√a)` is, for `a` in a compact subset of `[1, ∞)`, uniformly equivalent on
the cell to the density `⟨x⟩^{-2m}` of `X_{-m,c}`, and is continuous in `a`. So if `f(r) → f(r₀)` in
`X_{-m,c}`, then `∫_{C_c} wtF0(a(r), x) |f(r, x)|² dx → ∫_{C_c} wtF0(a(r₀), x) |f(r₀, x)|² dx`
(`wtCoreCont`), for every real `m`. This one statement gives the continuity of `E_0` and of `E_1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff NNReal

namespace UnforcedLeray.Short.IIIa

/-- **Continuity of the fixed-cell energy along an `X_{-m,c}`-continuous path** (SP 3036-3037, 3044,
3060-3071). -/
def WtCoreCont : Prop :=
  ∀ (ν c m : ℝ) (I : Set ℝ) (f : ℝ → ℝ × ℝ → ℂ), 0 < ν → 0 < c → (∀ r ∈ I, 0 ≤ r) →
    (∀ r ∈ I, MemLp (f r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ I, Tendsto (fun r' => xNorm c (-m) (f r' - f r)) (𝓝[I] r) (𝓝 0)) →
    ContinuousOn (fun r => ∫ x in B0579.cell c, wtF0 c m (clockA ν r) x * ‖f r x‖ ^ 2) I

/-- The base of `wtF0`. -/
def wtBase (c a : ℝ) (x : ℝ × ℝ) : ℝ :=
  1 + x.2 ^ 2 / a + (c / Real.pi) ^ 2 * Real.sin (Real.pi * x.1 / c) ^ 2 / a

theorem wtBase_pos (c : ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) : 0 < wtBase c a x := by
  unfold wtBase
  positivity

theorem wtF0_eq_base (c m a : ℝ) (x : ℝ × ℝ) : wtF0 c m a x = wtBase c a x ^ (-m) := rfl

/-- The ratio of `wtF0` to the density `⟨x⟩^{-2m}` of `X_{-m,c}`. -/
def wtRatio (c m a : ℝ) (x : ℝ × ℝ) : ℝ := wtF0 c m a x * B0579.jb x ^ m

theorem wtRatio_nonneg (c m : ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) : 0 ≤ wtRatio c m a x :=
  mul_nonneg (Real.rpow_nonneg (wtBase_pos c ha x).le _) (Real.rpow_nonneg (B0579.jb_pos x).le _)

/-- The bound of the ratio: `(b/j)^{-m} ≤ 1 + κ^{-m}`, `κ = 4/(π²A)`, since `κ j ≤ b ≤ j`. -/
theorem wtRatio_le (c m : ℝ) (hc : 0 < c) {a A : ℝ} (h1 : 1 ≤ a) (hA : a ≤ A) {x : ℝ × ℝ}
    (hx : x ∈ B0579.cell c) :
    wtRatio c m a x ≤ 1 + (4 / (Real.pi ^ 2 * A)) ^ (-m) := by
  have ha : 0 < a := lt_of_lt_of_le one_pos h1
  have hA0 : 0 < A := lt_of_lt_of_le ha hA
  have hA1 : 1 ≤ A := h1.trans hA
  have hpi : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hκ : 0 < 4 / (Real.pi ^ 2 * A) := by positivity
  have hκ1 : 4 / (Real.pi ^ 2 * A) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hb : 0 < wtBase c a x := wtBase_pos c ha x
  have hj : 0 < B0579.jb x := B0579.jb_pos x
  have hx1 : |x.1| ≤ c / 2 := by
    have h : x.1 ∈ Ico (-(c / 2)) (c / 2) := hx.1
    exact abs_le.mpr ⟨h.1, h.2.le⟩
  have hsL := E0.adjWeight_sinsq_aux c x.1 hc hx1
  have hsU := E0.adjWeight_sinsq_le c x.1 hc
  set S := (c / Real.pi) ^ 2 * Real.sin (Real.pi * x.1 / c) ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hbU : wtBase c a x ≤ B0579.jb x := by
    have h2 : x.2 ^ 2 / a ≤ x.2 ^ 2 := div_le_self (sq_nonneg _) h1
    have h3 : S / a ≤ S := div_le_self hS0 h1
    unfold wtBase B0579.jb
    rw [← hS]
    linarith
  have hbL : 4 / (Real.pi ^ 2 * A) * B0579.jb x ≤ wtBase c a x := by
    have h2 : x.2 ^ 2 / A ≤ x.2 ^ 2 / a := div_le_div_of_nonneg_left (sq_nonneg _) ha hA
    have h3 : S / A ≤ S / a := div_le_div_of_nonneg_left hS0 ha hA
    have h4 : 4 / (Real.pi ^ 2 * A) * x.1 ^ 2 ≤ S / A := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hA0]
      have : 4 * x.1 ^ 2 ≤ Real.pi ^ 2 * S := by
        have h := mul_le_mul_of_nonneg_left hsL (sq_nonneg Real.pi)
        have e : Real.pi ^ 2 * (4 / Real.pi ^ 2 * x.1 ^ 2) = 4 * x.1 ^ 2 := by
          field_simp
        rwa [e] at h
      have hAp : 0 ≤ A := hA0.le
      calc 4 * x.1 ^ 2 * A ≤ (Real.pi ^ 2 * S) * A := mul_le_mul_of_nonneg_right this hAp
        _ = S * (Real.pi ^ 2 * A) := by ring
    have h5 : 4 / (Real.pi ^ 2 * A) ≤ 1 / A := by
      rw [div_le_div_iff₀ (by positivity) hA0]
      nlinarith
    have h6 : 4 / (Real.pi ^ 2 * A) * x.2 ^ 2 ≤ x.2 ^ 2 / A := by
      rw [div_eq_mul_one_div (x.2 ^ 2) A, mul_comm]
      exact mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
    unfold wtBase B0579.jb
    rw [← hS]
    nlinarith
  have hrat : wtRatio c m a x = (wtBase c a x / B0579.jb x) ^ (-m) := by
    unfold wtRatio
    rw [wtF0_eq_base, Real.div_rpow hb.le hj.le, Real.rpow_neg hj.le m, div_inv_eq_mul]
  have hq0 : 0 < wtBase c a x / B0579.jb x := div_pos hb hj
  have hq1 : wtBase c a x / B0579.jb x ≤ 1 := (div_le_one hj).mpr hbU
  have hq2 : 4 / (Real.pi ^ 2 * A) ≤ wtBase c a x / B0579.jb x := (le_div_iff₀ hj).mpr hbL
  rw [hrat]
  rcases le_total 0 m with hm | hm
  · have h := Real.rpow_le_rpow_of_nonpos hκ hq2 (neg_nonpos.mpr hm)
    linarith
  · have h := Real.rpow_le_rpow hq0.le hq1 (neg_nonneg.mpr hm)
    rw [Real.one_rpow] at h
    have : 0 ≤ (4 / (Real.pi ^ 2 * A)) ^ (-m) := Real.rpow_nonneg hκ.le _
    linarith

/-- `wtF0` is continuous in the plane variable. -/
theorem continuous_wtF0 (c m : ℝ) {a : ℝ} (ha : 0 < a) : Continuous (wtF0 c m a) := by
  have hb : Continuous (wtBase c a) := by
    unfold wtBase
    have h1 : Continuous fun x : ℝ × ℝ => Real.sin (Real.pi * x.1 / c) :=
      Real.continuous_sin.comp ((continuous_const.mul continuous_fst).div_const c)
    exact ((continuous_const.add ((continuous_snd.pow 2).div_const a)).add
      ((continuous_const.mul (h1.pow 2)).div_const a))
  exact hb.rpow_const fun x => Or.inl (wtBase_pos c ha x).ne'

theorem continuous_wtRatio (c m : ℝ) {a : ℝ} (ha : 0 < a) : Continuous (wtRatio c m a) :=
  (continuous_wtF0 c m ha).mul (B0579.continuous_jb_rpow m)

/-- `wtF0` is continuous in `a > 0`, at a fixed point. -/
theorem continuousAt_wtRatio (c m : ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) :
    ContinuousAt (fun a' => wtRatio c m a' x) a := by
  have hb : ContinuousAt (fun a' => wtBase c a' x) a := by
    unfold wtBase
    exact (continuousAt_const.add (continuousAt_const.div continuousAt_id ha.ne')).add
      (continuousAt_const.div continuousAt_id ha.ne')
  have h : ContinuousAt (fun a' => wtBase c a' x ^ (-m)) a :=
    hb.rpow_const (Or.inl (wtBase_pos c ha x).ne')
  exact h.mul continuousAt_const

/-- The fixed-cell integral against the measure of `X_{-m,c}`. -/
theorem integral_wtF0_eq (c m a : ℝ) (u : ℝ × ℝ → ℝ) :
    ∫ x in B0579.cell c, wtF0 c m a x * u x =
      ∫ x, wtRatio c m a x * u x ∂(B0579.cellMeasure c (-m)) := by
  unfold B0579.cellMeasure
  rw [integral_withDensity_eq_integral_smul (B0579.measurable_density (-m))]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hj : 0 < B0579.jb x := B0579.jb_pos x
  simp only [NNReal.smul_def, B0579.coe_density, smul_eq_mul, wtRatio]
  have e : B0579.jb x ^ (-m) * B0579.jb x ^ m = 1 := by
    rw [← Real.rpow_add hj]
    simp
  calc wtF0 c m a x * u x
      = (B0579.jb x ^ (-m) * B0579.jb x ^ m) * (wtF0 c m a x * u x) := by rw [e, one_mul]
    _ = B0579.jb x ^ (-m) * (wtF0 c m a x * B0579.jb x ^ m * u x) := by ring

/-- `‖h‖₂² = ∫ |h|²`. -/
theorem sq_toReal_eLpNorm {μ : Measure (ℝ × ℝ)} {h : ℝ × ℝ → ℂ} (hh : MemLp h 2 μ) :
    (eLpNorm h 2 μ).toReal ^ 2 = ∫ x, ‖h x‖ ^ 2 ∂μ := by
  have h0 : 0 ≤ ∫ x, ‖h x‖ ^ 2 ∂μ := integral_nonneg fun _ => by positivity
  have h1 := hh.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
  have e : ((2 : ℝ≥0∞).toReal) = 2 := by simp
  simp only [e, Real.rpow_two] at h1
  rw [h1, ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

/-- `∫ |h||g| ≤ ‖h‖₂‖g‖₂`. -/
theorem integral_norm_mul_norm_le {μ : Measure (ℝ × ℝ)} {h g : ℝ × ℝ → ℂ} (hh : MemLp h 2 μ)
    (hg : MemLp g 2 μ) :
    ∫ x, ‖h x‖ * ‖g x‖ ∂μ ≤ (eLpNorm h 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have e2 : ENNReal.ofReal 2 = 2 := by simp
  have hh' : MemLp h (ENNReal.ofReal 2) μ := by rwa [e2]
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by rwa [e2]
  have h1 := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hh' hg'
  have e : ∀ f : ℝ × ℝ → ℂ, MemLp f 2 μ →
      (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = (eLpNorm f 2 μ).toReal := by
    intro f hf
    have h0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun _ => by positivity
    simp only [Real.rpow_two]
    rw [← Real.sqrt_eq_rpow, ← sq_toReal_eLpNorm hf, Real.sqrt_sq ENNReal.toReal_nonneg]
  rwa [e h hh, e g hg] at h1

/-- The `L¹` estimate of the difference of two squares. -/
theorem integral_abs_sq_sub_le {μ : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → ℂ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) :
    ∫ x, |‖f x‖ ^ 2 - ‖g x‖ ^ 2| ∂μ ≤
      (eLpNorm (f - g) 2 μ).toReal ^ 2 +
        2 * ((eLpNorm (f - g) 2 μ).toReal * (eLpNorm g 2 μ).toReal) := by
  have hh : MemLp (f - g) 2 μ := hf.sub hg
  have i1 : Integrable (fun x => ‖(f - g) x‖ ^ 2) μ := hh.integrable_norm_pow two_ne_zero
  have i2 : Integrable (fun x => ‖(f - g) x‖ * ‖g x‖) μ := hh.norm.integrable_mul hg.norm
  have i3 : Integrable (fun x => ‖f x‖ ^ 2) μ := hf.integrable_norm_pow two_ne_zero
  have i4 : Integrable (fun x => ‖g x‖ ^ 2) μ := hg.integrable_norm_pow two_ne_zero
  have hpt : ∀ x, |‖f x‖ ^ 2 - ‖g x‖ ^ 2| ≤ ‖(f - g) x‖ ^ 2 + 2 * (‖(f - g) x‖ * ‖g x‖) := by
    intro x
    have h1 : ‖f x‖ ≤ ‖(f - g) x‖ + ‖g x‖ := by
      have := norm_add_le ((f - g) x) (g x)
      simpa using this
    have h2 : ‖g x‖ ≤ ‖(f - g) x‖ + ‖f x‖ := by
      have := norm_sub_le (f x) ((f - g) x)
      have e : f x - (f - g) x = g x := by simp
      rw [e] at this
      linarith
    have hn1 := norm_nonneg (f x)
    have hn2 := norm_nonneg (g x)
    have hn3 := norm_nonneg ((f - g) x)
    rw [abs_le]
    constructor <;> nlinarith
  calc ∫ x, |‖f x‖ ^ 2 - ‖g x‖ ^ 2| ∂μ
      ≤ ∫ x, (‖(f - g) x‖ ^ 2 + 2 * (‖(f - g) x‖ * ‖g x‖)) ∂μ :=
        integral_mono (i3.sub i4).abs (i1.add (i2.const_mul 2)) hpt
    _ = ∫ x, ‖(f - g) x‖ ^ 2 ∂μ + 2 * ∫ x, ‖(f - g) x‖ * ‖g x‖ ∂μ := by
        rw [integral_add i1 (i2.const_mul 2), integral_const_mul]
    _ ≤ _ := by
        rw [← sq_toReal_eLpNorm hh]
        have := integral_norm_mul_norm_le hh hg
        linarith

/-- **Continuity of the fixed-cell energy** (SP 3036-3037, 3044, 3060-3071). -/
theorem wtCoreCont : WtCoreCont := by
  intro ν c m I f hν hc hI hmem hcont r₀ hr₀
  set μ := B0579.cellMeasure c (-m) with hμ
  have hr0 : 0 ≤ r₀ := hI r₀ hr₀
  have haC : Continuous (clockA ν) := by
    unfold clockA
    fun_prop
  have ha1 : ∀ r, 0 ≤ r → 1 ≤ clockA ν r := by
    intro r hr
    unfold clockA
    nlinarith [mul_nonneg hν.le hr]
  set A := clockA ν r₀ + 1 with hA
  set K := 1 + (4 / (Real.pi ^ 2 * A)) ^ (-m) with hK
  have hK0 : 0 ≤ K := by
    have hA0 : 0 < A := by
      have := ha1 r₀ hr0
      rw [hA]
      linarith
    positivity
  have hcell : ∀ᵐ x ∂μ, x ∈ B0579.cell c :=
    (B0579.cellMeasure_ac c (-m)).ae_le (ae_restrict_mem (B0579.measurableSet_cell c))
  -- eventually, `r` lies in `I` and `a(r) ≤ A`
  have hev : ∀ᶠ r in 𝓝[I] r₀, r ∈ I ∧ clockA ν r ≤ A := by
    have h1 : ∀ᶠ r in 𝓝 r₀, clockA ν r < A :=
      haC.continuousAt.eventually_lt continuousAt_const (by rw [hA]; linarith)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with r hr1 hr2 using ⟨hr1, hr2.le⟩
  have hbound : ∀ r, r ∈ I → clockA ν r ≤ A → ∀ᵐ x ∂μ, |wtRatio c m (clockA ν r) x| ≤ K := by
    intro r hr hrA
    filter_upwards [hcell] with x hx
    have ha := ha1 r (hI r hr)
    rw [abs_of_nonneg (wtRatio_nonneg c m (lt_of_lt_of_le one_pos ha) x)]
    exact wtRatio_le c m hc ha hrA hx
  -- the integrals against `μ`
  have hG : ∀ r, ∫ x in B0579.cell c, wtF0 c m (clockA ν r) x * ‖f r x‖ ^ 2 =
      ∫ x, wtRatio c m (clockA ν r) x * ‖f r x‖ ^ 2 ∂μ := fun r => integral_wtF0_eq c m _ _
  simp only [ContinuousWithinAt, hG]
  have hu0 : Integrable (fun x => ‖f r₀ x‖ ^ 2) μ := (hmem r₀ hr₀).integrable_norm_pow two_ne_zero
  have hmeasW : ∀ r, r ∈ I → AEStronglyMeasurable (wtRatio c m (clockA ν r)) μ := fun r hr =>
    (continuous_wtRatio c m (lt_of_lt_of_le one_pos (ha1 r (hI r hr)))).aestronglyMeasurable
  have hint : ∀ r, r ∈ I → clockA ν r ≤ A → ∀ u : ℝ × ℝ → ℝ, Integrable u μ →
      Integrable (fun x => wtRatio c m (clockA ν r) x * u x) μ := by
    intro r hr hrA u hu
    exact hu.bdd_mul (hmeasW r hr) ((hbound r hr hrA).mono fun x hx => by simpa using hx)
  -- the second term, by dominated convergence
  have hT2 : Tendsto (fun r => ∫ x, wtRatio c m (clockA ν r) x * ‖f r₀ x‖ ^ 2 ∂μ) (𝓝[I] r₀)
      (𝓝 (∫ x, wtRatio c m (clockA ν r₀) x * ‖f r₀ x‖ ^ 2 ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => K * ‖f r₀ x‖ ^ 2) ?_ ?_
      (hu0.const_mul K) ?_
    · filter_upwards [hev] with r hr
      exact (hint r hr.1 hr.2 _ hu0).aestronglyMeasurable
    · filter_upwards [hev] with r hr
      filter_upwards [hbound r hr.1 hr.2] with x hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right hx (by positivity)
    · refine Eventually.of_forall fun x => ?_
      have hc1 : ContinuousAt (fun a' => wtRatio c m a' x) (clockA ν r₀) :=
        continuousAt_wtRatio c m (lt_of_lt_of_le one_pos (ha1 r₀ hr0)) x
      have hc2 : Tendsto (fun r => wtRatio c m (clockA ν r) x) (𝓝[I] r₀)
          (𝓝 (wtRatio c m (clockA ν r₀) x)) :=
        hc1.tendsto.comp (haC.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      exact hc2.mul_const _
  -- the first term, by the `L²` convergence
  have hn : Tendsto (fun r => (eLpNorm (f r - f r₀) 2 μ).toReal) (𝓝[I] r₀) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont r₀ hr₀)
    simpa [xNorm, hμ, Function.comp_def] using h
  have hbd : Tendsto (fun r => K * ((eLpNorm (f r - f r₀) 2 μ).toReal ^ 2 +
      2 * ((eLpNorm (f r - f r₀) 2 μ).toReal * (eLpNorm (f r₀) 2 μ).toReal))) (𝓝[I] r₀) (𝓝 0) := by
    have h : Tendsto (fun r => K * ((eLpNorm (f r - f r₀) 2 μ).toReal ^ 2 +
        2 * ((eLpNorm (f r - f r₀) 2 μ).toReal * (eLpNorm (f r₀) 2 μ).toReal))) (𝓝[I] r₀)
        (𝓝 (K * ((0 : ℝ) ^ 2 + 2 * (0 * (eLpNorm (f r₀) 2 μ).toReal)))) :=
      ((hn.pow 2).add ((hn.mul_const _).const_mul 2)).const_mul K
    simpa using h
  have hT1 : Tendsto (fun r => ∫ x, wtRatio c m (clockA ν r) x * ‖f r x‖ ^ 2 ∂μ -
      ∫ x, wtRatio c m (clockA ν r) x * ‖f r₀ x‖ ^ 2 ∂μ) (𝓝[I] r₀) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [hev] with r hr
    have hf := hmem r hr.1
    have hf0 := hmem r₀ hr₀
    have hur : Integrable (fun x => ‖f r x‖ ^ 2) μ := hf.integrable_norm_pow two_ne_zero
    have hsub : ∫ x, wtRatio c m (clockA ν r) x * ‖f r x‖ ^ 2 ∂μ -
        ∫ x, wtRatio c m (clockA ν r) x * ‖f r₀ x‖ ^ 2 ∂μ =
        ∫ x, wtRatio c m (clockA ν r) x * (‖f r x‖ ^ 2 - ‖f r₀ x‖ ^ 2) ∂μ := by
      rw [← integral_sub (hint r hr.1 hr.2 _ hur) (hint r hr.1 hr.2 _ hu0)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      ring
    rw [hsub]
    have habs : Integrable (fun x => |‖f r x‖ ^ 2 - ‖f r₀ x‖ ^ 2|) μ := (hur.sub hu0).abs
    calc ‖∫ x, wtRatio c m (clockA ν r) x * (‖f r x‖ ^ 2 - ‖f r₀ x‖ ^ 2) ∂μ‖
        ≤ ∫ x, ‖wtRatio c m (clockA ν r) x * (‖f r x‖ ^ 2 - ‖f r₀ x‖ ^ 2)‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, K * |‖f r x‖ ^ 2 - ‖f r₀ x‖ ^ 2| ∂μ := by
          refine integral_mono_ae (hint r hr.1 hr.2 _ (hur.sub hu0)).norm (habs.const_mul K) ?_
          filter_upwards [hbound r hr.1 hr.2] with x hx
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
      _ = K * ∫ x, |‖f r x‖ ^ 2 - ‖f r₀ x‖ ^ 2| ∂μ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_sq_sub_le hf hf0) hK0
  have hfinal := hT1.add hT2
  simpa using hfinal

end UnforcedLeray.Short.IIIa
