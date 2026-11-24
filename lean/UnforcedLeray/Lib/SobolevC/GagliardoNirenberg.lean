import UnforcedLeray.Lib.Sobolev
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# The mixed-exponent Gagliardo–Nirenberg inequality (block 2E, critic correction 4)


manuscript eq. (2.45), tex 5756–5762, blueprint unit B0690:
`‖∇w‖²_{Y_{2p}} ≤ C ‖w‖_∞ ‖D²w‖_{Y_p}`, "by the spatial Gagliardo–Nirenberg inequality at each
phase".  The spatial inequality is proved here, direction by direction, with the constant
`2p - 1`:
`‖∂_v w‖²_{L^{2p}} ≤ (2p - 1) ‖w‖_∞ ‖∂_v ∂_v w‖_{L^p}`, `1 ≤ p < ∞`.

## Proof
Put `a = ∂_v w`, `b = ∂_v a` and `G(t) = t |t|^{2p-2}`, which is `C¹` with
`G'(t) = (2p - 1)|t|^{2p-2}` (`hasDerivAt_oddPow`).  Integration by parts in the direction `v`
(Mathlib `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) gives
`∫ |a|^{2p} = ∫ a G(a) = -∫ w G'(a) b`, hence `∫|a|^{2p} ≤ (2p-1) M ∫ |a|^{2p-2}|b|`, and
Hölder with exponents `p/(p-1)` and `p` closes the estimate (`gn_mixed_integral`).

## Density
`gn_mixed_of_tendsto` passes the inequality to limits: `w_k ∈ C²_c` with `|w_k| ≤ M`,
`∂_v w_k → g` a.e. and `∂_v∂_v w_k → h` in `L^p` give `‖g‖²_{2p} ≤ (2p - 1) M ‖h‖_p` (Fatou).
The density argument itself (cutoffs and mollifiers of a `W^{2,p} ∩ L^∞` field) is in
`SobolevC/GNDensity.lean` (`GN.gn_mixed_weak`, `W.gn_mixed`).

## Main declarations
* `GN.oddPow`, `GN.hasDerivAt_oddPow`;
* `GN.integral_abs_rpow_dirDeriv_eq` (the integration-by-parts identity);
* `GN.gn_mixed_integral`, `GN.gn_mixed` (`C²_c` functions, real and `eLpNorm` forms);
* `GN.gn_mixed_of_tendsto` (the closure step for the density argument).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Sob

namespace GN

/-! ### The odd power `t ↦ t |t|^r` -/

/-- The odd power `t ↦ t |t|^r`. -/
def oddPow (r t : ℝ) : ℝ := t * |t| ^ r

theorem continuous_abs_rpow {r : ℝ} (hr : 0 ≤ r) : Continuous fun t : ℝ => |t| ^ r :=
  continuous_abs.rpow_const fun _ => Or.inr hr

theorem continuous_oddPow {r : ℝ} (hr : 0 ≤ r) : Continuous (oddPow r) :=
  continuous_id.mul (continuous_abs_rpow hr)

@[simp] theorem oddPow_zero (r : ℝ) : oddPow r 0 = 0 := by simp [oddPow]

/-- `t ↦ t |t|^r` is differentiable with derivative `(r + 1)|t|^r`, for `r ≥ 0`. -/
theorem hasDerivAt_oddPow {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    HasDerivAt (oddPow r) ((r + 1) * |t| ^ r) t := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [hasDerivAt_iff_tendsto_slope]
    have hc : Tendsto (fun s : ℝ => |s| ^ r) (𝓝[≠] (0 : ℝ)) (𝓝 (|(0 : ℝ)| ^ r)) :=
      ((continuous_abs_rpow hr).tendsto 0).mono_left nhdsWithin_le_nhds
    have he : (r + 1) * |(0 : ℝ)| ^ r = |(0 : ℝ)| ^ r := by
      rcases eq_or_lt_of_le hr with h | h
      · rw [← h]; simp
      · rw [abs_zero, Real.zero_rpow h.ne']; ring
    rw [he]
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 0 := hs
    rw [slope_def_field, oddPow_zero, sub_zero, sub_zero, oddPow, mul_div_cancel_left₀ _ hs']
  · have h1 : HasDerivAt (fun s : ℝ => |s| ^ r)
        ((SignType.sign t : ℝ) * r * |t| ^ (r - 1)) t :=
      (hasDerivAt_abs ht).rpow_const (Or.inl (abs_ne_zero.mpr ht))
    have h2 : HasDerivAt (fun y => y * |y| ^ r)
        (1 * |t| ^ r + t * ((SignType.sign t : ℝ) * r * |t| ^ (r - 1))) t :=
      (hasDerivAt_id' t).mul h1
    have hts : t * (SignType.sign t : ℝ) = |t| := self_mul_sign t
    have hpow : |t| * |t| ^ (r - 1) = |t| ^ r := by
      rw [Real.rpow_sub_one (abs_ne_zero.mpr ht), mul_div_cancel₀ _ (abs_ne_zero.mpr ht)]
    have he : 1 * |t| ^ r + t * ((SignType.sign t : ℝ) * r * |t| ^ (r - 1)) =
        (r + 1) * |t| ^ r := by
      calc 1 * |t| ^ r + t * ((SignType.sign t : ℝ) * r * |t| ^ (r - 1))
          = 1 * |t| ^ r + r * ((t * (SignType.sign t : ℝ)) * |t| ^ (r - 1)) := by ring
        _ = (r + 1) * |t| ^ r := by rw [hts, hpow]; ring
    exact h2.congr_deriv he

/-- `a · (a |a|^r) = |a|^{r+2}`. -/
theorem mul_oddPow (r t : ℝ) (hr : 0 ≤ r) : t * oddPow r t = |t| ^ (r + 2) := by
  rw [oddPow, Real.rpow_add' (abs_nonneg t) (by linarith)]
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  ring

/-! ### The inequality for `C²_c` functions -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The integration-by-parts identity** (tex 5756–5762, B0690): for `w ∈ C²_c`, `p ≥ 1`,
`∫ |∂_v w|^{2p} = -∫ w · (2p - 1)|∂_v w|^{2p-2} ∂_v∂_v w`. -/
theorem integral_abs_rpow_dirDeriv_eq {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hs : HasCompactSupport w) (v : E) {p : ℝ} (hp : 1 ≤ p) :
    ∫ x, |fderiv ℝ w x v| ^ (2 * p) ∂μ =
      -∫ x, w x * ((2 * p - 1) * |fderiv ℝ w x v| ^ (2 * p - 2) *
        fderiv ℝ (fun y => fderiv ℝ w y v) x v) ∂μ := by
  set a : E → ℝ := fun x => fderiv ℝ w x v with ha_def
  have hr : 0 ≤ 2 * p - 2 := by linarith
  have ha1 : ContDiff ℝ 1 a :=
    (hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have had : Differentiable ℝ a := ha1.differentiable (by norm_num)
  have hb : Continuous fun x => fderiv ℝ a x v :=
    (ha1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hG : ∀ x, HasFDerivAt (fun y => oddPow (2 * p - 2) (a y))
      (((2 * p - 2 + 1) * |a x| ^ (2 * p - 2)) • fderiv ℝ a x) x :=
    fun x => (hasDerivAt_oddPow hr (a x)).comp_hasFDerivAt x (had x).hasFDerivAt
  have hGv : ∀ x, fderiv ℝ (fun y => oddPow (2 * p - 2) (a y)) x v =
      (2 * p - 1) * |a x| ^ (2 * p - 2) * fderiv ℝ a x v := by
    intro x
    rw [(hG x).fderiv, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    ring
  have hsa : HasCompactSupport a := hs.fderiv_apply ℝ v
  have hca : Continuous a := ha1.continuous
  have hwc : Continuous w := hw.continuous
  have hcG : Continuous fun x => oddPow (2 * p - 2) (a x) := (continuous_oddPow hr).comp hca
  have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (f := w)
    (g := fun y => oddPow (2 * p - 2) (a y)) (v := v) ?_ ?_ ?_
    (fun x _ => (hw.differentiable (by norm_num) x)) (fun x _ => (hG x).differentiableAt)
  · simp_rw [hGv] at ibp
    have hlhs : (fun x => |fderiv ℝ w x v| ^ (2 * p)) =
        fun x => fderiv ℝ w x v * oddPow (2 * p - 2) (a x) := by
      funext x
      rw [mul_oddPow _ _ hr]
      congr 1
      ring
    rw [hlhs, ibp, neg_neg]
  · -- `∂_v w · G(a)`
    refine Continuous.integrable_of_hasCompactSupport (hca.mul hcG) ?_
    exact hsa.mul_right
  · -- `w · ∂_v G(a)`
    simp_rw [hGv]
    refine Continuous.integrable_of_hasCompactSupport
      (hwc.mul ((continuous_const.mul ((continuous_abs_rpow hr).comp hca)).mul hb)) ?_
    exact hs.mul_right
  · exact Continuous.integrable_of_hasCompactSupport (hwc.mul hcG) hs.mul_right

/-- **Mixed Gagliardo–Nirenberg, integral form** (tex 5756–5762, B0690): for `w ∈ C²_c`,
`|w| ≤ M` and `1 ≤ p`,
`(∫ |∂_v w|^{2p})^{1/p} ≤ (2p - 1) M (∫ |∂_v∂_v w|^p)^{1/p}`. -/
theorem gn_mixed_integral {w : E → ℝ} (hw : ContDiff ℝ 2 w) (hs : HasCompactSupport w)
    {M : ℝ} (hM : ∀ x, |w x| ≤ M) (v : E) {p : ℝ} (hp : 1 ≤ p) :
    (∫ x, |fderiv ℝ w x v| ^ (2 * p) ∂μ) ^ (1 / p) ≤
      (2 * p - 1) * M * (∫ x, |fderiv ℝ (fun y => fderiv ℝ w y v) x v| ^ p ∂μ) ^ (1 / p) := by
  set a : E → ℝ := fun x => fderiv ℝ w x v with ha_def
  set b : E → ℝ := fun x => fderiv ℝ a x v with hb_def
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hr : 0 ≤ 2 * p - 2 := by linarith
  have hp0 : 0 < p := by linarith
  have ha1 : ContDiff ℝ 1 a :=
    (hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hca : Continuous a := ha1.continuous
  have hcb : Continuous b := (ha1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsa : HasCompactSupport a := hs.fderiv_apply ℝ v
  have hsb : HasCompactSupport b := hsa.fderiv_apply ℝ v
  set I : ℝ := ∫ x, |a x| ^ (2 * p) ∂μ with hI
  set B : ℝ := ∫ x, |b x| ^ p ∂μ with hB
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  have hB0 : 0 ≤ B := integral_nonneg fun x => by positivity
  -- step 1: `I ≤ (2p-1) M ∫ |a|^{2p-2} |b|`
  have hJint : Integrable (fun x => |a x| ^ (2 * p - 2) * |b x|) μ :=
    Continuous.integrable_of_hasCompactSupport
      (((continuous_abs_rpow hr).comp hca).mul (continuous_abs.comp hcb)) hsb.abs.mul_left
  have step1 : I ≤ (2 * p - 1) * M * ∫ x, |a x| ^ (2 * p - 2) * |b x| ∂μ := by
    rw [hI, integral_abs_rpow_dirDeriv_eq μ hw hs v hp, ← integral_const_mul]
    refine (neg_le_abs _).trans ((abs_integral_le_integral_abs).trans ?_)
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
      (hJint.const_mul _) (Eventually.of_forall fun x => ?_)
    simp only
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * p - 1),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |a x| ^ (2 * p - 2))]
    have h1 : |w x| ≤ M := hM x
    have h2 : 0 ≤ (2 * p - 1) * |a x| ^ (2 * p - 2) * |b x| := by
      have : (0 : ℝ) ≤ 2 * p - 1 := by linarith
      positivity
    calc |w x| * ((2 * p - 1) * |a x| ^ (2 * p - 2) * |b x|)
        ≤ M * ((2 * p - 1) * |a x| ^ (2 * p - 2) * |b x|) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = (2 * p - 1) * M * (|a x| ^ (2 * p - 2) * |b x|) := by ring
  -- step 2: Hölder
  have step2 : ∫ x, |a x| ^ (2 * p - 2) * |b x| ∂μ ≤ I ^ ((p - 1) / p) * B ^ (1 / p) := by
    rcases eq_or_lt_of_le hp with h1 | h1
    · subst h1
      simp only [show (2 : ℝ) * 1 - 2 = 0 by norm_num, Real.rpow_zero, one_mul, sub_self,
        div_one, Real.rpow_one, hB]
      exact le_rfl
    · have hq : (p / (p - 1)).HolderConjugate p :=
        ((Real.holderConjugate_iff_eq_conjExponent h1).2 rfl).symm
      have hr' : 0 < 2 * p - 2 := by linarith
      have hmem1 : MemLp (fun x => |a x| ^ (2 * p - 2)) (ENNReal.ofReal (p / (p - 1))) μ := by
        refine Continuous.memLp_of_hasCompactSupport ((continuous_abs_rpow hr).comp hca) ?_
        refine hsa.comp_left (g := fun t : ℝ => |t| ^ (2 * p - 2)) ?_
        simp [Real.zero_rpow hr'.ne']
      have hmem2 : MemLp (fun x => |b x|) (ENNReal.ofReal p) μ :=
        Continuous.memLp_of_hasCompactSupport (continuous_abs.comp hcb) hsb.abs
      have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hq
        (Eventually.of_forall fun x => by positivity)
        (Eventually.of_forall fun x => abs_nonneg (b x)) hmem1 hmem2
      refine hH.trans (le_of_eq ?_)
      have hp1 : (p - 1) ≠ 0 := by linarith
      have e1 : (fun x => (|a x| ^ (2 * p - 2)) ^ (p / (p - 1))) = fun x => |a x| ^ (2 * p) := by
        funext x
        rw [← Real.rpow_mul (abs_nonneg _)]
        congr 1
        field_simp
      have e2 : (fun x => |b x| ^ p) = fun x => |b x| ^ p := rfl
      rw [e1, one_div_div, ← hI, ← hB]
  -- step 3: absorb
  have hC0 : 0 ≤ (2 * p - 1) * M := mul_nonneg (by linarith) hM0
  have hmain : I ≤ (2 * p - 1) * M * (I ^ ((p - 1) / p) * B ^ (1 / p)) :=
    step1.trans (mul_le_mul_of_nonneg_left step2 hC0)
  rcases eq_or_lt_of_le hI0 with hI00 | hIpos
  · rw [← hI00, Real.zero_rpow (by positivity)]
    have : 0 ≤ B ^ (1 / p) := Real.rpow_nonneg hB0 _
    exact mul_nonneg hC0 this
  · have hexp : (p - 1) / p + 1 / p = 1 := by
      rw [← add_div, sub_add_cancel, div_self hp0.ne']
    have hsplit : I = I ^ ((p - 1) / p) * I ^ (1 / p) := by
      rw [← Real.rpow_add hIpos, hexp, Real.rpow_one]
    have hpos : 0 < I ^ ((p - 1) / p) := Real.rpow_pos_of_pos hIpos _
    have h3 : I ^ ((p - 1) / p) * I ^ (1 / p) ≤
        I ^ ((p - 1) / p) * ((2 * p - 1) * M * B ^ (1 / p)) := by
      rw [← hsplit]
      calc I ≤ (2 * p - 1) * M * (I ^ ((p - 1) / p) * B ^ (1 / p)) := hmain
        _ = I ^ ((p - 1) / p) * ((2 * p - 1) * M * B ^ (1 / p)) := by ring
    exact le_of_mul_le_mul_left h3 hpos

/-- **Mixed Gagliardo–Nirenberg** (eq. (2.45), tex 5756–5762, B0690): for `w ∈ C²_c(E)`,
`|w| ≤ M` everywhere and `1 ≤ p`,
`‖∂_v w‖²_{L^{2p}} ≤ (2p - 1) M ‖∂_v∂_v w‖_{L^p}`. -/
theorem gn_mixed {w : E → ℝ} (hw : ContDiff ℝ 2 w) (hs : HasCompactSupport w)
    {M : ℝ} (hM : ∀ x, |w x| ≤ M) (v : E) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => fderiv ℝ w x v) (ENNReal.ofReal (2 * p)) μ ^ 2 ≤
      ENNReal.ofReal ((2 * p - 1) * M) *
        eLpNorm (fun x => fderiv ℝ (fun y => fderiv ℝ w y v) x v) (ENNReal.ofReal p) μ := by
  set a : E → ℝ := fun x => fderiv ℝ w x v with ha_def
  set b : E → ℝ := fun x => fderiv ℝ a x v with hb_def
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hp0 : 0 < p := by linarith
  have ha1 : ContDiff ℝ 1 a :=
    (hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hca : Continuous a := ha1.continuous
  have hcb : Continuous b := (ha1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsa : HasCompactSupport a := hs.fderiv_apply ℝ v
  have hsb : HasCompactSupport b := hsa.fderiv_apply ℝ v
  have hma : MemLp a (ENNReal.ofReal (2 * p)) μ := hca.memLp_of_hasCompactSupport hsa
  have hmb : MemLp b (ENNReal.ofReal p) μ := hcb.memLp_of_hasCompactSupport hsb
  have h2p : (ENNReal.ofReal (2 * p)).toReal = 2 * p := ENNReal.toReal_ofReal (by linarith)
  have hpp : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  rw [hma.eLpNorm_eq_integral_rpow_norm (by simp; linarith) ENNReal.ofReal_ne_top,
    hmb.eLpNorm_eq_integral_rpow_norm (by simp; linarith) ENNReal.ofReal_ne_top, h2p, hpp]
  simp only [Real.norm_eq_abs]
  set I : ℝ := ∫ x, |a x| ^ (2 * p) ∂μ with hI
  set B : ℝ := ∫ x, |b x| ^ p ∂μ with hB
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  have hkey := gn_mixed_integral μ hw hs hM v hp
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by nlinarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : (I ^ (2 * p)⁻¹) ^ 2 = I ^ (1 / p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hI0]
    congr 1
    field_simp
    norm_num
  rw [hsq]
  simpa [one_div] using hkey

/-! ### Passage to limits (the closure step of the density argument) -/

/-- **Closure step** for the density proof of (2.45) (tex 5756–5762, B0690): if `w_k ∈ C²_c`
with `|w_k| ≤ M`, `∂_v w_k → g` almost everywhere and `∂_v∂_v w_k → h` in `L^p`, then
`‖g‖²_{2p} ≤ (2p - 1) M ‖h‖_p`. -/
theorem gn_mixed_of_tendsto {w : ℕ → E → ℝ} (hw : ∀ k, ContDiff ℝ 2 (w k))
    (hs : ∀ k, HasCompactSupport (w k)) {M : ℝ} (hM : ∀ k x, |w k x| ≤ M) (v : E) {p : ℝ}
    (hp : 1 ≤ p) {g h : E → ℝ} (hhm : AEStronglyMeasurable h μ)
    (hg : ∀ᵐ x ∂μ, Tendsto (fun k => fderiv ℝ (w k) x v) atTop (𝓝 (g x)))
    (hh : Tendsto (fun k => eLpNorm (fun x => fderiv ℝ (fun y => fderiv ℝ (w k) y v) x v - h x)
      (ENNReal.ofReal p) μ) atTop (𝓝 0)) :
    eLpNorm g (ENNReal.ofReal (2 * p)) μ ^ 2 ≤
      ENNReal.ofReal ((2 * p - 1) * M) * eLpNorm h (ENNReal.ofReal p) μ := by
  set C : ℝ≥0∞ := ENNReal.ofReal ((2 * p - 1) * M)
  set u : ℕ → ℝ≥0∞ := fun k => eLpNorm (fun x => fderiv ℝ (w k) x v) (ENNReal.ofReal (2 * p)) μ
  set e : ℕ → ℝ≥0∞ := fun k =>
    eLpNorm (fun x => fderiv ℝ (fun y => fderiv ℝ (w k) y v) x v - h x) (ENNReal.ofReal p) μ
  set H : ℝ≥0∞ := eLpNorm h (ENNReal.ofReal p) μ
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hcont : ∀ k, Continuous fun x => fderiv ℝ (w k) x v := fun k =>
    ((hw k).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcont2 : ∀ k, Continuous fun x => fderiv ℝ (fun y => fderiv ℝ (w k) y v) x v := fun k =>
    (((hw k).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
      |>.continuous_fderiv (by norm_num)).clm_apply continuous_const
  -- each term
  have hk : ∀ k, u k ≤ (C * (e k + H)) ^ (2⁻¹ : ℝ) := by
    intro k
    have h1 := gn_mixed μ (hw k) (hs k) (hM k) v hp
    have htri : eLpNorm (fun x => fderiv ℝ (fun y => fderiv ℝ (w k) y v) x v)
        (ENNReal.ofReal p) μ ≤ e k + H := by
      have := eLpNorm_add_le (μ := μ) (p := ENNReal.ofReal p)
        (f := fun x => fderiv ℝ (fun y => fderiv ℝ (w k) y v) x v - h x) (g := h)
        (((hcont2 k).aestronglyMeasurable).sub hhm) hhm hp1
      have hfun : ((fun x => fderiv ℝ (fun y => fderiv ℝ (w k) y v) x v - h x) + h) =
          fun x => fderiv ℝ (fun y => fderiv ℝ (w k) y v) x v := by
        funext x; simp
      rw [hfun] at this
      exact this
    have h2 : u k ^ 2 ≤ C * (e k + H) := h1.trans (by gcongr)
    calc u k = (u k ^ 2) ^ (2⁻¹ : ℝ) := by
          rw [show (2⁻¹ : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.pow_rpow_inv_natCast (by norm_num)]
      _ ≤ (C * (e k + H)) ^ (2⁻¹ : ℝ) := ENNReal.rpow_le_rpow h2 (by norm_num)
  -- limits
  have hlim : Tendsto (fun k => (C * (e k + H)) ^ (2⁻¹ : ℝ)) atTop (𝓝 ((C * H) ^ (2⁻¹ : ℝ))) := by
    have h1 : Tendsto (fun k => e k + H) atTop (𝓝 (0 + H)) := hh.add tendsto_const_nhds
    rw [zero_add] at h1
    have hC : C ≠ ⊤ := ENNReal.ofReal_ne_top
    have h2 : Tendsto (fun k => C * (e k + H)) atTop (𝓝 (C * H)) :=
      ENNReal.Tendsto.const_mul h1 (Or.inr hC)
    exact (ENNReal.continuous_rpow_const.tendsto _).comp h2
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal (2 * p))
    (fun k => (hcont k).aestronglyMeasurable) g hg
  have hle : eLpNorm g (ENNReal.ofReal (2 * p)) μ ≤ (C * H) ^ (2⁻¹ : ℝ) := by
    refine hfatou.trans ?_
    rw [← hlim.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall hk)
  calc eLpNorm g (ENNReal.ofReal (2 * p)) μ ^ 2 ≤ ((C * H) ^ (2⁻¹ : ℝ)) ^ 2 := by gcongr
    _ = C * H := by
      rw [show (2⁻¹ : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.rpow_inv_natCast_pow (by norm_num)]

end GN

end UnforcedLeray.Sob
