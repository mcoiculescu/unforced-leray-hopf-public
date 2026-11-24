import UnforcedLeray.Lib.SobolevC.GagliardoNirenberg
import UnforcedLeray.Lib.ConvIneq
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The mixed Gagliardo–Nirenberg inequality for weak derivatives (block 2E, critic item 4)

Manuscript eq. (2.45), tex 5756–5762, blueprint unit B0690; scoping critic

parts for `C_c^∞` functions plus density").

`GagliardoNirenberg.lean` proves `‖∂_v w‖²_{2p} ≤ (2p - 1) M ‖∂_v∂_v w‖_p` for `w ∈ C²_c`,
`|w| ≤ M`.  This file removes the smoothness: for `f ∈ L^p(ℝⁿ)` with `|f| ≤ M` a.e. and weak
derivatives `g = ∂_v f`, `h = ∂_v g` in `L^p`,
`‖g‖²_{L^{2p}} ≤ (2p - 1) M ‖h‖_{L^p}` (`gn_mixed_weak`), and the `W^{2,p}` form
`W.gn_mixed` for the coordinate directions.

## Proof
1. *Cutoff* `χ_R(x) = χ(x/R)` (`cut`): `χ_R f` has compact support, `|χ_R f| ≤ M`, and by
   the Leibniz rule (`HasWeakDeriv.smul_left`) its weak derivatives are
   `g_R = (∂χ_R) f + χ_R g`, `h_R = (∂²χ_R) f + 2 (∂χ_R) g + χ_R h`, with
   `‖h_R‖_p ≤ ‖h‖_p + O(1/R)`, and `g_R → g` pointwise.
2. *Mollification* `w_k = φ_k ⋆ (χ_R f)` (`moll`): `w_k ∈ C^∞_c`, `|w_k| ≤ M`,
   `∂_v w_k = φ_k ⋆ g_R` (`fderiv_moll_apply`), `∂_v∂_v w_k = φ_k ⋆ h_R`,
   `‖φ_k ⋆ h_R‖_p ≤ ‖h_R‖_p` (Young, `Lib/ConvIneq`), and `φ_k ⋆ g_R → g_R` a.e. (Lebesgue
   differentiation, Mathlib `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`).
3. Both limits are closed by Fatou (`eLpNorm_sq_le_of_ae_tendsto`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff Convolution

namespace UnforcedLeray.Sob

namespace GN

/-! ### The Fatou closure -/

section Fatou

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

/-- **Closure under a.e. limits**: if `‖u_k‖²_q ≤ C (B + e_k)` with `e_k → 0` and `u_k → g`
a.e., then `‖g‖²_q ≤ C B`. -/
theorem eLpNorm_sq_le_of_ae_tendsto {u : ℕ → E → ℝ} {g : E → ℝ}
    (hu : ∀ k, AEStronglyMeasurable (u k) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => u k x) atTop (𝓝 (g x))) {q C B : ℝ≥0∞}
    {e : ℕ → ℝ≥0∞} (hC : C ≠ ⊤) (he : Tendsto e atTop (𝓝 0))
    (hk : ∀ k, eLpNorm (u k) q μ ^ 2 ≤ C * (B + e k)) :
    eLpNorm g q μ ^ 2 ≤ C * B := by
  have hk' : ∀ k, eLpNorm (u k) q μ ≤ (C * (B + e k)) ^ (2⁻¹ : ℝ) := by
    intro k
    calc eLpNorm (u k) q μ = (eLpNorm (u k) q μ ^ 2) ^ (2⁻¹ : ℝ) := by
          rw [show (2⁻¹ : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num,
            ENNReal.pow_rpow_inv_natCast (by norm_num)]
      _ ≤ (C * (B + e k)) ^ (2⁻¹ : ℝ) := ENNReal.rpow_le_rpow (hk k) (by norm_num)
  have hlim' : Tendsto (fun k => (C * (B + e k)) ^ (2⁻¹ : ℝ)) atTop (𝓝 ((C * B) ^ (2⁻¹ : ℝ))) := by
    have h1 : Tendsto (fun k => B + e k) atTop (𝓝 (B + 0)) := tendsto_const_nhds.add he
    rw [add_zero] at h1
    have h2 : Tendsto (fun k => C * (B + e k)) atTop (𝓝 (C * B)) :=
      ENNReal.Tendsto.const_mul h1 (Or.inr hC)
    exact (ENNReal.continuous_rpow_const.tendsto _).comp h2
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := q) hu g hlim
  have hle : eLpNorm g q μ ≤ (C * B) ^ (2⁻¹ : ℝ) := by
    refine hfatou.trans ?_
    rw [← hlim'.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall hk')
  calc eLpNorm g q μ ^ 2 ≤ ((C * B) ^ (2⁻¹ : ℝ)) ^ 2 := by gcongr
    _ = C * B := by
      rw [show (2⁻¹ : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.rpow_inv_natCast_pow (by norm_num)]

end Fatou

variable {n : ℕ}

/-! ### Mollification -/

/-- The mollifier bumps `rIn = 1/(k+1)`, `rOut = 2/(k+1)`. -/
def mollBump (n : ℕ) (k : ℕ) : ContDiffBump (0 : Eucl n) where
  rIn := 1 / (k + 1)
  rOut := 2 / (k + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < k + 1 := by positivity
    rw [div_lt_div_iff_of_pos_right this]; norm_num

/-- The mollifier `φ_k = (mollBump k).normed`. -/
def mollK (n : ℕ) (k : ℕ) : Eucl n → ℝ := (mollBump n k).normed volume

/-- `moll k u = φ_k ⋆ u`. -/
def moll (k : ℕ) (u : Eucl n → ℝ) : Eucl n → ℝ :=
  mollK n k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u

theorem moll_apply (k : ℕ) (u : Eucl n → ℝ) (x : Eucl n) :
    moll k u x = ∫ t, mollK n k (x - t) • u t := by
  rw [moll, convolution_lsmul_swap]

theorem contDiff_mollK (k : ℕ) : ContDiff ℝ ∞ (mollK n k) :=
  (mollBump n k).contDiff_normed

theorem hasCompactSupport_mollK (k : ℕ) : HasCompactSupport (mollK n k) :=
  (mollBump n k).hasCompactSupport_normed

theorem mollK_nonneg (k : ℕ) (x : Eucl n) : 0 ≤ mollK n k x :=
  (mollBump n k).nonneg_normed x

theorem integral_mollK (k : ℕ) : ∫ x, mollK n k x = 1 :=
  (mollBump n k).integral_normed

theorem eLpNorm_one_mollK (k : ℕ) : eLpNorm (mollK n k) 1 volume = 1 := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hint : Integrable (mollK n k) volume :=
    (contDiff_mollK k).continuous.integrable_of_hasCompactSupport (hasCompactSupport_mollK k)
  rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
  simp_rw [Real.norm_of_nonneg (mollK_nonneg k _)]
  rw [integral_mollK, ENNReal.ofReal_one]

/-- **Derivative of a mollification** = mollification of the weak derivative. -/
theorem fderiv_moll_apply (k : ℕ) {v : Eucl n} {u u' : Eucl n → ℝ}
    (hu : LocallyIntegrable u volume) (h : HasWeakDeriv (wholeSpace n) [v] u u') (x : Eucl n) :
    fderiv ℝ (moll k u) x v = moll k u' x := by
  set φ := mollK n k
  have hφ : ContDiff ℝ ∞ φ := contDiff_mollK k
  have hφc : HasCompactSupport φ := hasCompactSupport_mollK k
  have hd := hφc.hasFDerivAt_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (hφ.of_le (by simp)) hu x
  rw [moll, hd.fderiv]
  -- integrability of the derivative integrand
  have hex := (hφc.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Eucl n))
    (hφ.continuous_fderiv (by simp)) hu x
  rw [convolution_def, ContinuousLinearMap.integral_apply hex]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  -- change of variables `t ↦ x - t`
  have hcov : ∫ t, fderiv ℝ φ t v • u (x - t) = ∫ s, fderiv ℝ φ (x - s) v • u s := by
    rw [← integral_sub_left_eq_self (fun s => fderiv ℝ φ (x - s) v • u s) volume x]
    simp only [sub_sub_cancel]
  rw [hcov, moll_apply]
  set ψ : Eucl n → ℝ := fun s => φ (x - s) with hψ_def
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph (Homeomorph.subLeft x)
  have hdψ : ∀ s, fderiv ℝ ψ s v = -(fderiv ℝ φ (x - s) v) := by
    intro s
    have h1 : HasFDerivAt (fun s : Eucl n => x - s) (-ContinuousLinearMap.id ℝ (Eucl n)) s :=
      (hasFDerivAt_id s).const_sub x
    have h2 : HasFDerivAt ψ ((fderiv ℝ φ (x - s)).comp (-ContinuousLinearMap.id ℝ (Eucl n))) s :=
      ((hφ.differentiable (by simp)) (x - s)).hasFDerivAt.comp s h1
    rw [h2.fderiv]
    simp
  have hid := h.identity ψ ⟨hψ, hψc⟩
  simp only [iterDirDeriv_singleton, wholeSpace_μ, List.length_singleton, pow_one, neg_smul,
    one_smul] at hid
  simp_rw [hdψ, neg_smul, integral_neg] at hid
  exact neg_inj.mp hid

theorem contDiff_moll (k : ℕ) {u : Eucl n → ℝ} (hu : LocallyIntegrable u volume) :
    ContDiff ℝ ∞ (moll k u) :=
  (hasCompactSupport_mollK k).contDiff_convolution_left _ (contDiff_mollK k) hu

theorem hasCompactSupport_moll (k : ℕ) {u : Eucl n → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (moll k u) :=
  (hasCompactSupport_mollK k).convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hu

theorem integrable_mollK_sub (k : ℕ) (x : Eucl n) :
    Integrable (fun t => mollK n k (x - t)) volume :=
  ((contDiff_mollK k).continuous.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
    ((hasCompactSupport_mollK k).comp_homeomorph (Homeomorph.subLeft x))

theorem abs_moll_le (k : ℕ) {u : Eucl n → ℝ} {M : ℝ} (hM : ∀ᵐ t ∂volume, |u t| ≤ M)
    (x : Eucl n) : |moll k u x| ≤ M := by
  rw [moll_apply, ← Real.norm_eq_abs]
  calc ‖∫ t, mollK n k (x - t) • u t‖ ≤ ∫ t, mollK n k (x - t) * M := by
        refine norm_integral_le_of_norm_le ((integrable_mollK_sub k x).mul_const M) ?_
        filter_upwards [hM] with t ht
        rw [Real.norm_eq_abs, smul_eq_mul, abs_mul, abs_of_nonneg (mollK_nonneg k _)]
        exact mul_le_mul_of_nonneg_left ht (mollK_nonneg k _)
    _ = M := by
        rw [integral_mul_const, integral_sub_left_eq_self (mollK n k) volume x, integral_mollK,
          one_mul]

/-- Young: `‖φ_k ⋆ u‖_p ≤ ‖u‖_p`. -/
theorem eLpNorm_moll_le (k : ℕ) {u : Eucl n → ℝ} (hu : AEStronglyMeasurable u volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) : eLpNorm (moll k u) p volume ≤ eLpNorm u p volume := by
  have := Conv.eLpNorm_convolution_le_L1 (volume : Measure (Eucl n)) (K := mollK n k) (f := u)
    (contDiff_mollK k).continuous.aestronglyMeasurable hu hp
  rw [eLpNorm_one_mollK, one_mul] at this
  refine le_trans (le_of_eq ?_) this
  congr 1
  funext x
  exact moll_apply k u x

/-- Lebesgue differentiation: `φ_k ⋆ u → u` a.e. -/
theorem ae_tendsto_moll {u : Eucl n → ℝ} (hu : LocallyIntegrable u volume) :
    ∀ᵐ x ∂volume, Tendsto (fun k => moll k u x) atTop (𝓝 (u x)) := by
  have h1 : Tendsto (fun k => (mollBump n k).rOut) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    simp only [mollBump]
    rw [mul_one_div]
  have h2 : ∀ᶠ k in atTop, (mollBump n k).rOut ≤ 2 * (mollBump n k).rIn :=
    Eventually.of_forall fun k => le_of_eq (by simp only [mollBump]; rw [mul_one_div])
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable h1 h2 hu

/-! ### The smooth compactly supported step -/

/-- **(2.45) for compactly supported weak data** (tex 5756–5762, B0690). -/
theorem gn_mixed_cc {p : ℝ} (hp : 1 ≤ p) {v : Eucl n} {F₀ G₀ H₀ : Eucl n → ℝ} {M : ℝ}
    (hc : HasCompactSupport F₀) (hM : ∀ᵐ x ∂volume, |F₀ x| ≤ M)
    (hF : LocallyIntegrable F₀ volume) (hG : LocallyIntegrable G₀ volume)
    (hH : AEStronglyMeasurable H₀ volume)
    (h1 : HasWeakDeriv (wholeSpace n) [v] F₀ G₀) (h2 : HasWeakDeriv (wholeSpace n) [v] G₀ H₀) :
    eLpNorm G₀ (ENNReal.ofReal (2 * p)) volume ^ 2 ≤
      ENNReal.ofReal ((2 * p - 1) * M) * eLpNorm H₀ (ENNReal.ofReal p) volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hk : ∀ k, eLpNorm (moll k G₀) (ENNReal.ofReal (2 * p)) volume ^ 2 ≤
      ENNReal.ofReal ((2 * p - 1) * M) * (eLpNorm H₀ (ENNReal.ofReal p) volume + 0) := by
    intro k
    have hw2 : ContDiff ℝ 2 (moll k F₀) := (contDiff_moll k hF).of_le (by simp)
    have hd1 : (fun x => fderiv ℝ (moll k F₀) x v) = moll k G₀ :=
      funext fun x => fderiv_moll_apply k hF h1 x
    have hd2 : (fun x => fderiv ℝ (moll k G₀) x v) = moll k H₀ :=
      funext fun x => fderiv_moll_apply k hG h2 x
    have := GN.gn_mixed (volume : Measure (Eucl n)) hw2 (hasCompactSupport_moll k hc)
      (abs_moll_le k hM) v hp
    rw [hd1, hd2] at this
    rw [add_zero]
    exact this.trans (by gcongr; exact eLpNorm_moll_le k hH hp1)
  exact eLpNorm_sq_le_of_ae_tendsto (fun k => (contDiff_moll k hG).continuous.aestronglyMeasurable)
    (ae_tendsto_moll hG) ENNReal.ofReal_ne_top tendsto_const_nhds hk

/-! ### Cutoffs -/

/-- The bump `χ` with `χ = 1` on `B(0,1)` and support in `B(0,2)`. -/
def cutBump (n : ℕ) : ContDiffBump (0 : Eucl n) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `χ_R(x) = χ(x/R)`. -/
def cut (R : ℝ) (x : Eucl n) : ℝ := cutBump n (R⁻¹ • x)

theorem contDiff_cut (R : ℝ) : ContDiff ℝ ∞ (cut (n := n) R) :=
  (cutBump n).contDiff.comp (contDiff_const_smul R⁻¹)

theorem cut_nonneg (R : ℝ) (x : Eucl n) : 0 ≤ cut R x := (cutBump n).nonneg

theorem cut_le_one (R : ℝ) (x : Eucl n) : cut R x ≤ 1 := (cutBump n).le_one

theorem hasCompactSupport_cut {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (cut (n := n) R) :=
  (cutBump n).hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR))

theorem cut_eq_one {R : ℝ} (hR : 0 < R) {x : Eucl n} (hx : ‖x‖ ≤ R) : cut R x = 1 := by
  refine (cutBump n).one_of_mem_closedBall ?_
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  calc R⁻¹ * ‖x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
    _ = 1 := inv_mul_cancel₀ hR.ne'

theorem fderiv_cut_eq_zero {R : ℝ} (hR : 0 < R) {x : Eucl n} (hx : ‖x‖ < R) :
    fderiv ℝ (cut (n := n) R) x = 0 := by
  have : cut (n := n) R =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx)] with y hy
    exact cut_eq_one hR (le_of_lt (mem_ball_zero_iff.mp hy))
  rw [this.fderiv_eq]
  exact fderiv_const_apply 1

/-- Directional derivative of `y ↦ a (c • y)`. -/
theorem fderiv_comp_smul_apply {a : Eucl n → ℝ} (ha : Differentiable ℝ a) (c : ℝ)
    (x v : Eucl n) : fderiv ℝ (fun y => a (c • y)) x v = c * fderiv ℝ a (c • x) v := by
  have hA : HasFDerivAt (fun y : Eucl n => c • y) (c • ContinuousLinearMap.id ℝ (Eucl n)) x :=
    (hasFDerivAt_id x).const_smul c
  have h : HasFDerivAt (fun y => a (c • y))
      ((fderiv ℝ a (c • x)).comp (c • ContinuousLinearMap.id ℝ (Eucl n))) x :=
    (ha (c • x)).hasFDerivAt.comp x hA
  rw [h.fderiv]
  simp [smul_eq_mul]

/-- `∂_v χ` and `∂_v∂_v χ` for the fixed bump. -/
def d1 (n : ℕ) (v : Eucl n) (y : Eucl n) : ℝ := fderiv ℝ (cutBump n) y v

def d2 (n : ℕ) (v : Eucl n) (y : Eucl n) : ℝ := fderiv ℝ (d1 n v) y v

theorem contDiff_d1 (v : Eucl n) : ContDiff ℝ ∞ (d1 n v) :=
  contDiff_dirDeriv (cutBump n).contDiff v

theorem contDiff_d2 (v : Eucl n) : ContDiff ℝ ∞ (d2 n v) :=
  contDiff_dirDeriv (contDiff_d1 v) v

theorem exists_bound_d1 (v : Eucl n) : ∃ C, ∀ y, ‖d1 n v y‖ ≤ C :=
  (contDiff_d1 v).continuous.bounded_above_of_compact_support
    ((cutBump n).hasCompactSupport.fderiv_apply ℝ v)

theorem exists_bound_d2 (v : Eucl n) : ∃ C, ∀ y, ‖d2 n v y‖ ≤ C :=
  (contDiff_d2 v).continuous.bounded_above_of_compact_support
    (((cutBump n).hasCompactSupport.fderiv_apply ℝ v).fderiv_apply ℝ v)

theorem fderiv_cut_apply (R : ℝ) (x v : Eucl n) :
    fderiv ℝ (cut R) x v = R⁻¹ * d1 n v (R⁻¹ • x) :=
  fderiv_comp_smul_apply (((cutBump n).contDiff (n := 1)).differentiable one_ne_zero) R⁻¹ x v

theorem fderiv_fderiv_cut_apply (R : ℝ) (x v : Eucl n) :
    fderiv ℝ (fun y => fderiv ℝ (cut R) y v) x v = R⁻¹ * (R⁻¹ * d2 n v (R⁻¹ • x)) := by
  have hfun : (fun y => fderiv ℝ (cut (n := n) R) y v) = fun y => R⁻¹ * d1 n v (R⁻¹ • y) :=
    funext fun y => fderiv_cut_apply R y v
  have hd : Differentiable ℝ (fun y : Eucl n => d1 n v (R⁻¹ • y)) :=
    ((contDiff_d1 v).differentiable (by simp)).comp (differentiable_id.const_smul R⁻¹)
  rw [hfun, fderiv_const_mul (hd x), ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_comp_smul_apply ((contDiff_d1 v).differentiable (by simp)) R⁻¹ x v]
  rfl

/-! ### The weak-derivative inequality -/

/-- **Mixed Gagliardo–Nirenberg for weak derivatives** (eq. (2.45), tex 5756–5762, B0690):
for `1 ≤ p < ∞`, `f ∈ L^p(ℝⁿ)` with `|f| ≤ M` a.e., `g = ∂_v f` and `h = ∂_v g` weakly, both in
`L^p`, `‖g‖²_{L^{2p}} ≤ (2p - 1) M ‖h‖_{L^p}`. -/
theorem gn_mixed_weak {p : ℝ} (hp : 1 ≤ p) {v : Eucl n} {f g h : Eucl n → ℝ} {M : ℝ}
    (hM : ∀ᵐ x ∂volume, |f x| ≤ M) (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal p) volume) (hh : MemLp h (ENNReal.ofReal p) volume)
    (hfg : HasWeakDeriv (wholeSpace n) [v] f g) (hgh : HasWeakDeriv (wholeSpace n) [v] g h) :
    eLpNorm g (ENNReal.ofReal (2 * p)) volume ^ 2 ≤
      ENNReal.ofReal ((2 * p - 1) * M) * eLpNorm h (ENNReal.ofReal p) volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable hp1
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable hp1
  have hhl : LocallyIntegrable h volume := hh.locallyIntegrable hp1
  obtain ⟨C₁, hC₁⟩ := exists_bound_d1 v
  obtain ⟨C₂, hC₂⟩ := exists_bound_d2 v
  set Rk : ℕ → ℝ := fun k => (k : ℝ) + 1 with hRk
  have hRpos : ∀ k, 0 < Rk k := fun k => by positivity
  -- the cut-off data
  set χ : ℕ → Eucl n → ℝ := fun k => cut (Rk k) with hχ
  set a1 : ℕ → Eucl n → ℝ := fun k y => fderiv ℝ (χ k) y v with ha1
  set a2 : ℕ → Eucl n → ℝ := fun k y => fderiv ℝ (a1 k) y v with ha2
  have hχs : ∀ k, ContDiff ℝ ∞ (χ k) := fun k => contDiff_cut _
  have ha1s : ∀ k, ContDiff ℝ ∞ (a1 k) := fun k => contDiff_dirDeriv (hχs k) v
  have ha1b : ∀ k y, ‖a1 k y‖ ≤ (Rk k)⁻¹ * C₁ := by
    intro k y
    simp only [ha1, hχ]
    rw [fderiv_cut_apply, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hRpos k))]
    exact mul_le_mul_of_nonneg_left (hC₁ _) (inv_nonneg.mpr (hRpos k).le)
  have ha2b : ∀ k y, ‖a2 k y‖ ≤ (Rk k)⁻¹ * ((Rk k)⁻¹ * C₂) := by
    intro k y
    simp only [ha2, ha1, hχ]
    rw [fderiv_fderiv_cut_apply, norm_mul, norm_mul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hRpos k))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC₂ _)
      (inv_nonneg.mpr (hRpos k).le)) (inv_nonneg.mpr (hRpos k).le)
  set F : ℕ → Eucl n → ℝ := fun k y => χ k y • f y with hF
  set G : ℕ → Eucl n → ℝ := fun k y => a1 k y • f y + χ k y • g y with hG
  set H : ℕ → Eucl n → ℝ := fun k y =>
    (a2 k y • f y + a1 k y • g y) + (a1 k y • g y + χ k y • h y) with hH
  have hFG : ∀ k, HasWeakDeriv (wholeSpace n) [v] (F k) (G k) := fun k =>
    HasWeakDeriv.smul_left (hχs k) hfl hgl hfg
  have hGH : ∀ k, HasWeakDeriv (wholeSpace n) [v] (G k) (H k) := fun k =>
    (HasWeakDeriv.smul_left (ha1s k) hfl hgl hfg).add (HasWeakDeriv.smul_left (hχs k) hgl hhl hgh)
  -- each cut-off satisfies the inequality
  set C : ℝ≥0∞ := ENNReal.ofReal ((2 * p - 1) * M)
  set e : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal ((Rk k)⁻¹ * ((Rk k)⁻¹ * C₂)) * eLpNorm f (ENNReal.ofReal p) volume +
      ENNReal.ofReal ((Rk k)⁻¹ * C₁) * eLpNorm g (ENNReal.ofReal p) volume +
      ENNReal.ofReal ((Rk k)⁻¹ * C₁) * eLpNorm g (ENNReal.ofReal p) volume with he
  have hsm : ∀ k, AEStronglyMeasurable (χ k) volume :=
    fun k => (hχs k).continuous.aestronglyMeasurable
  have hsm1 : ∀ k, AEStronglyMeasurable (a1 k) volume :=
    fun k => (ha1s k).continuous.aestronglyMeasurable
  have hsm2 : ∀ k, AEStronglyMeasurable (a2 k) volume :=
    fun k => (contDiff_dirDeriv (ha1s k) v).continuous.aestronglyMeasurable
  have hHle : ∀ k, eLpNorm (H k) (ENNReal.ofReal p) volume ≤
      eLpNorm h (ENNReal.ofReal p) volume + e k := by
    intro k
    have t1 : eLpNorm (fun y => a2 k y • f y) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((Rk k)⁻¹ * ((Rk k)⁻¹ * C₂)) * eLpNorm f (ENNReal.ofReal p) volume :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun y => by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_right (ha2b k y) (norm_nonneg _)) _
    have t2 : eLpNorm (fun y => a1 k y • g y) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((Rk k)⁻¹ * C₁) * eLpNorm g (ENNReal.ofReal p) volume :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun y => by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_right (ha1b k y) (norm_nonneg _)) _
    have t3 : eLpNorm (fun y => χ k y • h y) (ENNReal.ofReal p) volume ≤
        eLpNorm h (ENNReal.ofReal p) volume := by
      refine eLpNorm_mono fun y => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cut_nonneg _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (cut_le_one _ _)
    have m1 : AEStronglyMeasurable (fun y => a2 k y • f y) volume := (hsm2 k).smul hf.1
    have m2 : AEStronglyMeasurable (fun y => a1 k y • g y) volume := (hsm1 k).smul hg.1
    have m3 : AEStronglyMeasurable (fun y => χ k y • h y) volume := (hsm k).smul hh.1
    calc eLpNorm (H k) (ENNReal.ofReal p) volume
        ≤ eLpNorm (fun y => a2 k y • f y + a1 k y • g y) (ENNReal.ofReal p) volume +
            eLpNorm (fun y => a1 k y • g y + χ k y • h y) (ENNReal.ofReal p) volume :=
          eLpNorm_add_le (m1.add m2) (m2.add m3) hp1
      _ ≤ (eLpNorm (fun y => a2 k y • f y) (ENNReal.ofReal p) volume +
            eLpNorm (fun y => a1 k y • g y) (ENNReal.ofReal p) volume) +
          (eLpNorm (fun y => a1 k y • g y) (ENNReal.ofReal p) volume +
            eLpNorm (fun y => χ k y • h y) (ENNReal.ofReal p) volume) :=
          add_le_add (eLpNorm_add_le m1 m2 hp1) (eLpNorm_add_le m2 m3 hp1)
      _ ≤ (ENNReal.ofReal ((Rk k)⁻¹ * ((Rk k)⁻¹ * C₂)) * eLpNorm f (ENNReal.ofReal p) volume +
            ENNReal.ofReal ((Rk k)⁻¹ * C₁) * eLpNorm g (ENNReal.ofReal p) volume) +
          (ENNReal.ofReal ((Rk k)⁻¹ * C₁) * eLpNorm g (ENNReal.ofReal p) volume +
            eLpNorm h (ENNReal.ofReal p) volume) := by gcongr
      _ = eLpNorm h (ENNReal.ofReal p) volume + e k := by simp only [he]; ring
  have hk : ∀ k, eLpNorm (G k) (ENNReal.ofReal (2 * p)) volume ^ 2 ≤
      C * (eLpNorm h (ENNReal.ofReal p) volume + e k) := by
    intro k
    have hFc : HasCompactSupport (F k) := (hasCompactSupport_cut (hRpos k).ne').smul_right
    have hFM : ∀ᵐ y ∂volume, |F k y| ≤ M := by
      filter_upwards [hM] with y hy
      have h0 : 0 ≤ χ k y := cut_nonneg _ _
      have h1 : χ k y ≤ 1 := cut_le_one _ _
      show |χ k y • f y| ≤ M
      rw [smul_eq_mul, abs_mul, abs_of_nonneg h0]
      exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans hy
    have hFl : LocallyIntegrable (F k) volume := hfl.continuous_smul (hχs k).continuous
    have hGl : LocallyIntegrable (G k) volume :=
      (hfl.continuous_smul (ha1s k).continuous).add (hgl.continuous_smul (hχs k).continuous)
    have hHm : AEStronglyMeasurable (H k) volume :=
      (((hsm2 k).smul hf.1).add ((hsm1 k).smul hg.1)).add
        (((hsm1 k).smul hg.1).add ((hsm k).smul hh.1))
    exact (gn_mixed_cc hp hFc hFM hFl hGl hHm (hFG k) (hGH k)).trans (by gcongr; exact hHle k)
  -- the limit `R → ∞`
  have hGlim : ∀ y, Tendsto (fun k => G k y) atTop (𝓝 (g y)) := by
    intro y
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ‖y‖
    filter_upwards [eventually_ge_atTop N] with k hk
    have hlt : ‖y‖ < Rk k := by
      simp only [hRk]
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    simp only [hG, ha1, hχ]
    rw [fderiv_cut_eq_zero (hRpos k) hlt, cut_eq_one (hRpos k) hlt.le]
    simp
  have hRinv : Tendsto (fun k => (Rk k)⁻¹) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine this.congr fun k => ?_
    simp [hRk]
  have hetend : Tendsto e atTop (𝓝 0) := by
    have hof : ∀ c : ℝ, Tendsto (fun k => ENNReal.ofReal ((Rk k)⁻¹ * c)) atTop (𝓝 0) := by
      intro c
      have h0 : Tendsto (fun k => (Rk k)⁻¹ * c) atTop (𝓝 0) := by
        simpa using hRinv.mul_const c
      simpa using ENNReal.tendsto_ofReal h0
    have hof2 : Tendsto (fun k => ENNReal.ofReal ((Rk k)⁻¹ * ((Rk k)⁻¹ * C₂))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun k => (Rk k)⁻¹ * ((Rk k)⁻¹ * C₂)) atTop (𝓝 0) := by
        simpa using hRinv.mul (hRinv.mul_const C₂)
      simpa using ENNReal.tendsto_ofReal h0
    have hfin : eLpNorm f (ENNReal.ofReal p) volume ≠ ⊤ := hf.2.ne
    have hgin : eLpNorm g (ENNReal.ofReal p) volume ≠ ⊤ := hg.2.ne
    have e1 := ENNReal.Tendsto.mul_const hof2 (Or.inr hfin)
    have e2 := ENNReal.Tendsto.mul_const (hof C₁) (Or.inr hgin)
    rw [zero_mul] at e1 e2
    simpa [he] using (e1.add e2).add e2
  exact eLpNorm_sq_le_of_ae_tendsto
    (fun k => (((hsm1 k).smul hf.1).add ((hsm k).smul hg.1)))
    (Eventually.of_forall hGlim) ENNReal.ofReal_ne_top hetend hk

end GN

variable {n : ℕ}

/-- **Mixed Gagliardo–Nirenberg on `W^{2,p}(ℝⁿ)`** (eq. (2.45), tex 5756–5762, B0690): for
`x ∈ W^{2,p}(ℝⁿ)`, `1 ≤ p < ∞`, with `|x| ≤ M` a.e. and each coordinate direction `i`,
`‖∂_i x‖²_{L^{2p}} ≤ (2p - 1) M ‖∂_i∂_i x‖_{L^p}`. -/
theorem W.gn_mixed {p : ℝ} (hp : 1 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)]
    (x : W (wholeSpace n) 1 ℝ ℝ 2 (ENNReal.ofReal p)) {M : ℝ}
    (hM : ∀ᵐ y ∂volume, |W.value (wholeSpace n) 1 ℝ ℝ 2 (ENNReal.ofReal p) x y| ≤ M)
    (i : Fin n) :
    eLpNorm (W.deriv (wholeSpace n) 1 ℝ ℝ 2 (ENNReal.ofReal p) (Idx.cons i Idx.zero) x)
        (ENNReal.ofReal (2 * p)) volume ^ 2 ≤
      ENNReal.ofReal ((2 * p - 1) * M) *
        eLpNorm (W.deriv (wholeSpace n) 1 ℝ ℝ 2 (ENNReal.ofReal p)
          (Idx.cons i (Idx.cons i Idx.zero)) x) (ENNReal.ofReal p) volume := by
  have hmem : ∀ u : Lp ℝ (ENNReal.ofReal p) (wμ (wholeSpace n).μ 1),
      MemLp (u : Eucl n → ℝ) (ENNReal.ofReal p) volume := fun u =>
    (Lp.memLp u).of_measure_le_smul ENNReal.one_ne_top (by rw [one_smul, wμ_one]; rfl)
  have h1 := W.hasWeakDeriv x (Idx.cons i (Idx.zero : Idx n 1))
  have h2 := W.hasWeakDeriv x (Idx.cons i (Idx.cons i (Idx.zero : Idx n 0)))
  rw [TestDomain.word_cons, TestDomain.word_zero, wholeSpace_dir] at h1
  rw [TestDomain.word_cons, TestDomain.word_cons, TestDomain.word_zero, wholeSpace_dir] at h2
  exact GN.gn_mixed_weak hp hM (hmem _) (hmem _) (hmem _) h1 (h1.of_cons h2)



end UnforcedLeray.Sob
