import UnforcedLeray.Lib.Kernels.GaussDeriv
import UnforcedLeray.Units.B0224.PlaneHeat
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Globally Smooth Desingularized 2D Heat Kernel (`GlueKernel`)

Constructs `safeHeat2D θ w`, a globally `C^∞` function on `ℝ × (ℝ × ℝ)` using `expNegInvGlue` and
`Real.smoothTransition` that:
1. Vanishes identically for `θ ≤ 0`;
2. Agrees with `gaussKernel 2 θ y` whenever `θ > 0` and `1 / 4 ≤ ‖y‖ ^ 2`;
3. Has all iterated `(s, q, η)`-derivatives of `(s, x) ↦ safeHeat2D (ν * (τ - s)) (x - z)`
   dominated by `K_{n, T} * ((1 + (x.1 - z.1) ^ 2 + (x.2 - z.2) ^ 2)⁻¹) ^ 2` whenever
   `|ν * (τ - s)| ≤ T`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Nat

namespace UnforcedLeray.Short.PartIIa.FlatAdjointSmoothAux

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0224 (planeι planeι_apply)

/-! ### 1. Definitions and algebraic identities -/

/-- Desingularized squared radius `r² + (1/8) smoothTransition(2 - 8 r²)`, equal to `r²` for
`r² ≥ 1 / 4` and bounded below by `1 / 8` on all of `ℝ × ℝ`. -/
def rhoSq (w : ℝ × ℝ) : ℝ :=
  w.1 ^ 2 + w.2 ^ 2 + (1 / 8 : ℝ) * Real.smoothTransition (2 - 8 * (w.1 ^ 2 + w.2 ^ 2))

def invRhoSq (w : ℝ × ℝ) : ℝ := (rhoSq w)⁻¹

def invRhoSq2 (w : ℝ × ℝ) : ℝ := (rhoSq w)⁻¹ ^ 2

/-- Smooth transition factor `u⁻¹ * expNegInvGlue u` on `ℝ`. -/
def glueInv (u : ℝ) : ℝ := Polynomial.eval u⁻¹ Polynomial.X * expNegInvGlue u

/-- Higher-order smooth transition factor `(u⁻¹)³ * expNegInvGlue u` on `ℝ`. -/
def glueInv3 (u : ℝ) : ℝ := Polynomial.eval u⁻¹ (Polynomial.X ^ 3) * expNegInvGlue u

/-- Globally `C^∞` desingularized 2D heat kernel on `ℝ × (ℝ × ℝ)`. -/
def safeHeat2D (θ : ℝ) (w : ℝ × ℝ) : ℝ :=
  (Real.pi * rhoSq w)⁻¹ * glueInv (4 * θ / rhoSq w)

def safeHeatPair (q : ℝ × (ℝ × ℝ)) : ℝ := safeHeat2D q.1 q.2

def safeHeatProfile (ν τ : ℝ) (z : ℝ × ℝ) (p : Profile) : ℝ :=
  safeHeat2D (ν * (τ - p.1)) (p.2 - z)

theorem rhoSq_ge_eighth (w : ℝ × ℝ) : (1 / 8 : ℝ) ≤ rhoSq w := by
  have hsq : 0 ≤ w.1 ^ 2 + w.2 ^ 2 := by positivity
  by_cases h : w.1 ^ 2 + w.2 ^ 2 ≤ 1 / 8
  · have h1 : 1 ≤ 2 - 8 * (w.1 ^ 2 + w.2 ^ 2) := by linarith
    rw [rhoSq, Real.smoothTransition.one_of_one_le h1]
    linarith
  · have hnn : 0 ≤ Real.smoothTransition (2 - 8 * (w.1 ^ 2 + w.2 ^ 2)) :=
      Real.smoothTransition.nonneg _
    unfold rhoSq
    linarith

theorem rhoSq_pos (w : ℝ × ℝ) : 0 < rhoSq w :=
  lt_of_lt_of_le (by norm_num) (rhoSq_ge_eighth w)

theorem invRhoSq_pos (w : ℝ × ℝ) : 0 < invRhoSq w :=
  inv_pos.2 (rhoSq_pos w)

theorem invRhoSq_le_eight (w : ℝ × ℝ) : invRhoSq w ≤ 8 := by
  unfold invRhoSq
  have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 8) (rhoSq_ge_eighth w)
  norm_num at h
  exact h

theorem rhoSq_eq_of_quarter_le {w : ℝ × ℝ} (hw : 1 / 4 ≤ w.1 ^ 2 + w.2 ^ 2) :
    rhoSq w = w.1 ^ 2 + w.2 ^ 2 := by
  have h0 : 2 - 8 * (w.1 ^ 2 + w.2 ^ 2) ≤ 0 := by linarith
  simp [rhoSq, Real.smoothTransition.zero_of_nonpos h0]

theorem glueInv_eq_sq_mul_glueInv3 (u : ℝ) : glueInv u = u ^ 2 * glueInv3 u := by
  by_cases hu : u ≤ 0
  · simp [glueInv, glueInv3, expNegInvGlue.zero_of_nonpos hu]
  · have hpos : 0 < u := lt_of_not_ge hu
    simp only [glueInv, glueInv3, Polynomial.eval_X, Polynomial.eval_pow]
    field_simp [hpos.ne']

theorem safeHeat2D_of_nonpos {θ : ℝ} (hθ : θ ≤ 0) (w : ℝ × ℝ) : safeHeat2D θ w = 0 := by
  have hu : 4 * θ / rhoSq w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (rhoSq_pos w).le
  simp [safeHeat2D, glueInv, expNegInvGlue.zero_of_nonpos hu]

theorem safeHeat2D_eq_gaussKernel {θ : ℝ} (hθ : 0 < θ) {y : Euc 2}
    (hy : 1 / 4 ≤ (planeι y).1 ^ 2 + (planeι y).2 ^ 2) :
    safeHeat2D θ (planeι y) = gaussKernel 2 θ y := by
  set r2 : ℝ := (planeι y).1 ^ 2 + (planeι y).2 ^ 2
  have hr2_pos : 0 < r2 := lt_of_lt_of_le (by norm_num) hy
  have hrho : rhoSq (planeι y) = r2 := rhoSq_eq_of_quarter_le hy
  have hnorm : ‖y‖ ^ 2 = r2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [r2, planeι_apply, Real.norm_eq_abs, sq_abs]
  have hu_pos : 0 < 4 * θ / r2 := div_pos (by linarith) hr2_pos
  have hglue : expNegInvGlue (4 * θ / r2) = Real.exp (-(4 * θ)⁻¹ * r2) := by
    simp only [expNegInvGlue, not_le.2 hu_pos, ↓reduceIte]
    congr 1
    field_simp [hθ.ne', hr2_pos.ne']
  have hrpow : (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) = (4 * Real.pi * θ)⁻¹ := by
    rw [show (-((2 : ℕ) : ℝ) / 2) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
  rw [UnforcedLeray.Gaussian.gaussKernel_eq_exp, hnorm, hrpow]
  unfold safeHeat2D glueInv
  rw [hrho, Polynomial.eval_X, hglue]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi, hr2_pos.ne', hθ.ne']

theorem safeHeatPair_eq_factor (q : ℝ × (ℝ × ℝ)) :
    safeHeatPair q =
      invRhoSq2 q.2 * ((16 / Real.pi) * q.1 ^ 2 * invRhoSq q.2 * glueInv3 (4 * q.1 * invRhoSq q.2)) := by
  unfold safeHeatPair safeHeat2D invRhoSq2 invRhoSq
  rw [div_eq_mul_inv (4 * q.1) (rhoSq q.2), glueInv_eq_sq_mul_glueInv3]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hR : rhoSq q.2 ≠ 0 := (rhoSq_pos q.2).ne'
  field_simp [hpi, hR]
  ring

/-! ### 2. Global `C^∞` regularity -/

theorem contDiff_rhoSq : ContDiff ℝ ∞ rhoSq := by
  unfold rhoSq
  have hsq : ContDiff ℝ ∞ (fun w : ℝ × ℝ => w.1 ^ 2 + w.2 ^ 2) :=
    (contDiff_fst.pow 2).add (contDiff_snd.pow 2)
  exact hsq.add (contDiff_const.mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul hsq))))

theorem contDiff_invRhoSq : ContDiff ℝ ∞ invRhoSq :=
  contDiff_rhoSq.inv fun w => (rhoSq_pos w).ne'

theorem contDiff_invRhoSq2 : ContDiff ℝ ∞ invRhoSq2 :=
  contDiff_invRhoSq.pow 2

theorem contDiff_glueInv : ContDiff ℝ ∞ glueInv :=
  expNegInvGlue.contDiff_polynomial_eval_inv_mul Polynomial.X

theorem contDiff_glueInv3 : ContDiff ℝ ∞ glueInv3 :=
  expNegInvGlue.contDiff_polynomial_eval_inv_mul (Polynomial.X ^ 3)

theorem contDiff_safeHeatPair : ContDiff ℝ ∞ safeHeatPair := by
  unfold safeHeatPair safeHeat2D
  have hR : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => rhoSq q.2) :=
    contDiff_rhoSq.comp contDiff_snd
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (Real.pi * rhoSq q.2)⁻¹) :=
    (contDiff_const.mul hR).inv fun q => mul_ne_zero Real.pi_pos.ne' (rhoSq_pos q.2).ne'
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => 4 * q.1 / rhoSq q.2) :=
    (contDiff_const.mul contDiff_fst).div hR fun q => (rhoSq_pos q.2).ne'
  exact h1.mul (contDiff_glueInv.comp h2)

/-! ### 3. Homogeneity bounds for `invRhoSq` and `invRhoSq2` -/

private theorem isCompact_closedDisk1 : IsCompact {w : ℝ × ℝ | w.1 ^ 2 + w.2 ^ 2 ≤ 1} := by
  refine (isCompact_closedBall (0 : ℝ × ℝ) 1).of_isClosed_subset
    (isClosed_le ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const) ?_
  intro w hw
  change w.1 ^ 2 + w.2 ^ 2 ≤ 1 at hw
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |w.1| ≤ 1 := abs_le.2 ⟨by nlinarith [sq_nonneg w.2], by nlinarith [sq_nonneg w.2]⟩
  have h2 : |w.2| ≤ 1 := abs_le.2 ⟨by nlinarith [sq_nonneg w.1], by nlinarith [sq_nonneg w.1]⟩
  exact max_le h1 h2

private theorem isCompact_unitCircle : IsCompact {w : ℝ × ℝ | w.1 ^ 2 + w.2 ^ 2 = 1} :=
  isCompact_closedDisk1.of_isClosed_subset
    (isClosed_eq ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const)
    fun _ hw => le_of_eq hw

private theorem norm_iteratedFDeriv_invRhoSq_of_quarter_lt (k : ℕ) {M : ℝ}
    (hM : ∀ u : ℝ × ℝ, u.1 ^ 2 + u.2 ^ 2 = 1 → ‖iteratedFDeriv ℝ k invRhoSq u‖ ≤ M)
    {w : ℝ × ℝ} (hw : 1 / 4 < w.1 ^ 2 + w.2 ^ 2) :
    ‖iteratedFDeriv ℝ k invRhoSq w‖ ≤ 4 * 2 ^ k * max M 0 := by
  set r : ℝ := Real.sqrt (w.1 ^ 2 + w.2 ^ 2)
  have hr_half : 1 / 2 < r := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) hw
  have hr : 0 < r := by linarith
  have hr2 : r ^ 2 = w.1 ^ 2 + w.2 ^ 2 := Real.sq_sqrt (by linarith)
  set u : ℝ × ℝ := r⁻¹ • w
  have hu : u.1 ^ 2 + u.2 ^ 2 = 1 := by
    show (r⁻¹ * w.1) ^ 2 + (r⁻¹ * w.2) ^ 2 = 1
    calc (r⁻¹ * w.1) ^ 2 + (r⁻¹ * w.2) ^ 2
        = (r ^ 2)⁻¹ * (w.1 ^ 2 + w.2 ^ 2) := by ring
      _ = (r ^ 2)⁻¹ * r ^ 2 := by rw [hr2]
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')
  have hru : r • u = w := smul_inv_smul₀ hr.ne' w
  set Nu : Set (ℝ × ℝ) :=
    {z : ℝ × ℝ | 1 / 4 < z.1 ^ 2 + z.2 ^ 2 ∧ 1 / 4 < (r • z).1 ^ 2 + (r • z).2 ^ 2}
  have hNu_open : IsOpen Nu :=
    (isOpen_lt continuous_const ((continuous_fst.pow 2).add (continuous_snd.pow 2))).inter
      (isOpen_lt continuous_const
        (((continuous_const.mul continuous_fst).pow 2).add
          ((continuous_const.mul continuous_snd).pow 2)))
  have hu_Nu : u ∈ Nu := ⟨by rw [hu]; norm_num, by rw [hru]; exact hw⟩
  have hev : (fun z : ℝ × ℝ => invRhoSq (r • z)) =ᶠ[𝓝 u]
      fun z : ℝ × ℝ => (r ^ 2)⁻¹ • invRhoSq z := by
    filter_upwards [hNu_open.mem_nhds hu_Nu] with z hz
    simp only [invRhoSq, smul_eq_mul]
    rw [rhoSq_eq_of_quarter_le hz.2.le, rhoSq_eq_of_quarter_le hz.1.le]
    show ((r * z.1) ^ 2 + (r * z.2) ^ 2)⁻¹ = (r ^ 2)⁻¹ * (z.1 ^ 2 + z.2 ^ 2)⁻¹
    rw [← mul_inv]
    congr 1
    ring
  have hev_deriv : iteratedFDeriv ℝ k (fun z : ℝ × ℝ => invRhoSq (r • z)) u =
      iteratedFDeriv ℝ k (fun z : ℝ × ℝ => (r ^ 2)⁻¹ • invRhoSq z) u :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds
  have hscale := UnforcedLeray.Kernels.iteratedFDeriv_comp_smul_right_of_ne k invRhoSq hr.ne' u
  rw [hru, hev_deriv,
    UnforcedLeray.Kernels.iteratedFDeriv_const_smul_left] at hscale
  have hnorm := congrArg norm hscale
  simp only [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (sq_nonneg r)),
    Real.norm_of_nonneg (pow_nonneg hr.le k)] at hnorm
  have heq : ‖iteratedFDeriv ℝ k invRhoSq w‖ =
      (r ^ 2)⁻¹ * (r⁻¹) ^ k * ‖iteratedFDeriv ℝ k invRhoSq u‖ := by
    have hpow : (r ^ k)⁻¹ = (r⁻¹) ^ k := (inv_pow r k).symm
    calc ‖iteratedFDeriv ℝ k invRhoSq w‖
        = (r ^ k)⁻¹ * (r ^ k * ‖iteratedFDeriv ℝ k invRhoSq w‖) := by
          rw [inv_mul_cancel_left₀ (pow_ne_zero k hr.ne')]
      _ = (r ^ k)⁻¹ * ((r ^ 2)⁻¹ * ‖iteratedFDeriv ℝ k invRhoSq u‖) := by rw [← hnorm]
      _ = (r ^ 2)⁻¹ * (r⁻¹) ^ k * ‖iteratedFDeriv ℝ k invRhoSq u‖ := by rw [hpow]; ring
  rw [heq]
  have hrinv : r⁻¹ ≤ 2 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hr_half.le
    norm_num at this
    exact this
  have hr2inv : (r ^ 2)⁻¹ ≤ 4 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) (show 1 / 4 ≤ r ^ 2 by rw [hr2]; exact hw.le)
    norm_num at this
    exact this
  have hpow_le : (r⁻¹) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (inv_nonneg.2 hr.le) hrinv k
  have hu_le : ‖iteratedFDeriv ℝ k invRhoSq u‖ ≤ max M 0 :=
    (hM u hu).trans (le_max_left M 0)
  exact mul_le_mul (mul_le_mul hr2inv hpow_le (by positivity) (by positivity))
    hu_le (norm_nonneg _) (by positivity)

private theorem norm_iteratedFDeriv_invRhoSq2_of_quarter_lt (k : ℕ) {M : ℝ}
    (hM : ∀ u : ℝ × ℝ, u.1 ^ 2 + u.2 ^ 2 = 1 → ‖iteratedFDeriv ℝ k invRhoSq2 u‖ ≤ M)
    {w : ℝ × ℝ} (hw : 1 / 4 < w.1 ^ 2 + w.2 ^ 2) :
    ‖iteratedFDeriv ℝ k invRhoSq2 w‖ ≤
      (2 ^ k * max M 0) * ((w.1 ^ 2 + w.2 ^ 2)⁻¹) ^ 2 := by
  set r : ℝ := Real.sqrt (w.1 ^ 2 + w.2 ^ 2)
  have hr_half : 1 / 2 < r := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) hw
  have hr : 0 < r := by linarith
  have hr2 : r ^ 2 = w.1 ^ 2 + w.2 ^ 2 := Real.sq_sqrt (by linarith)
  set u : ℝ × ℝ := r⁻¹ • w
  have hu : u.1 ^ 2 + u.2 ^ 2 = 1 := by
    show (r⁻¹ * w.1) ^ 2 + (r⁻¹ * w.2) ^ 2 = 1
    calc (r⁻¹ * w.1) ^ 2 + (r⁻¹ * w.2) ^ 2
        = (r ^ 2)⁻¹ * (w.1 ^ 2 + w.2 ^ 2) := by ring
      _ = (r ^ 2)⁻¹ * r ^ 2 := by rw [hr2]
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')
  have hru : r • u = w := smul_inv_smul₀ hr.ne' w
  set Nu : Set (ℝ × ℝ) :=
    {z : ℝ × ℝ | 1 / 4 < z.1 ^ 2 + z.2 ^ 2 ∧ 1 / 4 < (r • z).1 ^ 2 + (r • z).2 ^ 2}
  have hNu_open : IsOpen Nu :=
    (isOpen_lt continuous_const ((continuous_fst.pow 2).add (continuous_snd.pow 2))).inter
      (isOpen_lt continuous_const
        (((continuous_const.mul continuous_fst).pow 2).add
          ((continuous_const.mul continuous_snd).pow 2)))
  have hu_Nu : u ∈ Nu := ⟨by rw [hu]; norm_num, by rw [hru]; exact hw⟩
  have hev : (fun z : ℝ × ℝ => invRhoSq2 (r • z)) =ᶠ[𝓝 u]
      fun z : ℝ × ℝ => ((r ^ 2)⁻¹ ^ 2) • invRhoSq2 z := by
    filter_upwards [hNu_open.mem_nhds hu_Nu] with z hz
    simp only [invRhoSq2, smul_eq_mul]
    rw [rhoSq_eq_of_quarter_le hz.2.le, rhoSq_eq_of_quarter_le hz.1.le]
    show ((r * z.1) ^ 2 + (r * z.2) ^ 2)⁻¹ ^ 2 = (r ^ 2)⁻¹ ^ 2 * (z.1 ^ 2 + z.2 ^ 2)⁻¹ ^ 2
    rw [← mul_pow, ← mul_inv]
    congr 2
    ring
  have hev_deriv : iteratedFDeriv ℝ k (fun z : ℝ × ℝ => invRhoSq2 (r • z)) u =
      iteratedFDeriv ℝ k (fun z : ℝ × ℝ => ((r ^ 2)⁻¹ ^ 2) • invRhoSq2 z) u :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds
  have hscale := UnforcedLeray.Kernels.iteratedFDeriv_comp_smul_right_of_ne k invRhoSq2 hr.ne' u
  rw [hru, hev_deriv,
    UnforcedLeray.Kernels.iteratedFDeriv_const_smul_left] at hscale
  have hnorm := congrArg norm hscale
  simp only [norm_smul, Real.norm_of_nonneg (sq_nonneg (r ^ 2)⁻¹),
    Real.norm_of_nonneg (pow_nonneg hr.le k)] at hnorm
  have heq : ‖iteratedFDeriv ℝ k invRhoSq2 w‖ =
      ((r⁻¹) ^ k * ‖iteratedFDeriv ℝ k invRhoSq2 u‖) * ((w.1 ^ 2 + w.2 ^ 2)⁻¹) ^ 2 := by
    have hpow : (r ^ k)⁻¹ = (r⁻¹) ^ k := (inv_pow r k).symm
    calc ‖iteratedFDeriv ℝ k invRhoSq2 w‖
        = (r ^ k)⁻¹ * (r ^ k * ‖iteratedFDeriv ℝ k invRhoSq2 w‖) := by
          rw [inv_mul_cancel_left₀ (pow_ne_zero k hr.ne')]
      _ = (r ^ k)⁻¹ * ((r ^ 2)⁻¹ ^ 2 * ‖iteratedFDeriv ℝ k invRhoSq2 u‖) := by rw [← hnorm]
      _ = ((r⁻¹) ^ k * ‖iteratedFDeriv ℝ k invRhoSq2 u‖) * ((w.1 ^ 2 + w.2 ^ 2)⁻¹) ^ 2 := by
          rw [hpow, hr2]; ring
  rw [heq]
  have hrinv : r⁻¹ ≤ 2 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hr_half.le
    norm_num at this
    exact this
  have hpow_le : (r⁻¹) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (inv_nonneg.2 hr.le) hrinv k
  have hu_le : ‖iteratedFDeriv ℝ k invRhoSq2 u‖ ≤ max M 0 :=
    (hM u hu).trans (le_max_left M 0)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hpow_le hu_le (norm_nonneg _) (by positivity))
    (sq_nonneg _)

theorem bdd_iteratedFDeriv_invRhoSq (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ × ℝ, ‖iteratedFDeriv ℝ k invRhoSq w‖ ≤ C := by
  have hcont : Continuous (iteratedFDeriv ℝ k invRhoSq) :=
    contDiff_invRhoSq.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨M0, hM0⟩ := isCompact_closedDisk1.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨M1, hM1⟩ := isCompact_unitCircle.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max (max M0 0) (4 * 2 ^ k * max M1 0), by positivity, fun w => ?_⟩
  by_cases hw : w.1 ^ 2 + w.2 ^ 2 ≤ 1
  · exact (hM0 w hw).trans ((le_max_left M0 0).trans (le_max_left _ _))
  · have hq : 1 / 4 < w.1 ^ 2 + w.2 ^ 2 := by linarith
    exact (norm_iteratedFDeriv_invRhoSq_of_quarter_lt k (fun u hu => hM1 u hu) hq).trans
      (le_max_right _ _)

theorem bdd_iteratedFDeriv_invRhoSq2 (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ × ℝ,
      ‖iteratedFDeriv ℝ k invRhoSq2 w‖ ≤ C * ((1 + w.1 ^ 2 + w.2 ^ 2)⁻¹) ^ 2 := by
  have hcont : Continuous (iteratedFDeriv ℝ k invRhoSq2) :=
    contDiff_invRhoSq2.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨M0, hM0⟩ := isCompact_closedDisk1.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨M1, hM1⟩ := isCompact_unitCircle.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max (4 * max M0 0) (4 * (2 ^ k * max M1 0)), by positivity, fun w => ?_⟩
  set s2 : ℝ := w.1 ^ 2 + w.2 ^ 2
  have hs2_add : 1 + s2 = 1 + w.1 ^ 2 + w.2 ^ 2 := by unfold s2; ring
  have hs2_nn : 0 ≤ s2 := by positivity
  by_cases hw : s2 ≤ 1
  · have hinv : (1 / 2 : ℝ) ≤ (1 + s2)⁻¹ := by
      have := inv_anti₀ (by positivity : 0 < 1 + s2) (show 1 + s2 ≤ 2 by linarith)
      norm_num at this
      exact this
    have hsq : (1 / 4 : ℝ) ≤ ((1 + s2)⁻¹) ^ 2 := by nlinarith
    rw [← hs2_add]
    calc ‖iteratedFDeriv ℝ k invRhoSq2 w‖
        ≤ max M0 0 := (hM0 w hw).trans (le_max_left M0 0)
      _ ≤ (4 * max M0 0) * ((1 + s2)⁻¹) ^ 2 := by nlinarith [le_max_right M0 0]
      _ ≤ max (4 * max M0 0) (4 * (2 ^ k * max M1 0)) * ((1 + s2)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · have hq : 1 / 4 < s2 := by linarith
    have hs2_pos : 0 < s2 := by linarith
    have hinv : s2⁻¹ ≤ 2 * (1 + s2)⁻¹ := by
      rw [show (2 : ℝ) * (1 + s2)⁻¹ = ((1 + s2) / 2)⁻¹ by field_simp]
      exact inv_anti₀ (by linarith) (by linarith)
    have hsq : (s2⁻¹) ^ 2 ≤ 4 * ((1 + s2)⁻¹) ^ 2 := by
      have h1 : 0 ≤ s2⁻¹ := inv_nonneg.2 hs2_nn
      nlinarith
    have hhom := norm_iteratedFDeriv_invRhoSq2_of_quarter_lt k (fun u hu => hM1 u hu) hq
    rw [← hs2_add]
    calc ‖iteratedFDeriv ℝ k invRhoSq2 w‖
        ≤ (2 ^ k * max M1 0) * (s2⁻¹) ^ 2 := hhom
      _ ≤ (2 ^ k * max M1 0) * (4 * ((1 + s2)⁻¹) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (4 * (2 ^ k * max M1 0)) * ((1 + s2)⁻¹) ^ 2 := by ring
      _ ≤ max (4 * max M0 0) (4 * (2 ^ k * max M1 0)) * ((1 + s2)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

/-! ### 4. Leibniz and Faà di Bruno bounds on `{q | |q.1| ≤ T}` -/

private def HasUniformBdd (S : Set (ℝ × (ℝ × ℝ))) (f : ℝ × (ℝ × ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ S, ‖iteratedFDeriv ℝ n f q‖ ≤ C

private def HasWeightedBdd (S : Set (ℝ × (ℝ × ℝ))) (wt f : ℝ × (ℝ × ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ S, ‖iteratedFDeriv ℝ n f q‖ ≤ C * wt q

private theorem norm_iteratedFDeriv_comp_clm_of_le_one {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) {f : F → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg L) hL)

private theorem hasUniformBdd_mul {S : Set (ℝ × (ℝ × ℝ))} {f g : ℝ × (ℝ × ℝ) → ℝ}
    (hf : HasUniformBdd S f) (hg : HasUniformBdd S g) :
    HasUniformBdd S (fun q => f q * g q) := by
  refine ⟨hf.1.mul hg.1, fun n => ?_⟩
  choose A hA0 hA using hf.2
  choose B hB0 hB using hg.2
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * B (n - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA0 i)) (hB0 _),
    fun q hq => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hf.1 hg.1 q (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := hA i q hq
  have h2 := hB (n - i) q hq
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA0 i))

private theorem hasWeightedBdd_mul_uniform {S : Set (ℝ × (ℝ × ℝ))} {wt f g : ℝ × (ℝ × ℝ) → ℝ}
    (hwt : ∀ q ∈ S, 0 ≤ wt q) (hf : HasWeightedBdd S wt f) (hg : HasUniformBdd S g) :
    HasWeightedBdd S wt (fun q => f q * g q) := by
  refine ⟨hf.1.mul hg.1, fun n => ?_⟩
  choose A hA0 hA using hf.2
  choose B hB0 hB using hg.2
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * B (n - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA0 i)) (hB0 _),
    fun q hq => ?_⟩
  rw [Finset.sum_mul]
  refine (norm_iteratedFDeriv_mul_le hf.1 hg.1 q (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := hA i q hq
  have h2 := hB (n - i) q hq
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f q‖ * ‖iteratedFDeriv ℝ (n - i) g q‖
      ≤ (n.choose i : ℝ) * (A i * wt q) * B (n - i) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA0 i) (hwt q hq)))
    _ = (n.choose i : ℝ) * A i * B (n - i) * wt q := by ring

private theorem hasUniformBdd_comp_fst (T : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    HasUniformBdd {q : ℝ × (ℝ × ℝ) | |q.1| ≤ T} (fun q => g q.1) := by
  set L := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  have hL : ‖L‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by rw [one_mul]; exact norm_fst_le q
  refine ⟨hg.comp contDiff_fst, fun n => ?_⟩
  have hcont : Continuous (iteratedFDeriv ℝ n g) :=
    hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M 0, le_max_right M 0, fun q hq => ?_⟩
  have hqIcc : q.1 ∈ Icc (-T) T := abs_le.1 hq
  exact (norm_iteratedFDeriv_comp_clm_of_le_one L hL hg n q).trans
    ((hM q.1 hqIcc).trans (le_max_left M 0))

private theorem hasUniformBdd_invRhoSq_snd (S : Set (ℝ × (ℝ × ℝ))) :
    HasUniformBdd S (fun q => invRhoSq q.2) := by
  set L := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)
  have hL : ‖L‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by rw [one_mul]; exact norm_snd_le q
  refine ⟨contDiff_invRhoSq.comp contDiff_snd, fun n => ?_⟩
  obtain ⟨C, hC0, hC⟩ := bdd_iteratedFDeriv_invRhoSq n
  exact ⟨C, hC0, fun q _ => (norm_iteratedFDeriv_comp_clm_of_le_one L hL contDiff_invRhoSq n q).trans
    (hC q.2)⟩

private theorem hasWeightedBdd_invRhoSq2_snd (S : Set (ℝ × (ℝ × ℝ))) :
    HasWeightedBdd S (fun q => ((1 + q.2.1 ^ 2 + q.2.2 ^ 2)⁻¹) ^ 2) (fun q => invRhoSq2 q.2) := by
  set L := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)
  have hL : ‖L‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by rw [one_mul]; exact norm_snd_le q
  refine ⟨contDiff_invRhoSq2.comp contDiff_snd, fun n => ?_⟩
  obtain ⟨C, hC0, hC⟩ := bdd_iteratedFDeriv_invRhoSq2 n
  exact ⟨C, hC0, fun q _ =>
    (norm_iteratedFDeriv_comp_clm_of_le_one L hL contDiff_invRhoSq2 n q).trans (hC q.2)⟩

private theorem hasUniformBdd_comp_oneDim {S : Set (ℝ × (ℝ × ℝ))} {U : ℝ}
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {f : ℝ × (ℝ × ℝ) → ℝ} (hf : HasUniformBdd S f)
    (hrange : ∀ q ∈ S, |f q| ≤ U) :
    HasUniformBdd S (fun q => g (f q)) := by
  refine ⟨hg.comp hf.1, fun n => ?_⟩
  choose A hA0 hA using hf.2
  have hB_ex : ∀ i : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc (-U) U, ‖iteratedFDeriv ℝ i g u‖ ≤ M := by
    intro i
    have hcont : Continuous (iteratedFDeriv ℝ i g) :=
      hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := -U) (b := U)).exists_bound_of_continuousOn
      hcont.continuousOn
    exact ⟨max M 0, le_max_right M 0, fun u hu => (hM u hu).trans (le_max_left M 0)⟩
  choose B hB0 hB using hB_ex
  set C : ℝ := (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ n)⟩ B
  set D : ℝ := max 1 ((Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ n)⟩ A)
  have hC0 : 0 ≤ C := (hB0 0).trans (Finset.le_sup' B (Finset.mem_range.2 (Nat.zero_lt_succ n)))
  have hD1 : 1 ≤ D := le_max_left 1 _
  refine ⟨(n ! : ℝ) * C * D ^ n, by positivity, fun q hq => ?_⟩
  have hfq : f q ∈ Icc (-U) U := abs_le.1 (hrange q hq)
  refine norm_iteratedFDeriv_comp_le hg hf.1 (by exact_mod_cast le_top) q
    (fun i hi => (hB i (f q) hfq).trans
      (Finset.le_sup' B (Finset.mem_range.2 (Nat.lt_succ_of_le hi))))
    (fun i hi1 hi => ?_)
  have hAi : A i ≤ D :=
    (Finset.le_sup' A (Finset.mem_range.2 (Nat.lt_succ_of_le hi))).trans (le_max_right 1 _)
  exact (hA i q hq).trans (hAi.trans (le_self_pow₀ hD1 (by omega)))

theorem norm_iteratedFDeriv_safeHeatPair_le (n : ℕ) (T : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℝ × (ℝ × ℝ), |q.1| ≤ T →
      ‖iteratedFDeriv ℝ n safeHeatPair q‖ ≤ K * ((1 + q.2.1 ^ 2 + q.2.2 ^ 2)⁻¹) ^ 2 := by
  set T' : ℝ := max T 0
  set S : Set (ℝ × (ℝ × ℝ)) := {q : ℝ × (ℝ × ℝ) | |q.1| ≤ T'}
  have h4fst : HasUniformBdd S (fun q => 4 * q.1) :=
    hasUniformBdd_comp_fst T' (contDiff_const.mul contDiff_id)
  have hinv1 : HasUniformBdd S (fun q => invRhoSq q.2) := hasUniformBdd_invRhoSq_snd S
  have harg : HasUniformBdd S (fun q => (4 * q.1) * invRhoSq q.2) :=
    hasUniformBdd_mul h4fst hinv1
  have harg_bd : ∀ q ∈ S, |(4 * q.1) * invRhoSq q.2| ≤ 32 * T' := by
    intro q hq
    have hq' : |q.1| ≤ T' := hq
    rw [abs_mul, abs_mul, show |(4 : ℝ)| = 4 by norm_num,
      abs_of_pos (invRhoSq_pos q.2)]
    have h8 := invRhoSq_le_eight q.2
    nlinarith [abs_nonneg q.1]
  have hglue : HasUniformBdd S (fun q => glueInv3 ((4 * q.1) * invRhoSq q.2)) :=
    hasUniformBdd_comp_oneDim contDiff_glueInv3 harg harg_bd
  have h16sq : HasUniformBdd S (fun q => (16 / Real.pi) * q.1 ^ 2) :=
    hasUniformBdd_comp_fst T' (contDiff_const.mul (contDiff_id.pow 2))
  have htail : HasUniformBdd S
      (fun q => (16 / Real.pi) * q.1 ^ 2 * invRhoSq q.2 * glueInv3 ((4 * q.1) * invRhoSq q.2)) :=
    hasUniformBdd_mul (hasUniformBdd_mul h16sq hinv1) hglue
  have hhead : HasWeightedBdd S (fun q => ((1 + q.2.1 ^ 2 + q.2.2 ^ 2)⁻¹) ^ 2)
      (fun q => invRhoSq2 q.2) :=
    hasWeightedBdd_invRhoSq2_snd S
  have hprod := hasWeightedBdd_mul_uniform (fun _ _ => sq_nonneg _) hhead htail
  have hpair_eq : safeHeatPair = fun q => invRhoSq2 q.2 *
      ((16 / Real.pi) * q.1 ^ 2 * invRhoSq q.2 * glueInv3 ((4 * q.1) * invRhoSq q.2)) :=
    funext safeHeatPair_eq_factor
  rw [hpair_eq]
  obtain ⟨K, hK0, hK⟩ := hprod.2 n
  exact ⟨K, hK0, fun q hq => hK q (hq.trans (le_max_left T 0))⟩

/-! ### 5. Profile-level smoothness, parameter continuity, and decay bound -/

def heatArgCLM (ν : ℝ) : Profile →L[ℝ] ℝ × (ℝ × ℝ) :=
  ((-ν) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

theorem safeHeatProfile_eq_comp (ν τ : ℝ) (z : ℝ × ℝ) :
    safeHeatProfile ν τ z =
      (fun q : ℝ × (ℝ × ℝ) => safeHeatPair ((ν * τ, -z) + q)) ∘ heatArgCLM ν := by
  funext p
  simp only [safeHeatProfile, safeHeatPair, Function.comp_apply, heatArgCLM,
    ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, Prod.mk_add_mk]
  congr 1
  · ring
  · exact sub_eq_neg_add p.2 z

theorem contDiff_safeHeatProfile (ν τ : ℝ) (z : ℝ × ℝ) :
    ContDiff ℝ ∞ (safeHeatProfile ν τ z) := by
  rw [safeHeatProfile_eq_comp]
  exact (contDiff_safeHeatPair.comp (contDiff_const.add contDiff_id)).comp
    (heatArgCLM ν).contDiff

theorem iteratedFDeriv_safeHeatProfile_eq (ν τ : ℝ) (z : ℝ × ℝ) (n : ℕ) (p : Profile) :
    iteratedFDeriv ℝ n (safeHeatProfile ν τ z) p =
      (iteratedFDeriv ℝ n safeHeatPair (ν * (τ - p.1), p.2 - z)).compContinuousLinearMap
        fun _ => heatArgCLM ν := by
  have hshift : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => safeHeatPair ((ν * τ, -z) + q)) :=
    contDiff_safeHeatPair.comp (contDiff_const.add contDiff_id)
  rw [safeHeatProfile_eq_comp,
    (heatArgCLM ν).iteratedFDeriv_comp_right hshift p (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left n (ν * τ, -z) (heatArgCLM ν p)]
  congr 2
  simp only [heatArgCLM, ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, Prod.mk_add_mk]
  ext <;> simp <;> ring

theorem continuous_iteratedFDeriv_safeHeatProfile (ν : ℝ) (n : ℕ) (p : Profile) :
    Continuous (fun a : ℝ × (ℝ × ℝ) => iteratedFDeriv ℝ n (safeHeatProfile ν a.1 a.2) p) := by
  have hrew : (fun a : ℝ × (ℝ × ℝ) => iteratedFDeriv ℝ n (safeHeatProfile ν a.1 a.2) p) =
      fun a => ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ)
        (fun _ : Fin n => heatArgCLM ν)
        (iteratedFDeriv ℝ n safeHeatPair (ν * (a.1 - p.1), p.2 - a.2)) := by
    funext a
    exact iteratedFDeriv_safeHeatProfile_eq ν a.1 a.2 n p
  rw [hrew]
  refine (ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ)
    (fun _ : Fin n => heatArgCLM ν)).continuous.comp ?_
  refine (contDiff_safeHeatPair.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp ?_
  exact (continuous_const.mul (continuous_fst.sub continuous_const)).prodMk
    (continuous_const.sub continuous_snd)

theorem norm_iteratedFDeriv_safeHeatProfile_le (ν : ℝ) (n : ℕ) (T : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℝ) (z : ℝ × ℝ) (p : Profile),
      |ν * (τ - p.1)| ≤ T →
      ‖iteratedFDeriv ℝ n (safeHeatProfile ν τ z) p‖ ≤
        K * ((1 + (p.2.1 - z.1) ^ 2 + (p.2.2 - z.2) ^ 2)⁻¹) ^ 2 := by
  obtain ⟨K0, hK0_nn, hK0⟩ := norm_iteratedFDeriv_safeHeatPair_le n T
  refine ⟨K0 * ‖heatArgCLM ν‖ ^ n, by positivity, fun τ z p hT => ?_⟩
  rw [iteratedFDeriv_safeHeatProfile_eq]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ‖iteratedFDeriv ℝ n safeHeatPair (ν * (τ - p.1), p.2 - z)‖ * ‖heatArgCLM ν‖ ^ n
      ≤ (K0 * ((1 + (p.2.1 - z.1) ^ 2 + (p.2.2 - z.2) ^ 2)⁻¹) ^ 2) * ‖heatArgCLM ν‖ ^ n :=
        mul_le_mul_of_nonneg_right (hK0 (ν * (τ - p.1), p.2 - z) hT) (by positivity)
    _ = (K0 * ‖heatArgCLM ν‖ ^ n) * ((1 + (p.2.1 - z.1) ^ 2 + (p.2.2 - z.2) ^ 2)⁻¹) ^ 2 := by
        ring

end UnforcedLeray.Short.PartIIa.FlatAdjointSmoothAux
