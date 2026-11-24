import UnforcedLeray.Short.PartI.Sub.PartI_T23_2
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansion.RemainderLpBound.StreamDuhamel
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ExpPowAbsorb
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# `PartI:T23/2/3`: Weighted Pointwise Taylor Remainder Bound for `meanSourceRemainder`

Proves `TrainMeanSourceRemainderBound` (`Sub/PartI_T23_2.lean`), the inhomogeneous source Duhamel
Taylor remainder bound for the 1D heat Duhamel expansion of `meanStream`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set ContDiff
open scoped Topology ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (width)

namespace SourceRemainderBound

/-! ### 1. 1D derivative-sequence helpers, unit-interval Taylor bound, and heat-kernel identities -/

private theorem iteratedDeriv_eq_of_hasDerivAt_seq {U : Set ℝ} (hU : IsOpen U)
    (g : ℕ → ℝ → ℝ) (hd : ∀ k : ℕ, ∀ y ∈ U, HasDerivAt (g k) (g (k + 1) y) y) :
    (∀ k : ℕ, ∀ y ∈ U, iteratedDeriv k (g 0) y = g k y) ∧
      (∀ k : ℕ, ContDiffOn ℝ ∞ (g k) U) := by
  have hiter : ∀ k : ℕ, ∀ y ∈ U, iteratedDeriv k (g 0) y = g k y := by
    intro k
    induction k with
    | zero => intro y _; rfl
    | succ k ih =>
      intro y hy
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (g 0) =ᶠ[𝓝 y] g k := by
        filter_upwards [hU.mem_nhds hy] with z hz using ih z hz
      rw [hev.deriv_eq, (hd k y hy).deriv]
  have hcd_nat : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ n (g k) U := by
    intro n
    induction n with
    | zero =>
      intro k
      exact contDiffOn_zero.2 fun y hy => (hd k y hy).continuousAt.continuousWithinAt
    | succ n ih =>
      intro k
      push_cast
      rw [contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun y hy => (hd k y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact (ih (k + 1)).congr fun y hy => (hd k y hy).deriv
  exact ⟨hiter, fun k => contDiffOn_infty.2 fun n => hcd_nat n k⟩

private theorem iteratedDeriv_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ → ℝ) (k : ℕ) (x : ℝ)
    (hf : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) :
    iteratedDeriv k (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, iteratedDeriv k (f i) x := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    have h1 : (fun y => ∑ i ∈ insert a s, f i y) =
        (f a) + (fun y => ∑ i ∈ s, f i y) := by
      funext y
      exact Finset.sum_insert ha
    have hsum_cd : ContDiffAt ℝ ∞ (fun y => ∑ i ∈ s, f i y) x :=
      ContDiffAt.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [h1, iteratedDeriv_add
      ((hf a (Finset.mem_insert_self a s)).of_le (by exact_mod_cast le_top))
      (hsum_cd.of_le (by exact_mod_cast le_top)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]

private theorem contDiff_heatKernel1 (a : ℝ) : ContDiff ℝ ∞ (heatKernel1 a) := by
  unfold heatKernel1
  fun_prop

private theorem contDiff_iteratedDeriv (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ∀ k : ℕ, ContDiff ℝ ∞ (iteratedDeriv k φ)
  | 0 => by rw [iteratedDeriv_zero]; exact hφ
  | k + 1 => by
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp (contDiff_iteratedDeriv φ hφ k)).2

private theorem iteratedDeriv_comp_iteratedDeriv (φ : ℝ → ℝ) (b m : ℕ) (x : ℝ) :
    iteratedDeriv b (iteratedDeriv m φ) x = iteratedDeriv (b + m) φ x := by
  induction b generalizing x with
  | zero => simp
  | succ b ih =>
    have hfun : iteratedDeriv b (iteratedDeriv m φ) = iteratedDeriv (b + m) φ := funext ih
    rw [iteratedDeriv_succ, hfun, show b + 1 + m = (b + m) + 1 by omega, iteratedDeriv_succ]

/-- Lagrange Taylor remainder bound on the unit interval `Icc 0 1` for a derivative sequence
`g : ℕ → ℝ → ℝ` defined on `Ioo (-1 / 2) (3 / 2)`. -/
private theorem taylor_unit_interval_bound (g : ℕ → ℝ → ℝ) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hd : ∀ k : ℕ, ∀ θ ∈ Ioo (-1 / 2 : ℝ) (3 / 2), HasDerivAt (g k) (g (k + 1) θ) θ)
    (hbd : ∀ θ ∈ Icc (0 : ℝ) 1, |g (n + 1) θ| ≤ M) :
    |g 0 1 - ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ)⁻¹ * g k 0| ≤ M := by
  obtain ⟨hiter, hcd⟩ := iteratedDeriv_eq_of_hasDerivAt_seq isOpen_Ioo g hd
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-1 / 2 : ℝ) (3 / 2) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hcd_on : ContDiffOn ℝ (n + 1) (g 0) (Icc 0 1) :=
    ((hcd 0).mono hsub).of_le (by exact_mod_cast le_top)
  have hcd_at : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ (g 0) θ :=
    fun θ hθ => (hcd 0).contDiffAt (isOpen_Ioo.mem_nhds (hsub hθ))
  have hN1_bd : ∀ θ ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (n + 1) (g 0) (Icc 0 1) θ‖ ≤ M := by
    intro θ hθ
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hcd_at θ hθ).of_le (by exact_mod_cast le_top)) hθ,
      hiter (n + 1) θ (hsub hθ), Real.norm_eq_abs]
    exact hbd θ hθ
  have htaylor := taylor_mean_remainder_bound (f := g 0) (x := 1) zero_le_one
    hcd_on ⟨zero_le_one, le_rfl⟩ hN1_bd
  have heval : taylorWithinEval (g 0) n (Icc 0 1) 0 1 =
      ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ)⁻¹ * g k 0 := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hcd_at 0 ⟨le_rfl, zero_le_one⟩).of_le (by exact_mod_cast le_top))
      ⟨le_rfl, zero_le_one⟩, hiter k 0 (hsub ⟨le_rfl, zero_le_one⟩),
      sub_zero, one_pow, mul_one]
  rw [heval, Real.norm_eq_abs, sub_zero, one_pow, mul_one] at htaylor
  have hfact_ge1 : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  exact htaylor.trans (div_le_self hM hfact_ge1)

private def G1_deriv (k : ℕ) : ℝ → ℝ :=
  iteratedDeriv k (heatKernel1 1)

private theorem contDiff_G1_deriv (k : ℕ) : ContDiff ℝ ∞ (G1_deriv k) :=
  contDiff_iteratedDeriv (heatKernel1 1) (contDiff_heatKernel1 1) k

private theorem hasDerivAt_G1_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (G1_deriv k) (G1_deriv (k + 1) x) x := by
  have hd : DifferentiableAt ℝ (G1_deriv k) x :=
    (contDiff_G1_deriv k).differentiable (by simp) x
  have h := hd.hasDerivAt
  unfold G1_deriv at h ⊢
  rwa [← iteratedDeriv_succ] at h

private theorem hasDerivAt_heatKernel1_one (x : ℝ) :
    HasDerivAt (heatKernel1 1) (-(x / 2) * heatKernel1 1 x) x := by
  unfold heatKernel1
  have h1 : HasDerivAt (fun z : ℝ => -(z ^ 2) / (4 * 1)) (-(2 * x) / 4) x := by
    have h := (((hasDerivAt_id' x).pow 2).neg).div_const (4 * 1)
    refine h.congr_deriv ?_
    ring
  refine (h1.exp.const_mul (Real.sqrt (4 * Real.pi * 1))⁻¹).congr_deriv ?_
  ring

private theorem G1_deriv_one (x : ℝ) :
    G1_deriv 1 x = -(x / 2) * G1_deriv 0 x := by
  dsimp [G1_deriv]
  rw [iteratedDeriv_one, iteratedDeriv_zero, (hasDerivAt_heatKernel1_one x).deriv]

private theorem G1_deriv_succ_succ (k : ℕ) (x : ℝ) :
    G1_deriv (k + 2) x =
      -(((k : ℝ) + 1) / 2) * G1_deriv k x - (x / 2) * G1_deriv (k + 1) x := by
  induction k generalizing x with
  | zero =>
    have h1 : HasDerivAt (G1_deriv 1)
        (-(1 / 2) * G1_deriv 0 x - (x / 2) * G1_deriv 1 x) x := by
      have hlin : HasDerivAt (fun z : ℝ => -(z / 2)) (-(1 / 2)) x :=
        ((hasDerivAt_id' x).div_const 2).neg
      have hprod := (hlin.mul (hasDerivAt_G1_deriv 0 x)).congr_of_eventuallyEq
        (Eventually.of_forall fun z => G1_deriv_one z)
      refine hprod.congr_deriv ?_
      ring
    have h2 := (hasDerivAt_G1_deriv 1 x).unique h1
    rw [h2]
    push_cast
    ring
  | succ k ih =>
    have h1 : HasDerivAt (G1_deriv (k + 2))
        (-(((k : ℝ) + 1 + 1) / 2) * G1_deriv (k + 1) x -
          (x / 2) * G1_deriv (k + 2) x) x := by
      have hterm1 := (hasDerivAt_G1_deriv k x).const_mul (-(((k : ℝ) + 1) / 2))
      have hlin : HasDerivAt (fun z : ℝ => z / 2) (1 / 2) x :=
        (hasDerivAt_id' x).div_const 2
      have hterm2 := hlin.mul (hasDerivAt_G1_deriv (k + 1) x)
      have hsub := (hterm1.sub hterm2).congr_of_eventuallyEq
        (Eventually.of_forall fun z => ih z)
      refine hsub.congr_deriv ?_
      ring
    have h2 := (hasDerivAt_G1_deriv (k + 2) x).unique h1
    rw [h2]
    push_cast
    ring

private theorem iteratedDeriv_heatKernel1_scale {a : ℝ} (ha : 0 < a) (k : ℕ) (y : ℝ) :
    iteratedDeriv k (heatKernel1 a) y =
      ((Real.sqrt a)⁻¹) ^ (k + 1) * G1_deriv k ((Real.sqrt a)⁻¹ * y) := by
  have hfun : heatKernel1 a =
      fun e : ℝ => (Real.sqrt a)⁻¹ * heatKernel1 1 ((Real.sqrt a)⁻¹ * e) := by
    funext e
    simpa [mul_one] using PartI_T23.heatKernel1_nu_scale ha 1 e
  rw [hfun, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul ((contDiff_heatKernel1 1).of_le (by exact_mod_cast le_top)),
    pow_succ']
  dsimp [G1_deriv]
  ring

private theorem hasDerivAt_iteratedDeriv_heatKernel1_width {a : ℝ} (ha : 0 < a) (k : ℕ) (y : ℝ) :
    HasDerivAt (fun a' => iteratedDeriv k (heatKernel1 a') y)
      (iteratedDeriv (k + 2) (heatKernel1 a) y) a := by
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hg : HasDerivAt (fun a' : ℝ => (Real.sqrt a')⁻¹) (-((Real.sqrt a)⁻¹) ^ 3 / 2) a := by
    have h := (Real.hasDerivAt_sqrt ha.ne').inv hsq.ne'
    refine h.congr_deriv ?_
    field_simp
  have hx : HasDerivAt (fun a' : ℝ => (Real.sqrt a')⁻¹ * y)
      ((-((Real.sqrt a)⁻¹) ^ 3 / 2) * y) a := hg.mul_const y
  have hpow : HasDerivAt (fun a' : ℝ => ((Real.sqrt a')⁻¹) ^ (k + 1))
      (((k : ℝ) + 1) * ((Real.sqrt a)⁻¹) ^ k * (-((Real.sqrt a)⁻¹) ^ 3 / 2)) a := by
    refine (hg.pow (k + 1)).congr_deriv ?_
    push_cast
    ring
  have hG : HasDerivAt (fun a' : ℝ => G1_deriv k ((Real.sqrt a')⁻¹ * y))
      (G1_deriv (k + 1) ((Real.sqrt a)⁻¹ * y) * ((-((Real.sqrt a)⁻¹) ^ 3 / 2) * y)) a :=
    (hasDerivAt_G1_deriv k ((Real.sqrt a)⁻¹ * y)).comp a hx
  have hprod := hpow.mul hG
  have hev : (fun a' : ℝ => ((Real.sqrt a')⁻¹) ^ (k + 1) * G1_deriv k ((Real.sqrt a')⁻¹ * y))
      =ᶠ[𝓝 a] (fun a' : ℝ => iteratedDeriv k (heatKernel1 a') y) := by
    filter_upwards [Ioi_mem_nhds ha] with a' ha'
    exact (iteratedDeriv_heatKernel1_scale ha' k y).symm
  refine (hprod.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  rw [iteratedDeriv_heatKernel1_scale ha (k + 2) y, G1_deriv_succ_succ k ((Real.sqrt a)⁻¹ * y)]
  ring

private theorem hasDerivAt_iteratedDeriv_heatKernel1_space (a : ℝ) (k : ℕ) (η ξ c_mul : ℝ) :
    HasDerivAt (fun θ : ℝ => iteratedDeriv k (heatKernel1 a) (η - c_mul * θ))
      (-c_mul * iteratedDeriv (k + 1) (heatKernel1 a) (η - c_mul * ξ)) ξ := by
  have hd : DifferentiableAt ℝ (iteratedDeriv k (heatKernel1 a)) (η - c_mul * ξ) :=
    (contDiff_iteratedDeriv (heatKernel1 a) (contDiff_heatKernel1 a) k).differentiable (by simp) _
  have h1 := hd.hasDerivAt
  rw [← iteratedDeriv_succ] at h1
  have hlin : HasDerivAt (fun θ : ℝ => η - c_mul * θ) (-c_mul) ξ := by
    exact (((hasDerivAt_id' ξ).const_mul c_mul).const_sub η).congr_deriv (by ring)
  refine (h1.comp ξ hlin).congr_deriv ?_
  ring

/-! ### 2. Weight inequalities and heat-kernel band bounds -/

/-- For `θ ∈ Icc 0 1` and `η, ξ : ℝ`, `|η| ≤ (1 + |η - θ * ξ|) * (1 + |ξ|)`. -/
private theorem abs_le_one_add_sub_mul_one_add {η ξ θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    |η| ≤ (1 + |η - θ * ξ|) * (1 + |ξ|) := by
  have h1 : |η| ≤ |η - θ * ξ| + |θ * ξ| := by
    simpa [sub_add_cancel] using abs_add_le (η - θ * ξ) (θ * ξ)
  have h2 : |θ * ξ| ≤ |ξ| := by
    rw [abs_mul, abs_of_nonneg hθ.1]
    exact mul_le_of_le_one_left (abs_nonneg ξ) hθ.2
  nlinarith [abs_nonneg (η - θ * ξ), abs_nonneg ξ]

private theorem pow_abs_le_one_add_sub_mul_one_add (m : ℕ) {η ξ θ : ℝ}
    (hθ : θ ∈ Icc (0 : ℝ) 1) :
    |η| ^ m ≤ (1 + |η - θ * ξ|) ^ m * (1 + |ξ|) ^ m := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg η) (abs_le_one_add_sub_mul_one_add hθ) m

/-- For all `ξ : ℝ` and `m, r : ℕ` with `2 * r ≤ 2 * N + 2`,
`ξ ^ (2 * r) * (1 + |ξ|) ^ m ≤ 2 ^ m * (1 + ξ ^ 2) ^ (m + N + 1)`. -/
private theorem pow_mul_one_add_abs_le_jap (m N r : ℕ) (hr : r ≤ N + 1) (ξ : ℝ) :
    |ξ| ^ (2 * r) * (1 + |ξ|) ^ m ≤ (2 : ℝ) ^ m * (1 + ξ ^ 2) ^ (m + N + 1) := by
  have h1 : 1 + |ξ| ≤ 2 * (1 + ξ ^ 2) := by
    nlinarith [sq_nonneg (|ξ| - 1), sq_abs ξ]
  have h1_pow : (1 + |ξ|) ^ m ≤ (2 : ℝ) ^ m * (1 + ξ ^ 2) ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 m
  have h2 : |ξ| ^ (2 * r) ≤ (1 + ξ ^ 2) ^ (N + 1) := by
    calc |ξ| ^ (2 * r) = (|ξ| ^ 2) ^ r := by rw [pow_mul]
      _ = (ξ ^ 2) ^ r := by rw [sq_abs]
      _ ≤ (1 + ξ ^ 2) ^ r := pow_le_pow_left₀ (sq_nonneg ξ) (by linarith) r
      _ ≤ (1 + ξ ^ 2) ^ (N + 1) := pow_le_pow_right₀ (by linarith [sq_nonneg ξ]) hr
  calc |ξ| ^ (2 * r) * (1 + |ξ|) ^ m
      ≤ (1 + ξ ^ 2) ^ (N + 1) * ((2 : ℝ) ^ m * (1 + ξ ^ 2) ^ m) :=
        mul_le_mul h2 h1_pow (by positivity) (by positivity)
    _ = (2 : ℝ) ^ m * (1 + ξ ^ 2) ^ (m + N + 1) := by
        rw [show m + N + 1 = (N + 1) + m by omega, pow_add]
        ring

/-- Uniform bound on `|G1_deriv k x|` for all `x ∈ ℝ`. -/
private theorem abs_G1_deriv_le (k : ℕ) :
    ∃ C_k : ℝ, 0 < C_k ∧ ∀ x : ℝ, |G1_deriv k x| ≤ C_k := by
  obtain ⟨D, hD_pos, hD⟩ := PartI_T23.heatKernel1_weighted_jet_bound 0 k 0
  refine ⟨polyP D (k + 1) 1 0, by unfold polyP; positivity, fun x => ?_⟩
  have h := hD one_pos le_rfl le_rfl le_rfl x
  simp only [pow_zero, one_mul, one_mul, iteratedDeriv_zero, Real.one_rpow, mul_one] at h
  exact h

/-- Uniform bound on `|iteratedDeriv k (heatKernel1 a) y|` for `a ≥ a_min > 0` and `y ∈ ℝ`. -/
private theorem abs_iteratedDeriv_heatKernel1_le_of_ge (k : ℕ) :
    ∃ C_k : ℝ, 0 < C_k ∧ ∀ {a_min a : ℝ}, 0 < a_min → a_min ≤ a → ∀ y : ℝ,
      |iteratedDeriv k (heatKernel1 a) y| ≤ ((Real.sqrt a_min)⁻¹) ^ (k + 1) * C_k := by
  obtain ⟨C_k, hC_pos, hC⟩ := abs_G1_deriv_le k
  refine ⟨C_k, hC_pos, fun {a_min a} hamin ha y => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le hamin ha
  rw [iteratedDeriv_heatKernel1_scale ha0 k y, abs_mul,
    abs_of_pos (pow_pos (inv_pos.2 (Real.sqrt_pos.2 ha0)) (k + 1))]
  have hsq : (Real.sqrt a)⁻¹ ≤ (Real.sqrt a_min)⁻¹ :=
    inv_le_inv₀ (Real.sqrt_pos.2 ha0) (Real.sqrt_pos.2 hamin) |>.2 (Real.sqrt_le_sqrt ha)
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) hsq (k + 1)) (hC _) (abs_nonneg _) (by positivity)

/-- Weighted bound on `iteratedDeriv B (heatKernel1 a) (η - θ * ξ)` for `a ∈ [ν * (s / 2), ν * s]`,
`0 < ν ≤ 1`, `c ≥ 0`, `s ≥ 1`, `θ ∈ [0, 1]`. -/
private theorem heatKernel1_band_bound (m B : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {ν c s a : ℝ}, 0 < ν → ν ≤ 1 → 0 ≤ c → 1 ≤ s →
      a ∈ Icc (ν * (s / 2)) (ν * s) → ∀ (η ξ : ℝ) {θ : ℝ}, θ ∈ Icc (0 : ℝ) 1 →
        |η| ^ m * |iteratedDeriv B (heatKernel1 a) (η - θ * ξ)| ≤
          (1 + |ξ|) ^ m *
            (polyP D (B + 1) ν c * s ^ (((m : ℝ) - B - 1) / 2)) := by
  obtain ⟨D₀, hD₀_pos, hD₀⟩ := PartI_T23.heatKernel1_weighted_jet_bound m B 0
  refine ⟨(2 : ℝ) ^ (B + 1 + m) * D₀, by positivity, ?_⟩
  intro ν c s a hν hν1 hc hs ha η ξ θ hθ
  set ν' : ℝ := ν / 2
  set s' : ℝ := 2 * a / ν
  have hν'_pos : 0 < ν' := by dsimp [ν']; positivity
  have hν'_le1 : ν' ≤ 1 := by dsimp [ν']; linarith
  have hs_le_s' : s ≤ s' := by
    dsimp [s']
    rw [le_div_iff₀ hν]
    linarith [ha.1]
  have hs'_le_2s : s' ≤ 2 * s := by
    dsimp [s']
    rw [div_le_iff₀ hν]
    linarith [ha.2]
  have hs'1 : 1 ≤ s' := hs.trans hs_le_s'
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hs'0 : 0 < s' := lt_of_lt_of_le one_pos hs'1
  have hwidth : ν' * s' = a := by
    dsimp [ν', s']
    field_simp [hν.ne']
  have hjet := hD₀ hν'_pos hν'_le1 hc hs'1 (η - θ * ξ)
  simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hjet
  rw [hwidth] at hjet
  set α : ℝ := ((m : ℝ) - B - 1) / 2
  have hα_le_m : α ≤ (m : ℝ) := by
    dsimp [α]
    have : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hrpow : (s') ^ α ≤ (2 : ℝ) ^ m * s ^ α := by
    rcases le_or_gt α 0 with hα0 | hα0
    · have h1 : (s') ^ α ≤ s ^ α := Real.rpow_le_rpow_of_nonpos hs0 hs_le_s' hα0
      have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      exact h1.trans (le_mul_of_one_le_left (Real.rpow_nonneg hs0.le _) h2m)
    · calc (s') ^ α
          ≤ (2 * s) ^ α := Real.rpow_le_rpow hs'0.le hs'_le_2s hα0.le
        _ = (2 : ℝ) ^ α * s ^ α := Real.mul_rpow two_pos.le hs0.le
        _ ≤ (2 : ℝ) ^ (m : ℝ) * s ^ α :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_le (by norm_num) hα_le_m)
              (Real.rpow_nonneg hs0.le _)
        _ = (2 : ℝ) ^ m * s ^ α := by rw [Real.rpow_natCast]
  have hpoly_ν' : polyP D₀ (B + 1) ν' c ≤ (2 : ℝ) ^ (B + 1) * polyP D₀ (B + 1) ν c := by
    unfold polyP
    have h1 : 1 + c + (ν')⁻¹ ≤ 2 * (1 + c + ν⁻¹) := by
      dsimp [ν']
      rw [inv_div, div_eq_mul_inv]
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      linarith
    have hpow : (1 + c + (ν')⁻¹) ^ (B + 1) ≤ (2 : ℝ) ^ (B + 1) * (1 + c + ν⁻¹) ^ (B + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 (B + 1)
    calc D₀ * (1 + c + (ν')⁻¹) ^ (B + 1)
        ≤ D₀ * ((2 : ℝ) ^ (B + 1) * (1 + c + ν⁻¹) ^ (B + 1)) :=
          mul_le_mul_of_nonneg_left hpow hD₀_pos.le
      _ = (2 : ℝ) ^ (B + 1) * (D₀ * (1 + c + ν⁻¹) ^ (B + 1)) := by ring
  have hjet_bd : (1 + |η - θ * ξ|) ^ m * |iteratedDeriv B (heatKernel1 a) (η - θ * ξ)| ≤
      polyP ((2 : ℝ) ^ (B + 1 + m) * D₀) (B + 1) ν c * s ^ α := by
    calc (1 + |η - θ * ξ|) ^ m * |iteratedDeriv B (heatKernel1 a) (η - θ * ξ)|
        ≤ polyP D₀ (B + 1) ν' c * (s') ^ α := hjet
      _ ≤ ((2 : ℝ) ^ (B + 1) * polyP D₀ (B + 1) ν c) * ((2 : ℝ) ^ m * s ^ α) :=
          mul_le_mul hpoly_ν' hrpow (Real.rpow_nonneg hs'0.le _) (by unfold polyP; positivity)
      _ = polyP ((2 : ℝ) ^ (B + 1 + m) * D₀) (B + 1) ν c * s ^ α := by
          unfold polyP
          rw [pow_add]
          ring
  calc |η| ^ m * |iteratedDeriv B (heatKernel1 a) (η - θ * ξ)|
      ≤ ((1 + |η - θ * ξ|) ^ m * (1 + |ξ|) ^ m) *
          |iteratedDeriv B (heatKernel1 a) (η - θ * ξ)| :=
        mul_le_mul_of_nonneg_right (pow_abs_le_one_add_sub_mul_one_add m hθ) (abs_nonneg _)
    _ = (1 + |ξ|) ^ m *
          ((1 + |η - θ * ξ|) ^ m * |iteratedDeriv B (heatKernel1 a) (η - θ * ξ)|) := by ring
    _ ≤ (1 + |ξ|) ^ m * (polyP ((2 : ℝ) ^ (B + 1 + m) * D₀) (B + 1) ν c * s ^ α) :=
        mul_le_mul_of_nonneg_left hjet_bd (by positivity)

/-! ### 3. Parametric differentiation of double integrals `∫ t in a..d, ∫ w, Φ k t w η` -/

private theorem aestronglyMeasurable_parametric_integral_Ioc {a d : ℝ}
    {H : ℝ → ℝ → ℝ} (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Ioc a d ×ˢ univ)) :
    AEStronglyMeasurable (fun t : ℝ => ∫ w : ℝ, H t w) (volume.restrict (Ioc a d)) := by
  let G : ℝ × ℝ → ℝ := (Ioc a d ×ˢ (univ : Set ℝ)).indicator (fun p => H p.1 p.2)
  have hS_meas : MeasurableSet (Ioc a d ×ˢ (univ : Set ℝ)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hG_aem : AEStronglyMeasurable G (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (aestronglyMeasurable_indicator_iff hS_meas).2 (hH.aestronglyMeasurable hS_meas)
  have h_int_aem : AEStronglyMeasurable (fun t : ℝ => ∫ w : ℝ, G (t, w)) volume :=
    hG_aem.integral_prod_right'
  refine h_int_aem.restrict.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  congr 1
  funext w
  have hmem : ((t, w) : ℝ × ℝ) ∈ Ioc a d ×ˢ (univ : Set ℝ) := ⟨ht, mem_univ w⟩
  simp [G, hmem]

private theorem iteratedDeriv_eq_of_hasDerivAt_le (b : ℕ) (g : ℕ → ℝ → ℝ)
    (hd : ∀ k ≤ b, ∀ y : ℝ, HasDerivAt (g k) (g (k + 1) y) y) :
    (∀ k ≤ b, ∀ y : ℝ, iteratedDeriv k (g 0) y = g k y) ∧
      ContDiff ℝ (b : WithTop ℕ∞) (g 0) := by
  have hiter : ∀ k ≤ b, ∀ y : ℝ, iteratedDeriv k (g 0) y = g k y := by
    intro k hk
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      have heq : iteratedDeriv k (g 0) = g k := funext (ih (by omega))
      rw [iteratedDeriv_succ, heq, (hd k (by omega) y).deriv]
  have hcd : ∀ n k : ℕ, n + k ≤ b → ContDiff ℝ (n : WithTop ℕ∞) (g k) := by
    intro n
    induction n with
    | zero =>
      intro k hk
      exact contDiff_zero.2 (continuous_iff_continuousAt.mpr fun y => (hd k (by omega) y).continuousAt)
    | succ n ih =>
      intro k hk
      push_cast
      rw [contDiff_succ_iff_deriv]
      refine ⟨fun y => (hd k (by omega) y).differentiableAt, by simp, ?_⟩
      have hderiv : deriv (g k) = g (k + 1) := funext fun y => (hd k (by omega) y).deriv
      rw [hderiv]
      exact ih (k + 1) (by omega)
  exact ⟨hiter, hcd b 0 (by omega)⟩

/-- Iterated differentiation in `η` up to order `b` under `∫ t in a..d, ∫ w : ℝ, Φ k t w η` for a
family `Φ : ℕ → ℝ → ℝ → ℝ → ℝ` with uniform integrable majorants `dom k` for `k ≤ b + 1`. -/
private theorem iteratedDeriv_intervalIntegral_integral (b : ℕ) {a d : ℝ} (had : a ≤ d)
    (Φ : ℕ → ℝ → ℝ → ℝ → ℝ) (dom : ℕ → ℝ → ℝ)
    (hdom_int : ∀ k ≤ b + 1, Integrable (dom k) volume)
    (hΦ_cont : ∀ k ≤ b + 1, ∀ η : ℝ,
      ContinuousOn (fun p : ℝ × ℝ => Φ k p.1 p.2 η) (Ioc a d ×ˢ univ))
    (hΦ_deriv : ∀ k ≤ b, ∀ t ∈ Ioc a d, ∀ w η : ℝ,
      HasDerivAt (Φ k t w) (Φ (k + 1) t w η) η)
    (hΦ_bd : ∀ k ≤ b + 1, ∀ t ∈ Ioc a d, ∀ w η : ℝ, |Φ k t w η| ≤ dom k w) :
    (∀ k ≤ b, ∀ η : ℝ,
      iteratedDeriv k (fun η' => ∫ t in a..d, ∫ w : ℝ, Φ 0 t w η') η =
        ∫ t in a..d, ∫ w : ℝ, Φ k t w η) ∧
    ContDiff ℝ (b : WithTop ℕ∞) (fun η' => ∫ t in a..d, ∫ w : ℝ, Φ 0 t w η') ∧
    (∀ k ≤ b + 1, ∀ η₀ : ℝ, IntervalIntegrable (fun t => ∫ w : ℝ, Φ k t w η₀) volume a d) := by
  let g : ℕ → ℝ → ℝ := fun k η => ∫ t in a..d, ∫ w : ℝ, Φ k t w η
  have hI_int_all : ∀ k ≤ b + 1, ∀ η₀ : ℝ,
      IntervalIntegrable (fun t => ∫ w : ℝ, Φ k t w η₀) volume a d := by
    intro k hk1 η₀
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le had]
    have h_const : IntegrableOn (fun _ : ℝ => ∫ w : ℝ, dom k w) (Ioc a d) volume :=
      integrableOn_const measure_Ioc_lt_top.ne
    refine h_const.mono' (aestronglyMeasurable_parametric_integral_Ioc (hΦ_cont k hk1 η₀)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    refine norm_integral_le_of_norm_le (hdom_int k hk1) (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs]
    exact hΦ_bd k hk1 t ht w η₀
  have hI_deriv : ∀ k ≤ b, ∀ t ∈ Ioc a d, ∀ η₀ : ℝ,
      HasDerivAt (fun η => ∫ w : ℝ, Φ k t w η) (∫ w : ℝ, Φ (k + 1) t w η₀) η₀ := by
    intro k hk t ht η₀
    have hk1 : k ≤ b + 1 := by omega
    have hk2 : k + 1 ≤ b + 1 := by omega
    have hF_meas : ∀ η : ℝ, AEStronglyMeasurable (fun w => Φ k t w η) volume := by
      intro η
      have hc : Continuous (fun w : ℝ => Φ k t w η) :=
        (hΦ_cont k hk1 η).comp_continuous (continuous_const.prodMk continuous_id)
          (fun w => ⟨ht, mem_univ w⟩)
      exact hc.aestronglyMeasurable
    have hF_int : Integrable (fun w => Φ k t w η₀) volume := by
      refine (hdom_int k hk1).mono' (hF_meas η₀) (Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs]
      exact hΦ_bd k hk1 t ht w η₀
    have hF'_meas : AEStronglyMeasurable (fun w => Φ (k + 1) t w η₀) volume := by
      have hc : Continuous (fun w : ℝ => Φ (k + 1) t w η₀) :=
        (hΦ_cont (k + 1) hk2 η₀).comp_continuous (continuous_const.prodMk continuous_id)
          (fun w => ⟨ht, mem_univ w⟩)
      exact hc.aestronglyMeasurable
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := univ) (bound := dom (k + 1)) univ_mem
      (Eventually.of_forall hF_meas) hF_int hF'_meas
      (Eventually.of_forall fun w => fun η _ => ?_)
      (hdom_int (k + 1) hk2)
      (Eventually.of_forall fun w => fun η _ => hΦ_deriv k hk t ht w η)).2
    rw [Real.norm_eq_abs]
    exact hΦ_bd (k + 1) hk2 t ht w η
  have hg_deriv : ∀ k ≤ b, ∀ η₀ : ℝ, HasDerivAt (g k) (g (k + 1) η₀) η₀ := by
    intro k hk η₀
    have hk1 : k ≤ b + 1 := by omega
    have hk2 : k + 1 ≤ b + 1 := by omega
    set B_k1 : ℝ := ∫ w : ℝ, dom (k + 1) w
    have hI_meas : ∀ η : ℝ,
        AEStronglyMeasurable (fun t => ∫ w : ℝ, Φ k t w η) (volume.restrict (uIoc a d)) := by
      intro η
      rw [uIoc_of_le had]
      exact aestronglyMeasurable_parametric_integral_Ioc (hΦ_cont k hk1 η)
    have hI_int : IntervalIntegrable (fun t => ∫ w : ℝ, Φ k t w η₀) volume a d :=
      hI_int_all k hk1 η₀
    have hI'_meas : AEStronglyMeasurable (fun t => ∫ w : ℝ, Φ (k + 1) t w η₀)
        (volume.restrict (uIoc a d)) := by
      rw [uIoc_of_le had]
      exact aestronglyMeasurable_parametric_integral_Ioc (hΦ_cont (k + 1) hk2 η₀)
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun η t => ∫ w : ℝ, Φ k t w η)
      (F' := fun η t => ∫ w : ℝ, Φ (k + 1) t w η)
      (s := univ) (bound := fun _ => B_k1) univ_mem
      (Eventually.of_forall hI_meas) hI_int hI'_meas
      (Eventually.of_forall fun t ht => fun η _ => ?_)
      intervalIntegrable_const
      (Eventually.of_forall fun t ht => fun η _ => ?_)).2
    · rw [uIoc_of_le had] at ht
      exact norm_integral_le_of_norm_le (hdom_int (k + 1) hk2) (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        exact hΦ_bd (k + 1) hk2 t ht w η)
    · rw [uIoc_of_le had] at ht
      exact hI_deriv k hk t ht η
  have hmain := iteratedDeriv_eq_of_hasDerivAt_le b g hg_deriv
  exact ⟨hmain.1, hmain.2, hI_int_all⟩

/-! ### 4. Splitting `meanSourceDuhamel` and `meanSourceCoeff` at `t = s / 2` -/

private def D_near {ν c : ℝ} (tr : B0140.TrainSol ν c) (s η : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(s / 2), ∫ ξ : ℝ, heatKernel1 (ν * (s - t)) (η - ξ) * meanStress tr t ξ

private def D_far {ν c : ℝ} (tr : B0140.TrainSol ν c) (s η : ℝ) : ℝ :=
  ∫ t in (s / 2)..s, ∫ z : ℝ,
    heatKernel1 1 z * meanStress tr t (η - Real.sqrt (ν * (s - t)) * z)

private theorem iteratedDeriv_D_near (b : ℕ) {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {P₀ : ℝ}
    (hP₀ : ∀ t : ℝ, 0 < t → ∀ ξ : ℝ, (1 + ξ ^ 2) * |meanStress tr t ξ| ≤ P₀)
    {s : ℝ} (hs : 1 ≤ s) :
    (∀ η : ℝ,
      iteratedDeriv b (D_near tr s) η =
        ∫ t in (0 : ℝ)..(s / 2), ∫ ξ : ℝ,
          iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) * meanStress tr t ξ) ∧
    ContDiff ℝ (b : WithTop ℕ∞) (D_near tr s) ∧
    (∀ η : ℝ, IntervalIntegrable
      (fun t => ∫ ξ : ℝ, iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) * meanStress tr t ξ)
      volume 0 (s / 2)) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hs2 : 0 ≤ s / 2 := by positivity
  have hP₀_nn : 0 ≤ P₀ := by
    have h := hP₀ 1 one_pos 0
    simpa using (by positivity : (0 : ℝ) ≤ (1 + 0 ^ 2) * |meanStress tr 1 0|).trans h
  set a_min : ℝ := ν * (s / 2)
  have hamin : 0 < a_min := by dsimp [a_min]; positivity
  let Φ : ℕ → ℝ → ℝ → ℝ → ℝ := fun k t ξ η =>
    iteratedDeriv k (heatKernel1 (ν * (s - t))) (η - ξ) * meanStress tr t ξ
  choose C_k hC_k_pos hC_k using abs_iteratedDeriv_heatKernel1_le_of_ge
  let dom : ℕ → ℝ → ℝ := fun k ξ =>
    (((Real.sqrt a_min)⁻¹) ^ (k + 1) * C_k k * P₀) * (1 + ξ ^ 2)⁻¹
  have hdom_int : ∀ k ≤ b + 1, Integrable (dom k) volume :=
    fun k _ => integrable_inv_one_add_sq.const_mul _
  have hΦ_cont : ∀ k ≤ b + 1, ∀ η : ℝ,
      ContinuousOn (fun p : ℝ × ℝ => Φ k p.1 p.2 η) (Ioc 0 (s / 2) ×ˢ univ) := by
    intro k _ η
    have h1 : ContinuousOn
        (fun p : ℝ × ℝ => ((Real.sqrt (ν * (s - p.1)))⁻¹) ^ (k + 1) *
          G1_deriv k ((Real.sqrt (ν * (s - p.1)))⁻¹ * (η - p.2)))
        (Ioc 0 (s / 2) ×ˢ univ) := by
      have hsub : ContinuousOn (fun p : ℝ × ℝ => ν * (s - p.1)) (Ioc 0 (s / 2) ×ˢ univ) :=
        continuousOn_const.mul (continuousOn_const.sub continuousOn_fst)
      have hsq : ContinuousOn (fun p : ℝ × ℝ => Real.sqrt (ν * (s - p.1)))
          (Ioc 0 (s / 2) ×ˢ univ) := ContinuousOn.sqrt hsub
      have hinv : ContinuousOn (fun p : ℝ × ℝ => (Real.sqrt (ν * (s - p.1)))⁻¹)
          (Ioc 0 (s / 2) ×ˢ univ) :=
        hsq.inv₀ fun p hp => (Real.sqrt_pos.2 (by nlinarith [hp.1.2, hs0, hν])).ne'
      exact (hinv.pow (k + 1)).mul
        ((contDiff_G1_deriv k).continuous.comp_continuousOn
          (hinv.mul (continuousOn_const.sub continuousOn_snd)))
    have h1' : ContinuousOn
        (fun p : ℝ × ℝ => iteratedDeriv k (heatKernel1 (ν * (s - p.1))) (η - p.2))
        (Ioc 0 (s / 2) ×ˢ univ) := by
      refine h1.congr fun p hp => ?_
      have ha : 0 < ν * (s - p.1) := by nlinarith [hp.1.2, hs0, hν]
      exact iteratedDeriv_heatKernel1_scale ha k (η - p.2)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => meanStress tr p.1 p.2) (Ioc 0 (s / 2) ×ˢ univ) :=
      (PartI_T23.contDiffOn_meanStress hc tr).continuousOn.mono
        (prod_mono (fun t ht => ht.1) Subset.rfl)
    exact h1'.mul h2
  have hΦ_deriv : ∀ k ≤ b, ∀ t ∈ Ioc 0 (s / 2), ∀ ξ η : ℝ,
      HasDerivAt (Φ k t ξ) (Φ (k + 1) t ξ η) η := by
    intro k _ t _ ξ η
    have hd : DifferentiableAt ℝ (iteratedDeriv k (heatKernel1 (ν * (s - t)))) (η - ξ) :=
      (contDiff_iteratedDeriv _ (contDiff_heatKernel1 _) k).differentiable (by simp) _
    have h1 := hd.hasDerivAt
    rw [← iteratedDeriv_succ] at h1
    have hsub : HasDerivAt (fun η' : ℝ => η' - ξ) 1 η :=
      (hasDerivAt_id' η).sub_const ξ
    have hcomp := (h1.comp η hsub).mul_const (meanStress tr t ξ)
    refine hcomp.congr_deriv ?_
    dsimp [Φ]
    ring
  have hΦ_bd : ∀ k ≤ b + 1, ∀ t ∈ Ioc 0 (s / 2), ∀ ξ η : ℝ, |Φ k t ξ η| ≤ dom k ξ := by
    intro k _ t ht ξ η
    dsimp [Φ, dom]
    rw [abs_mul]
    have ha : a_min ≤ ν * (s - t) := by
      dsimp [a_min]
      nlinarith [ht.2, hν]
    have hK := hC_k k hamin ha (η - ξ)
    have hS : |meanStress tr t ξ| ≤ P₀ * (1 + ξ ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity), mul_comm]
      exact hP₀ t ht.1 ξ
    calc |iteratedDeriv k (heatKernel1 (ν * (s - t))) (η - ξ)| * |meanStress tr t ξ|
        ≤ (((Real.sqrt a_min)⁻¹) ^ (k + 1) * C_k k) * (P₀ * (1 + ξ ^ 2)⁻¹) :=
          mul_le_mul hK hS (abs_nonneg _) (by have := hC_k_pos k; positivity)
      _ = (((Real.sqrt a_min)⁻¹) ^ (k + 1) * C_k k * P₀) * (1 + ξ ^ 2)⁻¹ := by ring
  have hmain := iteratedDeriv_intervalIntegral_integral b hs2 Φ dom hdom_int hΦ_cont hΦ_deriv hΦ_bd
  have h0 : (fun η' => ∫ t in (0 : ℝ)..(s / 2), ∫ ξ : ℝ, Φ 0 t ξ η') = D_near tr s := by
    funext η'
    rfl
  rw [h0] at hmain
  exact ⟨hmain.1 b le_rfl, hmain.2.1, hmain.2.2 b (by omega)⟩

private theorem iteratedDeriv_D_far (b : ℕ) {ν c : ℝ} (_hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c)
    (B_k : ℕ → ℝ) (_hB_nn : ∀ k ≤ b + 1, 0 ≤ B_k k)
    (hB : ∀ k ≤ b + 1, ∀ t : ℝ, 0 < t → ∀ y : ℝ, |iteratedDeriv k (meanStress tr t) y| ≤ B_k k)
    {s : ℝ} (hs : 1 ≤ s) :
    (∀ η : ℝ,
      iteratedDeriv b (D_far tr s) η =
        ∫ t in (s / 2)..s, ∫ z : ℝ,
          heatKernel1 1 z *
            iteratedDeriv b (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z)) ∧
    ContDiff ℝ (b : WithTop ℕ∞) (D_far tr s) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hs2 : s / 2 ≤ s := by linarith
  let Φ : ℕ → ℝ → ℝ → ℝ → ℝ := fun k t z η =>
    heatKernel1 1 z * iteratedDeriv k (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z)
  let dom : ℕ → ℝ → ℝ := fun k z => B_k k * heatKernel1 1 z
  have hK1_int : Integrable (heatKernel1 1) volume := by
    have h0 := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := 0) (by norm_num)
    have h1 : Integrable (fun z : ℝ => Real.exp (-(1 / 4) * z ^ 2)) volume := by
      simpa using h0
    refine (h1.const_mul (Real.sqrt (4 * Real.pi * 1))⁻¹).congr (ae_of_all _ fun z => ?_)
    dsimp [heatKernel1]
    rw [show -(z ^ 2) / (4 * 1) = -(1 / 4) * z ^ 2 by ring]
  have hdom_int : ∀ k ≤ b + 1, Integrable (dom k) volume :=
    fun k _ => hK1_int.const_mul (B_k k)
  have hΦ_cont : ∀ k ≤ b + 1, ∀ η : ℝ,
      ContinuousOn (fun p : ℝ × ℝ => Φ k p.1 p.2 η) (Ioc (s / 2) s ×ˢ univ) := by
    intro k _ η
    have hms_k : ContDiffOn ℝ ∞
        (fun x : ℝ × ℝ => iteratedDeriv k (meanStress tr x.1) x.2) (Ioi 0 ×ˢ univ) :=
      UnforcedLeray.Short.PartIIa.etaDerivIter_contDiffOn (meanStress tr)
        (PartI_T23.contDiffOn_meanStress hc tr) k
    have hmap : Continuous (fun p : ℝ × ℝ =>
        ((p.1, η - Real.sqrt (ν * (s - p.1)) * p.2) : ℝ × ℝ)) :=
      continuous_fst.prodMk
        (continuous_const.sub
          ((Real.continuous_sqrt.comp
            (continuous_const.mul (continuous_const.sub continuous_fst))).mul continuous_snd))
    have hcomp : ContinuousOn
        (fun p : ℝ × ℝ => iteratedDeriv k (meanStress tr p.1)
          (η - Real.sqrt (ν * (s - p.1)) * p.2))
        (Ioc (s / 2) s ×ˢ univ) :=
      hms_k.continuousOn.comp hmap.continuousOn
        (fun p hp => ⟨lt_of_lt_of_le (by positivity : 0 < s / 2) hp.1.1.le, mem_univ _⟩)
    exact ((contDiff_heatKernel1 1).continuous.comp continuous_snd).continuousOn.mul hcomp
  have hΦ_deriv : ∀ k ≤ b, ∀ t ∈ Ioc (s / 2) s, ∀ z η : ℝ,
      HasDerivAt (Φ k t z) (Φ (k + 1) t z η) η := by
    intro k _ t ht z η
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < s / 2) ht.1.le
    have hms_sm : ContDiff ℝ ∞ (meanStress tr t) := by
      have hcomp : ContDiffOn ℝ ∞
          ((fun x : ℝ × ℝ => meanStress tr x.1 x.2) ∘ (fun y : ℝ => ((t, y) : ℝ × ℝ))) univ :=
        (PartI_T23.contDiffOn_meanStress hc tr).comp
          (contDiffOn_univ.2 (contDiff_const.prodMk contDiff_id))
          (fun y _ => ⟨ht0, mem_univ y⟩)
      exact contDiffOn_univ.1 hcomp
    have hd : DifferentiableAt ℝ (iteratedDeriv k (meanStress tr t))
        (η - Real.sqrt (ν * (s - t)) * z) :=
      (contDiff_iteratedDeriv _ hms_sm k).differentiable (by simp) _
    have h1 := hd.hasDerivAt
    rw [← iteratedDeriv_succ] at h1
    have hsub : HasDerivAt (fun η' : ℝ => η' - Real.sqrt (ν * (s - t)) * z) 1 η :=
      (hasDerivAt_id' η).sub_const _
    have hcomp := (h1.comp η hsub).const_mul (heatKernel1 1 z)
    refine hcomp.congr_deriv ?_
    dsimp [Φ]
    ring
  have hΦ_bd : ∀ k ≤ b + 1, ∀ t ∈ Ioc (s / 2) s, ∀ z η : ℝ, |Φ k t z η| ≤ dom k z := by
    intro k hk t ht z η
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < s / 2) ht.1.le
    have hK1_nn : 0 ≤ heatKernel1 1 z := by unfold heatKernel1; positivity
    dsimp [Φ, dom]
    rw [abs_mul, abs_of_nonneg hK1_nn, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB k hk t ht0 _) hK1_nn
  have hmain := iteratedDeriv_intervalIntegral_integral b hs2 Φ dom hdom_int hΦ_cont hΦ_deriv hΦ_bd
  have h0 : (fun η' => ∫ t in (s / 2)..s, ∫ z : ℝ, Φ 0 t z η') = D_far tr s := by
    funext η'
    rfl
  rw [h0] at hmain
  exact ⟨hmain.1 b le_rfl, hmain.2.1⟩

/-- For `ν > 0`, `c > 0`, `IsBUCTrain tr`, and `s ≥ 1`,
`meanSourceDuhamel tr s η = D_near tr s η + D_far tr s η`. -/
private theorem meanSourceDuhamel_eq_add {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {s : ℝ} (hs : 1 ≤ s) (η : ℝ) :
    meanSourceDuhamel tr s η = D_near tr s η + D_far tr s η := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  obtain ⟨M0, hM0⟩ := htr.sup_bound hs0.le
  set g_int : ℝ → ℝ := fun t => ∫ ξ : ℝ, heatKernel1 (ν * (s - t)) (η - ξ) * meanStress tr t ξ
  set H_ext : ℝ → ℝ → ℝ := fun t z =>
    heatKernel1 1 z *
      meanStress tr (min (max t 0) s) (η - Real.sqrt (ν * max (s - t) 0) * z)
  set g_ext : ℝ → ℝ := fun t => ∫ z : ℝ, H_ext t z
  have hg_eq_on_Ioo : ∀ t ∈ Ioo (0 : ℝ) s, g_int t = g_ext t := by
    intro t ht
    dsimp [g_ext, H_ext]
    have ha : 0 < ν * (s - t) := mul_pos hν (sub_pos.2 ht.2)
    have hsq : 0 < Real.sqrt (ν * (s - t)) := Real.sqrt_pos.2 ha
    have hsub := integral_sub_left_eq_self
      (fun u : ℝ => heatKernel1 (ν * (s - t)) u * meanStress tr t (η - u)) volume η
    have hsub' : g_int t =
        ∫ u : ℝ, heatKernel1 (ν * (s - t)) u * meanStress tr t (η - u) := by
      refine (integral_congr_ae (Eventually.of_forall fun ξ => ?_)).trans hsub
      change heatKernel1 (ν * (s - t)) (η - ξ) * meanStress tr t ξ =
        heatKernel1 (ν * (s - t)) (η - ξ) * meanStress tr t (η - (η - ξ))
      rw [show η - (η - ξ) = ξ by ring]
    rw [hsub']
    have hmul := Measure.integral_comp_mul_left
      (fun u : ℝ => heatKernel1 (ν * (s - t)) u * meanStress tr t (η - u))
      (Real.sqrt (ν * (s - t)))
    rw [abs_inv, abs_of_pos hsq, smul_eq_mul] at hmul
    have hmul' : (∫ u : ℝ, heatKernel1 (ν * (s - t)) u * meanStress tr t (η - u)) =
        Real.sqrt (ν * (s - t)) * ∫ z : ℝ,
          heatKernel1 (ν * (s - t)) (Real.sqrt (ν * (s - t)) * z) *
            meanStress tr t (η - Real.sqrt (ν * (s - t)) * z) := by
      rw [hmul, mul_inv_cancel_left₀ hsq.ne']
    rw [hmul', ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    have hscale := PartI_T23.heatKernel1_nu_scale ha 1 (Real.sqrt (ν * (s - t)) * z)
    rw [mul_one, mul_one, inv_mul_cancel_left₀ hsq.ne'] at hscale
    rw [max_eq_left ht.1.le, min_eq_left ht.2.le, max_eq_left (sub_pos.2 ht.2).le]
    change Real.sqrt (ν * (s - t)) *
        (heatKernel1 (ν * (s - t)) (Real.sqrt (ν * (s - t)) * z) *
          meanStress tr t (η - Real.sqrt (ν * (s - t)) * z)) =
      heatKernel1 1 z * meanStress tr t (η - Real.sqrt (ν * (s - t)) * z)
    rw [hscale, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hsq.ne', one_mul]
  have hK1_int : Integrable (fun z : ℝ => (M0 * M0) * heatKernel1 1 z) volume := by
    have h0 := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := 0) (by norm_num)
    have h1 : Integrable (fun z : ℝ => Real.exp (-(1 / 4) * z ^ 2)) volume := by simpa using h0
    refine ((h1.const_mul (Real.sqrt (4 * Real.pi * 1))⁻¹).congr
      (ae_of_all _ fun z => ?_)).const_mul (M0 * M0)
    dsimp [heatKernel1]
    rw [show -(z ^ 2) / (4 * 1) = -(1 / 4) * z ^ 2 by ring]
  have hms_Ici : ContinuousOn (fun x : ℝ × ℝ => meanStress tr x.1 x.2) (Ici 0 ×ˢ univ) := by
    set prod_ext : ℝ → Plane → ℝ := fun r z => tr.v (max r 0) z 0 * tr.v (max r 0) z 1
    have hp_cont : Continuous (fun p : ℝ × Plane => prod_ext p.1 p.2) := by
      have h0 : ContinuousOn (fun p : ℝ × Plane => tr.v p.1 p.2 0) (Ici 0 ×ˢ univ) :=
        (PiLp.continuous_apply 2 _ 0).comp_continuousOn tr.isTrain.smooth_v.continuousOn
      have h1 : ContinuousOn (fun p : ℝ × Plane => tr.v p.1 p.2 1) (Ici 0 ×ˢ univ) :=
        (PiLp.continuous_apply 2 _ 1).comp_continuousOn tr.isTrain.smooth_v.continuousOn
      have hmap : Continuous (fun p : ℝ × Plane => ((max p.1 0, p.2) : ℝ × Plane)) :=
        (continuous_fst.max continuous_const).prodMk continuous_snd
      exact (h0.mul h1).comp_continuous hmap fun p => ⟨le_max_right p.1 0, mem_univ p.2⟩
    have hle : -c / 2 ≤ c / 2 := by linarith
    have hcont_uncurry : Continuous
        (Function.uncurry (fun (x : ℝ × ℝ) (q : ℝ) => prod_ext x.1 (q, x.2))) :=
      hp_cont.comp ((continuous_fst.comp continuous_fst).prodMk
        (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
    have h_all : Continuous
        (fun x : ℝ × ℝ => c⁻¹ * ∫ q in (-c / 2)..(c / 2), prod_ext x.1 (q, x.2)) :=
      continuous_const.mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          hcont_uncurry (-c / 2) (c / 2))
    refine h_all.continuousOn.congr fun x hx => ?_
    unfold meanStress hmean
    dsimp only
    rw [smul_eq_mul, intervalIntegral.integral_of_le hle]
    congr 1; refine setIntegral_congr_fun measurableSet_Ioc fun q _ => ?_
    dsimp [prod_ext]; rw [max_eq_left hx.1]
  have hg_ext_cont : Continuous g_ext := by
    rw [continuous_iff_continuousAt]
    intro t₀
    have hH_cont_t : ∀ z : ℝ, Continuous (fun t : ℝ => H_ext t z) := by
      intro z
      refine continuous_const.mul (hms_Ici.comp_continuous
        (((continuous_id.max continuous_const).min continuous_const).prodMk
          (continuous_const.sub ((Real.continuous_sqrt.comp
            (continuous_const.mul ((continuous_const.sub continuous_id).max continuous_const))).mul
            continuous_const)))
        (fun t => ⟨le_min (le_max_right t 0) hs0.le, mem_univ _⟩))
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => (M0 * M0) * heatKernel1 1 z)
      (Eventually.of_forall fun t => ?_)
      (Eventually.of_forall fun t => Eventually.of_forall fun z => ?_)
      hK1_int
      (Eventually.of_forall fun z => (hH_cont_t z).continuousAt.tendsto)
    · have h1 : Continuous (fun z : ℝ => H_ext t z) :=
        (contDiff_heatKernel1 1).continuous.mul (hms_Ici.comp_continuous
          (continuous_const.prodMk (continuous_const.sub (continuous_const.mul continuous_id)))
          (fun z => ⟨le_min (le_max_right t 0) hs0.le, mem_univ _⟩))
      exact h1.aestronglyMeasurable
    · have hcl_mem : min (max t 0) s ∈ Icc (0 : ℝ) s :=
        ⟨le_min (le_max_right t 0) hs0.le, min_le_right _ _⟩
      have hK1_nn : 0 ≤ heatKernel1 1 z := by unfold heatKernel1; positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK1_nn, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (msi_meanStress_bound hc tr (fun w => hM0 _ hcl_mem w) _) hK1_nn
  have hcongr_Ioo : ∀ a d : ℝ, a ≤ d → (0 : ℝ) ≤ a → d ≤ s →
      (∫ t in a..d, g_int t) = ∫ t in a..d, g_ext t := by
    intro a d had ha0 hds
    rw [intervalIntegral.integral_of_le had, intervalIntegral.integral_of_le had,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    exact hg_eq_on_Ioo t ⟨lt_of_le_of_lt ha0 ht.1, lt_of_lt_of_le ht.2 hds⟩
  have hfar_eq : (∫ t in (s / 2)..s, g_ext t) = D_far tr s η := by
    unfold D_far
    have hs2 : s / 2 ≤ s := by linarith
    rw [intervalIntegral.integral_of_le hs2, intervalIntegral.integral_of_le hs2,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    dsimp [g_ext, H_ext]
    congr 1; funext z
    have ht0 : 0 ≤ t := by linarith [ht.1]
    rw [max_eq_left ht0, min_eq_left ht.2.le, max_eq_left (sub_pos.2 ht.2).le]
  unfold meanSourceDuhamel D_near
  change (∫ t in (0 : ℝ)..s, g_int t) = (∫ t in (0 : ℝ)..(s / 2), g_int t) + D_far tr s η
  rw [hcongr_Ioo 0 s hs0.le le_rfl le_rfl,
    hcongr_Ioo 0 (s / 2) (by positivity) le_rfl (by linarith), ← hfar_eq]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hg_ext_cont.intervalIntegrable (μ := volume) 0 (s / 2))
    (hg_ext_cont.intervalIntegrable (μ := volume) (s / 2) s)).symm

/-! ### 5. Exponential-to-power absorption, moment integrals, and sum re-indexing -/

/-- Absorbing `s ^ p * exp (-(κ * ν * s / c ^ 2))` into `polyP C M ν c * s ^ α` for `s ≥ 1`
and `-(q : ℝ) ≤ α`. -/
private theorem rpow_mul_exp_le_polyP_mul_rpow {κ : ℝ} (hκ : 0 < κ) (p q : ℕ) {α : ℝ}
    (hα : -(q : ℝ) ≤ α) :
    ∃ C : ℝ, ∃ M : ℕ, 0 < C ∧ ∀ {ν c s : ℝ}, 0 < ν → 0 < c → 1 ≤ s →
      s ^ p * Real.exp (-(κ * ν * s / c ^ 2)) ≤ polyP C M ν c * s ^ α := by
  obtain ⟨C₀, M₀, hC₀_nn, hAbs⟩ := UnforcedLeray.Short.PartIIa.expPowAbsorb κ (p + q) hκ
  refine ⟨max C₀ 1, M₀, lt_max_of_lt_right one_pos, ?_⟩
  intro ν c s hν hc hs
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have h1 := hAbs ν c s hν hc hs0.le
  have hexp_le1 : Real.exp (-(κ / 2 * ν * s / c ^ 2)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.2
    have : 0 ≤ κ / 2 * ν * s / c ^ 2 := by positivity
    linarith
  have hpoly_nn : 0 ≤ UnforcedLeray.Short.PartIIa.polyConst C₀ M₀ ν c := by
    unfold UnforcedLeray.Short.PartIIa.polyConst
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    positivity
  have h2 : s ^ (p + q) * Real.exp (-(κ * ν * s / c ^ 2)) ≤
      polyP (max C₀ 1) M₀ ν c := by
    calc s ^ (p + q) * Real.exp (-(κ * ν * s / c ^ 2))
        ≤ UnforcedLeray.Short.PartIIa.polyConst C₀ M₀ ν c *
            Real.exp (-(κ / 2 * ν * s / c ^ 2)) := h1
      _ ≤ UnforcedLeray.Short.PartIIa.polyConst C₀ M₀ ν c * 1 :=
          mul_le_mul_of_nonneg_left hexp_le1 hpoly_nn
      _ ≤ polyP (max C₀ 1) M₀ ν c := by
          rw [mul_one]
          unfold UnforcedLeray.Short.PartIIa.polyConst polyP
          have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hsp : s ^ p = s ^ (p + q) * s ^ (-(q : ℝ)) := by
    rw [← Real.rpow_natCast s p, ← Real.rpow_natCast s (p + q), ← Real.rpow_add hs0]
    congr 1
    push_cast
    ring
  have hsq_le : s ^ (-(q : ℝ)) ≤ s ^ α :=
    Real.rpow_le_rpow_of_exponent_le hs hα
  calc s ^ p * Real.exp (-(κ * ν * s / c ^ 2))
      = (s ^ (p + q) * Real.exp (-(κ * ν * s / c ^ 2))) * s ^ (-(q : ℝ)) := by
        rw [hsp]; ring
    _ ≤ polyP (max C₀ 1) M₀ ν c * s ^ α :=
        mul_le_mul h2 hsq_le (Real.rpow_nonneg hs0.le _) (by unfold polyP; positivity)

/-- Bound on `∫ t in Ioi 0, (1 + t ^ (N + 1)) * exp (-(lam * t))` for `lam = κ * ν / c ^ 2`. -/
private theorem integral_one_add_pow_mul_exp_Ioi (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, ∃ M : ℕ, 0 < C ∧ ∀ {ν c : ℝ}, 0 < ν → 1 ≤ c →
      IntegrableOn (fun t : ℝ => (1 + t ^ (N + 1)) * Real.exp (-(κ * ν * t / c ^ 2))) (Ioi 0) volume ∧
      (∫ t in Ioi (0 : ℝ), (1 + t ^ (N + 1)) * Real.exp (-(κ * ν * t / c ^ 2))) ≤
        polyP C M ν c := by
  set C_out : ℝ := (1 + ((N + 1).factorial : ℝ)) * (1 + κ⁻¹) ^ (N + 2)
  refine ⟨C_out, 3 * (N + 2), by dsimp [C_out]; positivity, ?_⟩
  intro ν c hν hc1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  set lam : ℝ := κ * ν / c ^ 2
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have h_eq : ∀ t : ℝ, (1 + t ^ (N + 1)) * Real.exp (-(κ * ν * t / c ^ 2)) =
      t ^ 0 * Real.exp (-(lam * t)) + t ^ (N + 1) * Real.exp (-(lam * t)) := by
    intro t
    dsimp [lam]
    rw [pow_zero, show κ * ν * t / c ^ 2 = κ * ν / c ^ 2 * t by ring]
    ring
  have hint0 := UnforcedLeray.Short.PartIIa.lmc_integrable_pow_mul_exp 0 hlam
  have hintN := UnforcedLeray.Short.PartIIa.lmc_integrable_pow_mul_exp (N + 1) hlam
  have hint : IntegrableOn
      (fun t : ℝ => (1 + t ^ (N + 1)) * Real.exp (-(κ * ν * t / c ^ 2))) (Ioi 0) volume := by
    refine (hint0.add hintN).congr_fun (fun t _ => (h_eq t).symm) measurableSet_Ioi
  refine ⟨hint, ?_⟩
  have hval : (∫ t in Ioi (0 : ℝ), (1 + t ^ (N + 1)) * Real.exp (-(κ * ν * t / c ^ 2))) =
      (1 / lam) ^ 1 + ((N + 1).factorial : ℝ) * (1 / lam) ^ (N + 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => h_eq t),
      integral_add hint0 hintN,
      UnforcedLeray.Short.PartIIa.lmc_integral_pow_mul_exp 0 hlam,
      UnforcedLeray.Short.PartIIa.lmc_integral_pow_mul_exp (N + 1) hlam]
    simp
  rw [hval]
  set X : ℝ := 1 + c + ν⁻¹
  have hX1 : 1 ≤ X := by
    dsimp [X]
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hlam_inv : 1 / lam ≤ (1 + κ⁻¹) * X ^ 3 := by
    have h1 : 1 / lam = κ⁻¹ * (c ^ 2 * ν⁻¹) := by
      dsimp [lam]
      field_simp
    have hcX : c ≤ X := by dsimp [X]; have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le; linarith
    have hνX : ν⁻¹ ≤ X := by dsimp [X]; linarith
    have hc2 : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc0.le hcX 2
    have h2 : c ^ 2 * ν⁻¹ ≤ X ^ 3 := by
      calc c ^ 2 * ν⁻¹ ≤ X ^ 2 * X := mul_le_mul hc2 hνX (inv_nonneg.2 hν.le) (by positivity)
        _ = X ^ 3 := by ring
    have hκ1 : κ⁻¹ ≤ 1 + κ⁻¹ := by linarith
    rw [h1]
    exact mul_le_mul hκ1 h2 (by positivity) (by positivity)
  have hZ1 : 1 ≤ (1 + κ⁻¹) * X ^ 3 := by
    have : 1 ≤ X ^ 3 := one_le_pow₀ hX1
    have : 0 ≤ κ⁻¹ := inv_nonneg.2 hκ.le
    nlinarith
  have hpow1 : (1 / lam) ^ 1 ≤ ((1 + κ⁻¹) * X ^ 3) ^ (N + 2) :=
    (pow_le_pow_left₀ (by positivity) hlam_inv 1).trans (pow_le_pow_right₀ hZ1 (by omega))
  have hpowN : (1 / lam) ^ (N + 2) ≤ ((1 + κ⁻¹) * X ^ 3) ^ (N + 2) :=
    pow_le_pow_left₀ (by positivity) hlam_inv (N + 2)
  calc (1 / lam) ^ 1 + ((N + 1).factorial : ℝ) * (1 / lam) ^ (N + 2)
      ≤ ((1 + κ⁻¹) * X ^ 3) ^ (N + 2) +
          ((N + 1).factorial : ℝ) * ((1 + κ⁻¹) * X ^ 3) ^ (N + 2) :=
        add_le_add hpow1 (mul_le_mul_of_nonneg_left hpowN (by positivity))
    _ = polyP C_out (3 * (N + 2)) ν c := by
        unfold polyP
        dsimp [C_out, X]
        rw [mul_pow, ← pow_mul]
        ring

/-- For `t ≥ 0` and `l ≤ N + 1`, `t ^ l ≤ 1 + t ^ (N + 1)`. -/
private theorem pow_le_one_add_pow {t : ℝ} (ht : 0 ≤ t) {l N : ℕ} (hl : l ≤ N + 1) :
    t ^ l ≤ 1 + t ^ (N + 1) := by
  rcases le_total t 1 with ht1 | ht1
  · have h1 : t ^ l ≤ 1 := pow_le_one₀ ht ht1
    linarith [pow_nonneg ht (N + 1)]
  · have h1 : t ^ l ≤ t ^ (N + 1) := pow_le_pow_right₀ ht1 hl
    linarith

/-- Odd spatial moments of `meanStress` vanish by evenness (`PartI_T23.meanStress_even`). -/
private theorem integral_odd_pow_mul_meanStress_eq_zero {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (∫ ξ : ℝ, ξ ^ (2 * k + 1) * meanStress tr t ξ) = 0 := by
  set f : ℝ → ℝ := fun ξ => ξ ^ (2 * k + 1) * meanStress tr t ξ
  have hodd : ∀ ξ : ℝ, f (-ξ) = -f ξ := by
    intro ξ
    have hpow : (-ξ) ^ (2 * k + 1) = -(ξ ^ (2 * k + 1)) := by
      rw [pow_succ, pow_mul, neg_sq, ← pow_mul, pow_succ]
      ring
    dsimp [f]
    rw [PartI_T23.meanStress_even hc tr ht ξ, hpow]
    ring
  have h1 : (∫ ξ : ℝ, f (-ξ)) = ∫ ξ : ℝ, f ξ := integral_neg_eq_self f volume
  have h2 : (∫ ξ : ℝ, f (-ξ)) = -(∫ ξ : ℝ, f ξ) := by
    simp_rw [hodd]
    exact integral_neg f
  linarith

/-- Filtering out odd indices in `∑ r ∈ range (2 * K + 2), C_r r * ∫ ξ, ξ^r * meanStress tr t ξ`. -/
private theorem sum_range_mul_integral_meanStress_eq_even {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {t : ℝ} (ht : 0 ≤ t) (K : ℕ) (C_r : ℕ → ℝ) :
    (∑ r ∈ Finset.range (2 * K + 2),
        C_r r * ∫ ξ : ℝ, ξ ^ r * meanStress tr t ξ) =
      ∑ k ∈ Finset.range (K + 1),
        C_r (2 * k) * ∫ ξ : ℝ, ξ ^ (2 * k) * meanStress tr t ξ := by
  induction K with
  | zero =>
    rw [show 2 * 0 + 2 = 2 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.range_zero, Finset.sum_empty, zero_add,
      show (1 : ℕ) = 2 * 0 + 1 by omega,
      integral_odd_pow_mul_meanStress_eq_zero hc tr ht 0, mul_zero, add_zero,
      Finset.range_one, Finset.sum_singleton, mul_zero]
  | succ K ih =>
    rw [show 2 * (K + 1) + 2 = (2 * K + 2) + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      show 2 * K + 2 + 1 = 2 * (K + 1) + 1 by omega,
      integral_odd_pow_mul_meanStress_eq_zero hc tr ht (K + 1), mul_zero, add_zero,
      Finset.sum_range_succ (fun k => C_r (2 * k) * ∫ ξ : ℝ, ξ ^ (2 * k) * meanStress tr t ξ) (K + 1),
      show 2 * (K + 1) = 2 * K + 2 by omega]

/-- Antidiagonal sum re-indexing:
`∑ j ∈ range (N + 1), ∑ kl ∈ antidiagonal j, Φ kl.1 kl.2 = ∑ l ∈ range (N + 1), ∑ k ∈ range (N - l + 1), Φ k l`. -/
private theorem sum_range_antidiagonal_eq (N : ℕ) (Φ : ℕ → ℕ → ℝ) :
    (∑ j ∈ Finset.range (N + 1),
        ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j, Φ kl.1 kl.2) =
      ∑ l ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N - l + 1), Φ k l := by
  have hanti : ∀ j : ℕ,
      (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j, Φ kl.1 kl.2) =
        ∑ l ∈ Finset.range (j + 1), Φ (j - l) l := by
    intro j
    refine Finset.sum_bij (fun kl _ => kl.2)
      (fun kl hkl => Finset.mem_range.2
        (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hkl; omega))
      (fun kl₁ h₁ kl₂ h₂ h => by
        have e1 := Finset.HasAntidiagonal.mem_antidiagonal.1 h₁
        have e2 := Finset.HasAntidiagonal.mem_antidiagonal.1 h₂
        ext <;> omega)
      (fun l hl => ⟨(j - l, l), Finset.HasAntidiagonal.mem_antidiagonal.2
        (by have := Finset.mem_range.1 hl; omega), rfl⟩)
      (fun kl hkl => by
        have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hkl
        rw [show j - kl.2 = kl.1 by omega])
  induction N with
  | zero =>
    rw [Finset.range_one, Finset.sum_singleton, hanti 0, Finset.sum_singleton]
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, hanti (N + 1),
      Finset.sum_range_succ (fun l => ∑ k ∈ Finset.range (N + 1 - l + 1), Φ k l) (N + 1),
      Finset.sum_range_succ (fun l => Φ (N + 1 - l) l) (N + 1)]
    simp only [Nat.sub_self, zero_add, Finset.range_one, Finset.sum_singleton]
    rw [← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have h_eq : N - l + 1 = N + 1 - l := by omega
    rw [h_eq, ← Finset.sum_range_succ]

/-! ### 6. Base case `ℓ = 0`: weighted bound on `iteratedDeriv b (meanSourceRemainder tr N s) η` -/

private theorem abs_pow_le_one_add_sq_pow {r K : ℕ} (hr : r ≤ 2 * K) (ξ : ℝ) :
    |ξ| ^ r ≤ (1 + ξ ^ 2) ^ K := by
  rcases le_total |ξ| 1 with hξ1 | hξ1
  · calc |ξ| ^ r ≤ 1 := pow_le_one₀ (abs_nonneg ξ) hξ1
      _ ≤ (1 + ξ ^ 2) ^ K := one_le_pow₀ (by linarith [sq_nonneg ξ])
  · calc |ξ| ^ r ≤ |ξ| ^ (2 * K) := pow_le_pow_right₀ hξ1 hr
      _ = (|ξ| ^ 2) ^ K := by rw [pow_mul]
      _ = (ξ ^ 2) ^ K := by rw [sq_abs]
      _ ≤ (1 + ξ ^ 2) ^ K := pow_le_pow_left₀ (sq_nonneg ξ) (by linarith) K

private def nearTaylorRem (ν : ℝ) (N b : ℕ) (s t η ξ : ℝ) : ℝ :=
  iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) -
    ∑ l ∈ Finset.range (N + 1), ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
      ∑ r ∈ Finset.range (2 * (N - l) + 2),
        (r.factorial : ℝ)⁻¹ *
          ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η)

private theorem near_taylor_kernel_bound (N m b : ℕ) {D_band : ℝ} (hD_band_pos : 0 < D_band)
    (hBand : ∀ {ν c s a : ℝ}, 0 < ν → ν ≤ 1 → 0 ≤ c → 1 ≤ s →
      a ∈ Icc (ν * (s / 2)) (ν * s) → ∀ (η ξ : ℝ) {θ : ℝ}, θ ∈ Icc (0 : ℝ) 1 →
        |η| ^ m * |iteratedDeriv (b + 2 * N + 2) (heatKernel1 a) (η - θ * ξ)| ≤
          (1 + |ξ|) ^ m *
            (polyP D_band (b + 2 * N + 2 + 1) ν c *
              s ^ (((m : ℝ) - (b + 2 * N + 2 : ℕ) - 1) / 2)))
    {ν c s t : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 ≤ c) (hs : 1 ≤ s)
    (ht : t ∈ Ioc (0 : ℝ) (s / 2)) (η ξ : ℝ) :
    |η| ^ m * |nearTaylorRem ν N b s t η ξ| ≤
      ((N : ℝ) + 2) * (2 : ℝ) ^ m * (1 + t ^ (N + 1)) * (1 + ξ ^ 2) ^ (m + N + 1) *
        (polyP D_band (b + 2 * N + 2 + 1) ν c *
          s ^ (((m : ℝ) - (b + 2 * N + 2 : ℕ) - 1) / 2)) := by
  set B : ℕ := b + 2 * N + 2
  set K_band : ℝ := polyP D_band (B + 1) ν c * s ^ (((m : ℝ) - (B : ℕ) - 1) / 2)
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hK_nn : 0 ≤ K_band := by
    dsimp [K_band]; unfold polyP; positivity
  set M_step : ℝ := (2 : ℝ) ^ m * (1 + t ^ (N + 1)) * (1 + ξ ^ 2) ^ (m + N + 1) * K_band
  have hM_nn : 0 ≤ M_step := by
    dsimp [M_step]; have := ht.1.le; positivity
  -- 1. Time Taylor expansion of `θ ↦ |η|^m * (-(ν * t))^k * ∂_η^{b + 2k} G_{ν(s - θ t)}(η - ξ)`
  let g_t : ℕ → ℝ → ℝ := fun k θ =>
    |η| ^ m * ((-(ν * t)) ^ k * iteratedDeriv (b + 2 * k) (heatKernel1 (ν * (s - θ * t))) (η - ξ))
  have hd_t : ∀ k : ℕ, ∀ θ ∈ Ioo (-1 / 2 : ℝ) (3 / 2), HasDerivAt (g_t k) (g_t (k + 1) θ) θ := by
    intro k θ hθ
    have ha : 0 < ν * (s - θ * t) := by
      have : θ * t < s := by nlinarith [hθ.2, ht.1, ht.2, hs]
      exact mul_pos hν (sub_pos.2 this)
    have hlin : HasDerivAt (fun θ' : ℝ => ν * (s - θ' * t)) (-(ν * t)) θ := by
      have h1 : HasDerivAt (fun θ' : ℝ => s - θ' * t) (-t) θ := by
        exact (((hasDerivAt_id' θ).mul_const t).const_sub s).congr_deriv (by ring)
      refine (h1.const_mul ν).congr_deriv (by ring)
    have hcomp := (hasDerivAt_iteratedDeriv_heatKernel1_width ha (b + 2 * k) (η - ξ)).comp θ hlin
    have hmul := (hcomp.const_mul ((-(ν * t)) ^ k)).const_mul (|η| ^ m)
    refine hmul.congr_deriv ?_
    dsimp [g_t]
    rw [show b + 2 * (k + 1) = b + 2 * k + 2 by omega, pow_succ]
    ring
  have hbd_t : ∀ θ ∈ Icc (0 : ℝ) 1, |g_t (N + 1) θ| ≤ M_step := by
    intro θ hθ
    dsimp [g_t]
    rw [show b + 2 * (N + 1) = B by omega, abs_mul, abs_mul,
      abs_of_nonneg (pow_nonneg (abs_nonneg η) m), abs_pow, abs_neg,
      abs_of_pos (mul_pos hν ht.1)]
    have ha_mem : ν * (s - θ * t) ∈ Icc (ν * (s / 2)) (ν * s) :=
      ⟨mul_le_mul_of_nonneg_left (by nlinarith [hθ.2, ht.1, ht.2]) hν.le,
       mul_le_mul_of_nonneg_left (by nlinarith [hθ.1, ht.1]) hν.le⟩
    have h1 := hBand hν hν1 hc hs ha_mem η ξ (θ := 1) ⟨zero_le_one, le_rfl⟩
    rw [one_mul] at h1
    have hνt : (ν * t) ^ (N + 1) ≤ 1 + t ^ (N + 1) := by
      rw [mul_pow]
      have hν_pow : ν ^ (N + 1) ≤ 1 := pow_le_one₀ hν.le hν1
      have ht_pow : t ^ (N + 1) ≤ 1 + t ^ (N + 1) := pow_le_one_add_pow ht.1.le le_rfl
      calc ν ^ (N + 1) * t ^ (N + 1) ≤ 1 * t ^ (N + 1) :=
            mul_le_mul_of_nonneg_right hν_pow (pow_nonneg ht.1.le _)
        _ ≤ 1 + t ^ (N + 1) := by linarith
    have hjap := pow_mul_one_add_abs_le_jap m N 0 (by omega) ξ
    rw [mul_zero, pow_zero, one_mul] at hjap
    calc |η| ^ m * ((ν * t) ^ (N + 1) * |iteratedDeriv B (heatKernel1 (ν * (s - θ * t))) (η - ξ)|)
        = (ν * t) ^ (N + 1) * (|η| ^ m * |iteratedDeriv B (heatKernel1 (ν * (s - θ * t))) (η - ξ)|) := by
          ring
      _ ≤ (1 + t ^ (N + 1)) * ((1 + |ξ|) ^ m * K_band) :=
          mul_le_mul hνt h1 (by positivity) (by have := ht.1.le; positivity)
      _ = (1 + t ^ (N + 1)) * (1 + |ξ|) ^ m * K_band := by ring
      _ ≤ (1 + t ^ (N + 1)) * ((2 : ℝ) ^ m * (1 + ξ ^ 2) ^ (m + N + 1)) * K_band :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hjap (by have := ht.1.le; positivity)) hK_nn
      _ = M_step := by dsimp [M_step]; ring
  have htaylor_t := taylor_unit_interval_bound g_t N hM_nn hd_t hbd_t
  have htaylor_t' : |η| ^ m *
      |iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) -
        ∑ l ∈ Finset.range (N + 1),
          ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
            iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ)| ≤ M_step := by
    have heq : g_t 0 1 - ∑ l ∈ Finset.range (N + 1), (l.factorial : ℝ)⁻¹ * g_t l 0 =
        |η| ^ m * (iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) -
          ∑ l ∈ Finset.range (N + 1),
            ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
              iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ)) := by
      dsimp [g_t]
      rw [pow_zero, one_mul, one_mul, zero_mul, sub_zero, mul_sub (|η| ^ m), Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [heq, abs_mul, abs_of_nonneg (pow_nonneg (abs_nonneg η) m)] at htaylor_t
    exact htaylor_t
  -- 2. Spatial Taylor expansion for each `l ∈ Finset.range (N + 1)`
  have htaylor_ξ : ∀ l ∈ Finset.range (N + 1),
      |η| ^ m * |((-(ν * t)) ^ l / (l.factorial : ℝ)) *
        (iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ) -
          ∑ r ∈ Finset.range (2 * (N - l) + 2),
            (r.factorial : ℝ)⁻¹ *
              ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η))| ≤ M_step := by
    intro l hl
    have hl_le : l ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    set M_ξ : ℝ := (2 : ℝ) ^ m * (1 + ξ ^ 2) ^ (m + N + 1) * K_band
    have hM_ξ_nn : 0 ≤ M_ξ := by dsimp [M_ξ]; positivity
    let g_ξ : ℕ → ℝ → ℝ := fun r θ =>
      |η| ^ m * ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) (η - ξ * θ))
    have hd_ξ : ∀ r : ℕ, ∀ θ ∈ Ioo (-1 / 2 : ℝ) (3 / 2), HasDerivAt (g_ξ r) (g_ξ (r + 1) θ) θ := by
      intro r θ _
      have h1 := hasDerivAt_iteratedDeriv_heatKernel1_space (ν * s) (b + 2 * l + r) η θ ξ
      have hmul := (h1.const_mul ((-ξ) ^ r)).const_mul (|η| ^ m)
      refine hmul.congr_deriv ?_
      dsimp [g_ξ]
      rw [show b + 2 * l + (r + 1) = b + 2 * l + r + 1 by omega, pow_succ]
      ring
    have hbd_ξ : ∀ θ ∈ Icc (0 : ℝ) 1, |g_ξ (2 * (N - l) + 1 + 1) θ| ≤ M_ξ := by
      intro θ hθ
      dsimp [g_ξ]
      have hB_eq : b + 2 * l + (2 * (N - l) + 1 + 1) = B := by omega
      have hr_eq : 2 * (N - l) + 1 + 1 = 2 * (N - l + 1) := by omega
      rw [hB_eq, hr_eq, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (abs_nonneg η) m),
        abs_pow, abs_neg, show η - ξ * θ = η - θ * ξ by ring]
      have ha_mem : ν * s ∈ Icc (ν * (s / 2)) (ν * s) :=
        ⟨by nlinarith [hs0, hν], le_rfl⟩
      have h1 := hBand hν hν1 hc hs ha_mem η ξ hθ
      have hjap := pow_mul_one_add_abs_le_jap m N (N - l + 1) (by omega) ξ
      calc |η| ^ m * (|ξ| ^ (2 * (N - l + 1)) * |iteratedDeriv B (heatKernel1 (ν * s)) (η - θ * ξ)|)
          = |ξ| ^ (2 * (N - l + 1)) *
              (|η| ^ m * |iteratedDeriv B (heatKernel1 (ν * s)) (η - θ * ξ)|) := by ring
        _ ≤ |ξ| ^ (2 * (N - l + 1)) * ((1 + |ξ|) ^ m * K_band) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (|ξ| ^ (2 * (N - l + 1)) * (1 + |ξ|) ^ m) * K_band := by ring
        _ ≤ ((2 : ℝ) ^ m * (1 + ξ ^ 2) ^ (m + N + 1)) * K_band :=
            mul_le_mul_of_nonneg_right hjap hK_nn
        _ = M_ξ := rfl
    have htaylor := taylor_unit_interval_bound g_ξ (2 * (N - l) + 1) hM_ξ_nn hd_ξ hbd_ξ
    have heq : g_ξ 0 1 - ∑ r ∈ Finset.range (2 * (N - l) + 1 + 1), (r.factorial : ℝ)⁻¹ * g_ξ r 0 =
        |η| ^ m * (iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ) -
          ∑ r ∈ Finset.range (2 * (N - l) + 2),
            (r.factorial : ℝ)⁻¹ *
              ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η)) := by
      dsimp [g_ξ]
      rw [pow_zero, one_mul, mul_one, mul_zero, sub_zero, mul_sub (|η| ^ m), Finset.mul_sum,
        show 2 * (N - l) + 1 + 1 = 2 * (N - l) + 2 by omega]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [heq, abs_mul, abs_of_nonneg (pow_nonneg (abs_nonneg η) m)] at htaylor
    have hcoeff : |(-(ν * t)) ^ l / (l.factorial : ℝ)| ≤ 1 + t ^ (N + 1) := by
      rw [abs_div, abs_pow, abs_neg, abs_of_pos (mul_pos hν ht.1),
        abs_of_pos (Nat.cast_pos.2 (Nat.factorial_pos l)), mul_pow]
      have hfact1 : (1 : ℝ) ≤ (l.factorial : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos l)
      have hν_pow : ν ^ l ≤ 1 := pow_le_one₀ hν.le hν1
      have ht_pow : t ^ l ≤ 1 + t ^ (N + 1) := pow_le_one_add_pow ht.1.le (by omega)
      calc ν ^ l * t ^ l / (l.factorial : ℝ)
          ≤ ν ^ l * t ^ l := div_le_self (by have := ht.1; positivity) hfact1
        _ ≤ 1 * t ^ l := mul_le_mul_of_nonneg_right hν_pow (pow_nonneg ht.1.le l)
        _ ≤ 1 + t ^ (N + 1) := by linarith
    rw [abs_mul, show |η| ^ m * (|(-(ν * t)) ^ l / (l.factorial : ℝ)| *
        |iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ) -
          ∑ r ∈ Finset.range (2 * (N - l) + 2),
            (r.factorial : ℝ)⁻¹ *
              ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η)|) =
      |(-(ν * t)) ^ l / (l.factorial : ℝ)| *
        (|η| ^ m * |iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ) -
          ∑ r ∈ Finset.range (2 * (N - l) + 2),
            (r.factorial : ℝ)⁻¹ *
              ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η)|) by ring]
    calc |(-(ν * t)) ^ l / (l.factorial : ℝ)| *
          (|η| ^ m * |iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ) -
            ∑ r ∈ Finset.range (2 * (N - l) + 2),
              (r.factorial : ℝ)⁻¹ *
                ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η)|)
        ≤ (1 + t ^ (N + 1)) * M_ξ :=
          mul_le_mul hcoeff htaylor (by positivity) (by have := ht.1.le; positivity)
      _ = M_step := by dsimp [M_ξ, M_step]; ring
  -- 3. Combine the time and spatial Taylor remainders
  have hdecomp : nearTaylorRem ν N b s t η ξ =
      (iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) -
        ∑ l ∈ Finset.range (N + 1),
          ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
            iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ)) +
      ∑ l ∈ Finset.range (N + 1),
        ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
          (iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ) -
            ∑ r ∈ Finset.range (2 * (N - l) + 2),
              (r.factorial : ℝ)⁻¹ *
                ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η)) := by
    unfold nearTaylorRem
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  have hsum_ξ : |η| ^ m *
      |∑ l ∈ Finset.range (N + 1),
        ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
          (iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ) -
            ∑ r ∈ Finset.range (2 * (N - l) + 2),
              (r.factorial : ℝ)⁻¹ *
                ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η))| ≤
      ((N : ℝ) + 1) * M_step := by
    calc |η| ^ m * |∑ l ∈ Finset.range (N + 1), _|
        ≤ |η| ^ m * ∑ l ∈ Finset.range (N + 1),
            |((-(ν * t)) ^ l / (l.factorial : ℝ)) *
              (iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ) -
                ∑ r ∈ Finset.range (2 * (N - l) + 2),
                  (r.factorial : ℝ)⁻¹ *
                    ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η))| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ = ∑ l ∈ Finset.range (N + 1), |η| ^ m *
            |((-(ν * t)) ^ l / (l.factorial : ℝ)) *
              (iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ) -
                ∑ r ∈ Finset.range (2 * (N - l) + 2),
                  (r.factorial : ℝ)⁻¹ *
                    ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η))| :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ _l ∈ Finset.range (N + 1), M_step := Finset.sum_le_sum htaylor_ξ
      _ = ((N : ℝ) + 1) * M_step := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  calc |η| ^ m * |nearTaylorRem ν N b s t η ξ|
      ≤ |η| ^ m *
          (|iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) -
              ∑ l ∈ Finset.range (N + 1),
                ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
                  iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ)| +
            |∑ l ∈ Finset.range (N + 1),
              ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
                (iteratedDeriv (b + 2 * l) (heatKernel1 (ν * s)) (η - ξ) -
                  ∑ r ∈ Finset.range (2 * (N - l) + 2),
                    (r.factorial : ℝ)⁻¹ *
                      ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η))|) := by
        rw [hdecomp]
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
    _ ≤ M_step + ((N : ℝ) + 1) * M_step := by
        rw [mul_add]
        exact add_le_add htaylor_t' hsum_ξ
    _ = ((N : ℝ) + 2) * (2 : ℝ) ^ m * (1 + t ^ (N + 1)) * (1 + ξ ^ 2) ^ (m + N + 1) * K_band := by
        dsimp [M_step]; ring

private def meanSourceCoeff_integrand {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : ℕ) (t : ℝ) : ℝ :=
  ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
    ((-(ν * t)) ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
      ∫ ξ : ℝ, ξ ^ (2 * kl.1) * meanStress tr t ξ

private def meanSourceCoeff_near {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : ℕ) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(s / 2), meanSourceCoeff_integrand tr j t

private def meanSourceCoeff_far {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : ℕ) (s : ℝ) : ℝ :=
  ∫ t in Ioi (s / 2), meanSourceCoeff_integrand tr j t

private def P_near {ν c : ℝ} (tr : B0140.TrainSol ν c) (N : ℕ) (s η : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    meanSourceCoeff_near tr j s * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) η

private def P_far {ν c : ℝ} (tr : B0140.TrainSol ν c) (N : ℕ) (s η : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    meanSourceCoeff_far tr j s * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) η

private theorem integrable_pow_mul_meanStress_of_jap {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {t : ℝ} (ht : 0 < t) {K r : ℕ} (hr : r ≤ 2 * K)
    (hint : Integrable (fun ξ : ℝ => (1 + ξ ^ 2) ^ K * |meanStress tr t ξ|) volume) :
    Integrable (fun ξ : ℝ => ξ ^ r * meanStress tr t ξ) volume ∧
      |∫ ξ : ℝ, ξ ^ r * meanStress tr t ξ| ≤
        ∫ ξ : ℝ, (1 + ξ ^ 2) ^ K * |meanStress tr t ξ| := by
  have hcont : Continuous (fun ξ : ℝ => ξ ^ r * meanStress tr t ξ) :=
    (continuous_pow r).mul (PartI_T23.continuous_meanStress hc.le tr ht.le)
  have hpt : ∀ ξ : ℝ, ‖ξ ^ r * meanStress tr t ξ‖ ≤ (1 + ξ ^ 2) ^ K * |meanStress tr t ξ| := by
    intro ξ
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (abs_pow_le_one_add_sq_pow hr ξ) (abs_nonneg _)
  refine ⟨hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall hpt), ?_⟩
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)

private theorem aestronglyMeasurable_moment_meanStress {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (r : ℕ) {S : Set ℝ} (hS : MeasurableSet S) (hS_sub : S ⊆ Ioi 0) :
    AEStronglyMeasurable (fun t : ℝ => ∫ ξ : ℝ, ξ ^ r * meanStress tr t ξ)
      (volume.restrict S) := by
  let G : ℝ × ℝ → ℝ := (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).indicator
    (fun x : ℝ × ℝ => x.2 ^ r * meanStress tr x.1 x.2)
  have hU_meas : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    (isOpen_Ioi.prod isOpen_univ).measurableSet
  have hG_contOn : ContinuousOn (fun x : ℝ × ℝ => x.2 ^ r * meanStress tr x.1 x.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    (continuousOn_snd.pow r).mul (PartI_T23.contDiffOn_meanStress hc tr).continuousOn
  have hG_aem : AEStronglyMeasurable G (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (aestronglyMeasurable_indicator_iff hU_meas).2 (hG_contOn.aestronglyMeasurable hU_meas)
  have h_int_aem : AEStronglyMeasurable (fun t : ℝ => ∫ ξ : ℝ, G (t, ξ)) volume :=
    hG_aem.integral_prod_right'
  refine h_int_aem.restrict.congr ?_
  filter_upwards [ae_restrict_mem hS] with t ht
  have ht0 : 0 < t := hS_sub ht
  congr 1; funext ξ
  have hmem : ((t, ξ) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨ht0, mem_univ ξ⟩
  simp [G, hmem]

private theorem aestronglyMeasurable_meanSourceCoeff_integrand {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (j : ℕ) {S : Set ℝ} (hS : MeasurableSet S) (hS_sub : S ⊆ Ioi 0) :
    AEStronglyMeasurable (meanSourceCoeff_integrand tr j) (volume.restrict S) := by
  unfold meanSourceCoeff_integrand
  refine Finset.aestronglyMeasurable_fun_sum _ fun kl _ => ?_
  have hc_t : Continuous (fun t : ℝ =>
      (-(ν * t)) ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) := by
    fun_prop
  exact hc_t.aestronglyMeasurable.mul
    (aestronglyMeasurable_moment_meanStress hc tr (2 * kl.1) hS hS_sub)

private theorem abs_meanSourceCoeff_integrand_le {ν c : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hc : 0 < c) (tr : B0140.TrainSol ν c) {N m j : ℕ} (hj : j ≤ N) {t I_t : ℝ} (ht : 0 < t)
    (hint : Integrable (fun ξ : ℝ => (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|) volume)
    (hIt : (∫ ξ : ℝ, (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|) ≤ I_t) :
    |meanSourceCoeff_integrand tr j t| ≤
      ((N : ℝ) + 1) * (1 + t ^ (N + 1)) * I_t := by
  have hIt_nn : 0 ≤ I_t :=
    (integral_nonneg fun ξ => by positivity).trans hIt
  unfold meanSourceCoeff_integrand
  have hterm : ∀ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
      |((-(ν * t)) ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
          ∫ ξ : ℝ, ξ ^ (2 * kl.1) * meanStress tr t ξ| ≤
        (1 + t ^ (N + 1)) * I_t := by
    intro kl hkl
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.1 hkl
    have hkl1 : 2 * kl.1 ≤ 2 * (m + N + 1) := by omega
    have hkl2 : kl.2 ≤ N + 1 := by omega
    rw [abs_mul, abs_div, abs_pow, abs_neg, abs_of_pos (mul_pos hν ht),
      abs_of_pos (mul_pos (Nat.cast_pos.2 (Nat.factorial_pos kl.2))
        (Nat.cast_pos.2 (Nat.factorial_pos (2 * kl.1)))), mul_pow]
    have hden1 : (1 : ℝ) ≤ (kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ) := by
      have h1 : (1 : ℝ) ≤ (kl.2.factorial : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos kl.2)
      have h2 : (1 : ℝ) ≤ ((2 * kl.1).factorial : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (2 * kl.1))
      nlinarith
    have hcoeff : ν ^ kl.2 * t ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ)) ≤
        1 + t ^ (N + 1) := by
      calc ν ^ kl.2 * t ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))
          ≤ ν ^ kl.2 * t ^ kl.2 := div_le_self (by positivity) hden1
        _ ≤ 1 * t ^ kl.2 :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hν.le hν1) (pow_nonneg ht.le _)
        _ ≤ 1 + t ^ (N + 1) := by linarith [pow_le_one_add_pow ht.le hkl2]
    have hmom := (integrable_pow_mul_meanStress_of_jap hc tr ht hkl1 hint).2.trans hIt
    exact mul_le_mul hcoeff hmom (abs_nonneg _) (by positivity)
  have hcard : ((Finset.HasAntidiagonal.antidiagonal j).card : ℝ) ≤ (N : ℝ) + 1 := by
    have hbij : (Finset.HasAntidiagonal.antidiagonal j).card = (Finset.range (j + 1)).card := by
      refine Finset.card_bij (fun kl _ => kl.1)
        (fun kl hkl => Finset.mem_range.2
          (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hkl; omega))
        (fun kl₁ h₁ kl₂ h₂ h => by
          have e1 := Finset.HasAntidiagonal.mem_antidiagonal.1 h₁
          have e2 := Finset.HasAntidiagonal.mem_antidiagonal.1 h₂
          ext <;> omega)
        (fun k hk => ⟨(k, j - k), Finset.HasAntidiagonal.mem_antidiagonal.2
          (by have := Finset.mem_range.1 hk; omega), rfl⟩)
    rw [hbij, Finset.card_range]
    exact_mod_cast Nat.succ_le_succ hj
  calc |∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j, _|
      ≤ ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j,
          |((-(ν * t)) ^ kl.2 / ((kl.2.factorial : ℝ) * ((2 * kl.1).factorial : ℝ))) *
            ∫ ξ : ℝ, ξ ^ (2 * kl.1) * meanStress tr t ξ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _kl ∈ Finset.HasAntidiagonal.antidiagonal j, ((1 + t ^ (N + 1)) * I_t) :=
        Finset.sum_le_sum hterm
    _ = ((Finset.HasAntidiagonal.antidiagonal j).card : ℝ) * ((1 + t ^ (N + 1)) * I_t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((N : ℝ) + 1) * ((1 + t ^ (N + 1)) * I_t) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((N : ℝ) + 1) * (1 + t ^ (N + 1)) * I_t := by ring

private theorem near_time_slice_eq {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (N m b : ℕ) {s t : ℝ} (hat : 0 < ν * (s - t)) (ht : 0 < t)
    (hint : Integrable (fun ξ : ℝ => (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|) volume)
    (η : ℝ) :
    Integrable (fun ξ : ℝ => nearTaylorRem ν N b s t η ξ * meanStress tr t ξ) volume ∧
      (∫ ξ : ℝ, iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) * meanStress tr t ξ) -
        (∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff_integrand tr j t *
            iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η) =
      ∫ ξ : ℝ, nearTaylorRem ν N b s t η ξ * meanStress tr t ξ := by
  -- 1. Integrability of `iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) * meanStress tr t ξ`
  obtain ⟨C_b, hC_b_pos, hC_b⟩ := abs_iteratedDeriv_heatKernel1_le_of_ge b
  set K_b : ℝ := ((Real.sqrt (ν * (s - t)))⁻¹) ^ (b + 1) * C_b
  have hint_lead : Integrable
      (fun ξ : ℝ => iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) * meanStress tr t ξ)
      volume := by
    have hcont : Continuous
        (fun ξ : ℝ => iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) * meanStress tr t ξ) :=
      ((contDiff_iteratedDeriv _ (contDiff_heatKernel1 _) b).continuous.comp
        (continuous_const.sub continuous_id)).mul (PartI_T23.continuous_meanStress hc.le tr ht.le)
    refine (hint.const_mul K_b).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hC_b hat le_rfl (η - ξ)
    have h2 : |meanStress tr t ξ| ≤ (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ| :=
      le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ (by linarith [sq_nonneg ξ]))
    exact mul_le_mul h1 h2 (abs_nonneg _) (by dsimp [K_b]; positivity)
  -- 2. Integrability of moments `ξ ^ r * meanStress tr t ξ` for `r ≤ 2 * N + 1`
  have hint_mom : ∀ r ≤ 2 * N + 1,
      Integrable (fun ξ : ℝ => ξ ^ r * meanStress tr t ξ) volume :=
    fun r hr => (integrable_pow_mul_meanStress_of_jap hc tr ht (by omega) hint).1
  -- 3. Rewrite the finite sum into a single integral over `ξ`
  let Φ : ℕ → ℕ → ℝ := fun k l =>
    ((-(ν * t)) ^ l / ((l.factorial : ℝ) * ((2 * k).factorial : ℝ))) *
      iteratedDeriv (b + 2 * (k + l)) (heatKernel1 (ν * s)) η *
      ∫ ξ : ℝ, ξ ^ (2 * k) * meanStress tr t ξ
  have hsum1 : (∑ j ∈ Finset.range (N + 1),
        meanSourceCoeff_integrand tr j t *
          iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η) =
      ∑ l ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N - l + 1), Φ k l := by
    rw [← sum_range_antidiagonal_eq N Φ]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold meanSourceCoeff_integrand
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    have hj_eq : kl.1 + kl.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.1 hkl
    dsimp [Φ]
    rw [hj_eq]
    ring
  let C_lr : ℕ → ℕ → ℝ := fun l r =>
    ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
      ((r.factorial : ℝ)⁻¹ *
        ((-1 : ℝ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η))
  have hsum2 : (∑ l ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N - l + 1), Φ k l) =
      ∑ l ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (2 * (N - l) + 2),
        C_lr l r * ∫ ξ : ℝ, ξ ^ r * meanStress tr t ξ := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sum_range_mul_integral_meanStress_eq_even hc tr ht.le (N - l) (C_lr l)]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [Φ, C_lr]
    have hneg_even : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
    rw [hneg_even, one_mul, show b + 2 * (k + l) = b + 2 * l + 2 * k by omega]
    ring
  have hsum3 : (∑ l ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (2 * (N - l) + 2),
        C_lr l r * ∫ ξ : ℝ, ξ ^ r * meanStress tr t ξ) =
      ∫ ξ : ℝ,
        (∑ l ∈ Finset.range (N + 1), ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
          ∑ r ∈ Finset.range (2 * (N - l) + 2),
            (r.factorial : ℝ)⁻¹ *
              ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η)) *
          meanStress tr t ξ := by
    have hint_lr : ∀ l ∈ Finset.range (N + 1), ∀ r ∈ Finset.range (2 * (N - l) + 2),
        Integrable (fun ξ : ℝ => C_lr l r * (ξ ^ r * meanStress tr t ξ)) volume := by
      intro l hl r hr
      have hl' : l ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      have hr' : r ≤ 2 * (N - l) + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
      exact (hint_mom r (by omega)).const_mul (C_lr l r)
    have h_in : ∀ l ∈ Finset.range (N + 1),
        (∑ r ∈ Finset.range (2 * (N - l) + 2),
          C_lr l r * ∫ ξ : ℝ, ξ ^ r * meanStress tr t ξ) =
        ∫ ξ : ℝ, ∑ r ∈ Finset.range (2 * (N - l) + 2),
          C_lr l r * (ξ ^ r * meanStress tr t ξ) := by
      intro l hl
      simp_rw [← integral_const_mul]
      exact (integral_finsetSum (Finset.range (2 * (N - l) + 2)) (hint_lr l hl)).symm
    rw [Finset.sum_congr rfl h_in,
      ← integral_finsetSum (Finset.range (N + 1)) (fun l hl =>
        integrable_finsetSum _ (hint_lr l hl))]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    dsimp [C_lr]
    have hneg_pow : (-ξ) ^ r = (-1 : ℝ) ^ r * ξ ^ r := by
      rw [← mul_pow]; ring_nf
    rw [hneg_pow]
    ring
  have hint_poly : Integrable
      (fun ξ : ℝ =>
        (∑ l ∈ Finset.range (N + 1), ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
          ∑ r ∈ Finset.range (2 * (N - l) + 2),
            (r.factorial : ℝ)⁻¹ *
              ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η)) *
          meanStress tr t ξ) volume := by
    have h_eq : (fun ξ : ℝ =>
        (∑ l ∈ Finset.range (N + 1), ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
          ∑ r ∈ Finset.range (2 * (N - l) + 2),
            (r.factorial : ℝ)⁻¹ *
              ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η)) *
          meanStress tr t ξ) =
      fun ξ : ℝ => ∑ l ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (2 * (N - l) + 2),
        C_lr l r * (ξ ^ r * meanStress tr t ξ) := by
      funext ξ
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      dsimp [C_lr]
      have hneg_pow : (-ξ) ^ r = (-1 : ℝ) ^ r * ξ ^ r := by
        rw [← mul_pow]; ring_nf
      rw [hneg_pow]
      ring
    rw [h_eq]
    refine integrable_finsetSum _ fun l hl => integrable_finsetSum _ fun r hr => ?_
    have hl' : l ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have hr' : r ≤ 2 * (N - l) + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    exact (hint_mom r (by omega)).const_mul (C_lr l r)
  have hint_rem : Integrable (fun ξ : ℝ => nearTaylorRem ν N b s t η ξ * meanStress tr t ξ) volume := by
    have hfun : (fun ξ : ℝ => nearTaylorRem ν N b s t η ξ * meanStress tr t ξ) =
        fun ξ : ℝ =>
          iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) * meanStress tr t ξ -
            (∑ l ∈ Finset.range (N + 1), ((-(ν * t)) ^ l / (l.factorial : ℝ)) *
              ∑ r ∈ Finset.range (2 * (N - l) + 2),
                (r.factorial : ℝ)⁻¹ *
                  ((-ξ) ^ r * iteratedDeriv (b + 2 * l + r) (heatKernel1 (ν * s)) η)) *
              meanStress tr t ξ := by
      funext ξ; unfold nearTaylorRem; ring
    rw [hfun]
    exact hint_lead.sub hint_poly
  refine ⟨hint_rem, ?_⟩
  rw [hsum1, hsum2, hsum3, ← integral_sub hint_lead hint_poly]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  unfold nearTaylorRem
  ring

private theorem bound_D_far
    (hFD : TrainFluctuationDecay)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (N m b : ℕ) :
    ∃ C_dfar : ℝ, ∃ M_dfar : ℕ, ∃ ν_dfar : ℝ, 0 < C_dfar ∧ 0 < ν_dfar ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν_dfar → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        let c := trainPeriod ρ ν
        ∀ s : ℝ, 1 ≤ s →
          ContDiff ℝ b (D_far tr s) ∧
          ∀ η : ℝ,
            |η| ^ m * |iteratedDeriv b (D_far tr s) η| ≤
              polyP C_dfar M_dfar ν c * s ^ (((m : ℝ) - b - 2 * N - 3) / 2) := by
  set α : ℝ := ((m : ℝ) - b - 2 * N - 3) / 2
  have hα_ge : -((b + 2 * N + 3 : ℕ) : ℝ) ≤ α := by
    dsimp [α]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    push_cast
    linarith
  obtain ⟨C_fb, M_fb, κ_fb, ν_fb, hC_fb, hκ_fb, hν_fb, hDecay_fb⟩ :=
    PartI_T23.meanStress_weighted_jet_decay_of_fluctDecay hFD ρ hρ m b 0
  choose C_fk M_fk κ_fk ν_fk hC_fk hκ_fk hν_fk hDecay_fk using fun k : ℕ =>
    PartI_T23.meanStress_weighted_jet_decay_of_fluctDecay hFD ρ hρ 0 k 0
  set ν_far : ℝ := (Finset.range (b + 2)).inf' ⟨0, Finset.mem_range.2 (by omega)⟩ ν_fk
  have hν_far : 0 < ν_far := (Finset.lt_inf'_iff _).2 fun k _ => hν_fk k
  obtain ⟨C_abs_f, M_abs_f, hC_abs_f, hAbs_f⟩ :=
    rpow_mul_exp_le_polyP_mul_rpow (half_pos hκ_fb) (m + 1) (b + 2 * N + 3) hα_ge
  have hIz_int : Integrable (fun z : ℝ => (1 + |z|) ^ m * heatKernel1 1 z) volume := by
    have h0 := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := 0) (by norm_num)
    have hM := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := (m : ℝ))
      (by have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith)
    have hdom : Integrable (fun z : ℝ =>
        (2 : ℝ) ^ m * (Real.sqrt (4 * Real.pi * 1))⁻¹ *
          (|z| ^ (0 : ℝ) * Real.exp (-(1 / 4) * z ^ 2) +
            |z| ^ (m : ℝ) * Real.exp (-(1 / 4) * z ^ 2))) volume :=
      ((h0.abs.congr (Eventually.of_forall fun z => by
          dsimp; rw [abs_mul, abs_of_pos (Real.exp_pos _), Real.rpow_zero, abs_one,
            Real.rpow_zero])).add
        (hM.abs.congr (Eventually.of_forall fun z => by
          dsimp; rw [abs_mul, abs_of_pos (Real.exp_pos _), Real.rpow_natCast, abs_pow,
            Real.rpow_natCast]))).const_mul _
    have hcont : Continuous (fun z : ℝ => (1 + |z|) ^ m * heatKernel1 1 z) :=
      ((continuous_const.add continuous_abs).pow m).mul (contDiff_heatKernel1 1).continuous
    refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    have hK1_nn : 0 ≤ heatKernel1 1 z := by unfold heatKernel1; positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg hK1_nn]
    have hpow : (1 + |z|) ^ m ≤ (2 : ℝ) ^ m * (1 + |z| ^ m) :=
      UnforcedLeray.Short.PartIIa.pow_one_add_le m (abs_nonneg z)
    unfold heatKernel1
    rw [show -(z ^ 2) / (4 * 1) = -(1 / 4) * z ^ 2 by ring, Real.rpow_zero, Real.rpow_natCast]
    calc (1 + |z|) ^ m * ((Real.sqrt (4 * Real.pi * 1))⁻¹ * Real.exp (-(1 / 4) * z ^ 2))
        ≤ ((2 : ℝ) ^ m * (1 + |z| ^ m)) *
            ((Real.sqrt (4 * Real.pi * 1))⁻¹ * Real.exp (-(1 / 4) * z ^ 2)) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = _ := by ring
  set I_z : ℝ := max (∫ z : ℝ, (1 + |z|) ^ m * heatKernel1 1 z) 1
  have hIz_pos : 0 < I_z := lt_max_of_lt_right one_pos
  set C_dfar : ℝ := (2 : ℝ) ^ m * I_z * C_fb * C_abs_f
  have hC_dfar_pos : 0 < C_dfar := by dsimp only [C_dfar]; positivity
  set M_dfar : ℕ := M_fb + M_abs_f
  set ν_dfar : ℝ := min 1 (min ν_far ν_fb)
  refine ⟨C_dfar, M_dfar, ν_dfar, hC_dfar_pos, lt_min one_pos (lt_min hν_far hν_fb), ?_⟩
  intro ν hν hν_le tr htr c s hs
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_left _ _)
  have hν_far_le : ν ≤ ν_far := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_fb_le : ν ≤ ν_fb := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc1 : 1 ≤ c := by
    dsimp [c, trainPeriod]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  let B_fn : ℕ → ℝ := fun k => polyP (C_fk k) (M_fk k) ν c
  have hB_nn : ∀ k ≤ b + 1, 0 ≤ B_fn k :=
    fun k _ => by have := hC_fk k; dsimp only [B_fn, polyP]; positivity
  have hB_bd : ∀ k ≤ b + 1, ∀ t : ℝ, 0 < t → ∀ y : ℝ,
      |iteratedDeriv k (meanStress tr t) y| ≤ B_fn k := by
    intro k hk t ht y
    have hνk : ν ≤ ν_fk k :=
      hν_far_le.trans (Finset.inf'_le _ (Finset.mem_range.2 (by omega)))
    have h := hDecay_fk k ν hν hνk tr htr t ht y
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
    have hexp1 : Real.exp (-(κ_fk k * ν * t / c ^ 2)) ≤ 1 := by
      rw [← Real.exp_zero]; apply Real.exp_le_exp.2
      have := hκ_fk k
      have hpos : 0 ≤ κ_fk k * ν * t / c ^ 2 := by positivity
      linarith only [hpos]
    exact h.trans (mul_le_of_le_one_right (hB_nn k hk) hexp1)
  obtain ⟨hD_far_deriv, hD_far_cd⟩ := iteratedDeriv_D_far b hν hc0 tr B_fn hB_nn hB_bd hs
  refine ⟨hD_far_cd, fun η => ?_⟩
  rw [hD_far_deriv η]
  have hs2_le_s : s / 2 ≤ s := by linarith only [hs0]
  rw [intervalIntegral.integral_of_le hs2_le_s,
    ← abs_of_nonneg (pow_nonneg (abs_nonneg η) m), ← abs_mul, ← integral_const_mul,
    ← Real.norm_eq_abs]
  set P_fb : ℝ := polyP C_fb M_fb ν c
  have hP_fb_nn : 0 ≤ P_fb := by dsimp only [P_fb, polyP]; positivity
  set E_fb : ℝ := Real.exp (-(κ_fb / 2 * ν * s / c ^ 2))
  set K_z : ℝ := (2 : ℝ) ^ m * s ^ m * P_fb * E_fb
  have hKz_nn : 0 ≤ K_z := by dsimp only [K_z, E_fb]; positivity
  have hpt_far : ∀ t ∈ Ioc (s / 2) s,
      ‖|η| ^ m * ∫ z : ℝ,
        heatKernel1 1 z * iteratedDeriv b (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z)‖ ≤
        K_z * I_z := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < s / 2) ht.1.le
    rw [← integral_const_mul]
    have hdom_z : Integrable (fun z : ℝ => K_z * ((1 + |z|) ^ m * heatKernel1 1 z)) volume :=
      hIz_int.const_mul K_z
    have hpt_z : ∀ z : ℝ,
        ‖|η| ^ m * (heatKernel1 1 z *
          iteratedDeriv b (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z))‖ ≤
          K_z * ((1 + |z|) ^ m * heatKernel1 1 z) := by
      intro z
      set y : ℝ := η - Real.sqrt (ν * (s - t)) * z
      have hK1_nn : 0 ≤ heatKernel1 1 z := by unfold heatKernel1; positivity
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (pow_nonneg (abs_nonneg η) m), abs_of_nonneg hK1_nn]
      have hsq_le : Real.sqrt (ν * (s - t)) ≤ s := by
        have h1 : ν * (s - t) ≤ s ^ 2 := by
          have hst_le : ν * (s - t) ≤ 1 * s :=
            mul_le_mul hν1 (by linarith only [ht.1, hs0]) (sub_nonneg.2 ht.2) zero_le_one
          nlinarith only [hst_le, hs]
        calc Real.sqrt (ν * (s - t)) ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt h1
          _ = s := Real.sqrt_sq hs0.le
      have hη_le : |η| ≤ 2 * s * (1 + |z|) * (1 + y ^ 2) := by
        have h1 : |η| ≤ |y| + |Real.sqrt (ν * (s - t)) * z| := by
          simpa [y, sub_add_cancel] using abs_add_le y (Real.sqrt (ν * (s - t)) * z)
        have h2 : |Real.sqrt (ν * (s - t)) * z| ≤ s * |z| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact mul_le_mul_of_nonneg_right hsq_le (abs_nonneg z)
        have h3 : |y| + s * |z| ≤ s * (1 + |z|) * (1 + |y|) := by
          have hy1 : (1 - s) * |y| ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) (abs_nonneg y)
          have hzy : 0 ≤ s * |z| * |y| := by positivity
          linarith only [hy1, hzy, hs]
        have h4 : 1 + |y| ≤ 2 * (1 + y ^ 2) := by
          have hsq1 := sq_nonneg (|y| - 1)
          have hsq2 := sq_abs y
          nlinarith only [hsq1, hsq2]
        calc |η| ≤ |y| + s * |z| := h1.trans (add_le_add le_rfl h2)
          _ ≤ s * (1 + |z|) * (1 + |y|) := h3
          _ ≤ s * (1 + |z|) * (2 * (1 + y ^ 2)) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = 2 * s * (1 + |z|) * (1 + y ^ 2) := by ring
      have hη_pow : |η| ^ m ≤ (2 : ℝ) ^ m * s ^ m * (1 + |z|) ^ m * (1 + y ^ 2) ^ m := by
        calc |η| ^ m ≤ (2 * s * (1 + |z|) * (1 + y ^ 2)) ^ m :=
              pow_le_pow_left₀ (abs_nonneg η) hη_le m
          _ = (2 : ℝ) ^ m * s ^ m * (1 + |z|) ^ m * (1 + y ^ 2) ^ m := by
              rw [mul_pow, mul_pow, mul_pow]
      have hms_bd := hDecay_fb ν hν hν_fb_le tr htr t ht0 y
      simp only [iteratedDeriv_zero] at hms_bd
      have hexp_le : Real.exp (-(κ_fb * ν * t / c ^ 2)) ≤ E_fb := by
        dsimp only [E_fb]
        apply Real.exp_le_exp.2
        have ht1 := ht.1
        have h1 : κ_fb / 2 * ν * s ≤ κ_fb * ν * t := by
          rw [show κ_fb / 2 * ν * s = (κ_fb * ν) * (s / 2) by ring,
              show κ_fb * ν * t = (κ_fb * ν) * t by ring]
          exact mul_le_mul_of_nonneg_left (by linarith only [ht1]) (by positivity)
        have h2 : κ_fb / 2 * ν * s / c ^ 2 ≤ κ_fb * ν * t / c ^ 2 :=
          div_le_div_of_nonneg_right h1 (sq_nonneg c)
        linarith only [h2]
      have hms_bd' : (1 + y ^ 2) ^ m * |iteratedDeriv b (meanStress tr t) y| ≤ P_fb * E_fb :=
        hms_bd.trans (mul_le_mul_of_nonneg_left hexp_le hP_fb_nn)
      calc |η| ^ m * (heatKernel1 1 z * |iteratedDeriv b (meanStress tr t) y|)
          ≤ ((2 : ℝ) ^ m * s ^ m * (1 + |z|) ^ m * (1 + y ^ 2) ^ m) *
              (heatKernel1 1 z * |iteratedDeriv b (meanStress tr t) y|) :=
            mul_le_mul_of_nonneg_right hη_pow (by positivity)
        _ = ((2 : ℝ) ^ m * s ^ m * ((1 + |z|) ^ m * heatKernel1 1 z)) *
              ((1 + y ^ 2) ^ m * |iteratedDeriv b (meanStress tr t) y|) := by ring
        _ ≤ ((2 : ℝ) ^ m * s ^ m * ((1 + |z|) ^ m * heatKernel1 1 z)) * (P_fb * E_fb) :=
            mul_le_mul_of_nonneg_left hms_bd' (by positivity)
        _ = K_z * ((1 + |z|) ^ m * heatKernel1 1 z) := by dsimp only [K_z]; ring
    calc ‖∫ z : ℝ, |η| ^ m *
          (heatKernel1 1 z * iteratedDeriv b (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z))‖
        ≤ ∫ z : ℝ, K_z * ((1 + |z|) ^ m * heatKernel1 1 z) :=
          norm_integral_le_of_norm_le hdom_z (Eventually.of_forall hpt_z)
      _ = K_z * ∫ z : ℝ, (1 + |z|) ^ m * heatKernel1 1 z := integral_const_mul _ _
      _ ≤ K_z * I_z := mul_le_mul_of_nonneg_left (le_max_left _ _) hKz_nn
  have hint_bd := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Ioc (s / 2) s) measure_Ioc_lt_top hpt_far
  rw [Real.volume_real_Ioc_of_le hs2_le_s] at hint_bd
  have hs_len : s - s / 2 ≤ s := by linarith only [hs0]
  have habs_f := hAbs_f hν hc0 hs
  calc ‖∫ t in Ioc (s / 2) s,
        |η| ^ m * ∫ z : ℝ,
          heatKernel1 1 z * iteratedDeriv b (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z)‖
      ≤ K_z * I_z * (s - s / 2) := hint_bd
    _ ≤ K_z * I_z * s :=
        mul_le_mul_of_nonneg_left hs_len (mul_nonneg hKz_nn hIz_pos.le)
    _ = (2 : ℝ) ^ m * I_z * P_fb * (s ^ (m + 1) * E_fb) := by
        dsimp only [K_z]; rw [pow_succ]; ring
    _ ≤ (2 : ℝ) ^ m * I_z * P_fb * (polyP C_abs_f M_abs_f ν c * s ^ α) :=
        mul_le_mul_of_nonneg_left habs_f
          (mul_nonneg (mul_nonneg (by positivity) hIz_pos.le) hP_fb_nn)
    _ = polyP C_dfar M_dfar ν c * s ^ α := by
        dsimp only [P_fb, C_dfar, M_dfar]
        unfold polyP
        rw [pow_add]
        ring

private theorem trainMeanSourceRemainderBound_zero
    (hFD : TrainFluctuationDecay)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (N m b : ℕ) :
    ∃ C : ℝ, ∃ M : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        let c := trainPeriod ρ ν
        ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
          |η| ^ m * |iteratedDeriv b (meanSourceRemainder tr N s) η| ≤
            polyP C M ν c * s ^ (((m : ℝ) - b - 2 * N - 3) / 2) := by
  set B : ℕ := b + 2 * N + 2
  set α : ℝ := ((m : ℝ) - b - 2 * N - 3) / 2
  have hα_B : ((m : ℝ) - B - 1) / 2 = α := by
    dsimp [B, α]; push_cast; ring
  have hα_ge : -((b + 2 * N + 3 : ℕ) : ℝ) ≤ α := by
    dsimp [α]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    push_cast
    linarith
  -- 1. Heat-kernel bounds
  obtain ⟨D_band, hD_band_pos, hBand⟩ := heatKernel1_band_bound m B
  choose D_jet hD_jet_pos hJet using fun j : ℕ =>
    PartI_T23.heatKernel1_weighted_jet_bound m (b + 2 * j) 0
  set D_sum : ℝ := ∑ j ∈ Finset.range (N + 1), D_jet j
  have hD_sum_pos : 0 < D_sum :=
    Finset.sum_pos (fun j _ => hD_jet_pos j) ⟨0, Finset.mem_range.2 (Nat.succ_pos N)⟩
  -- 2. Fluctuation decay bounds for `meanStress` and `D_far` bound
  obtain ⟨C_w, M_w, κ_w, ν_w, hC_w, hκ_w, hν_w, hDecay_w⟩ :=
    PartI_T23.meanStress_weighted_jet_decay_of_fluctDecay hFD ρ hρ (m + N + 2) 0 0
  obtain ⟨C_dfar, M_dfar, ν_dfar, hC_dfar_pos, hν_dfar, hD_far_all⟩ :=
    bound_D_far hFD ρ hρ N m b
  -- 3. Time-integral and exponential-absorption bounds
  obtain ⟨C_ti_w, M_ti_w, hC_ti_w, hInt_w⟩ :=
    integral_one_add_pow_mul_exp_Ioi N (half_pos hκ_w)
  obtain ⟨C_abs_p, M_abs_p, hC_abs_p, hAbs_p⟩ :=
    rpow_mul_exp_le_polyP_mul_rpow (by positivity : 0 < κ_w / 4) m (b + 2 * N + 3) hα_ge
  -- 4. Assemble the total constants `C_tot`, `M_tot`, `ν₀`
  set C_near : ℝ := ((N : ℝ) + 2) * (2 : ℝ) ^ m * Real.pi * D_band * C_w * C_ti_w
  have hC_near_pos : 0 < C_near := by dsimp only [C_near]; positivity
  set M_near : ℕ := (B + 1) + M_w + M_ti_w
  set C_pfar : ℝ := ((N : ℝ) + 1) * Real.pi * C_w * C_ti_w * D_sum * C_abs_p
  have hC_pfar_pos : 0 < C_pfar := by dsimp only [C_pfar]; positivity
  set M_pfar : ℕ := M_w + M_ti_w + (b + 2 * N + 1) + M_abs_p
  set C_tot : ℝ := C_near + C_pfar + C_dfar
  set M_tot : ℕ := max M_near (max M_pfar M_dfar)
  set ν₀ : ℝ := min 1 (min ν_w ν_dfar)
  refine ⟨C_tot, M_tot, ν₀, by dsimp only [C_tot]; positivity,
    lt_min one_pos (lt_min hν_w hν_dfar), ?_⟩
  intro ν hν hν_le tr htr c s hs η
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_left _ _)
  have hν_w_le : ν ≤ ν_w := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_dfar_le : ν ≤ ν_dfar := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc1 : 1 ≤ c := by
    dsimp [c, trainPeriod]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hs2 : 0 ≤ s / 2 := by positivity
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  -- Pointwise decay of `meanStress` at weight `m + N + 2`
  set P_w : ℝ := polyP C_w M_w ν c
  have hPw_nn : 0 ≤ P_w := by dsimp only [P_w, polyP]; positivity
  have h_ms_w : ∀ t : ℝ, 0 < t → ∀ ξ : ℝ,
      (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ| ≤
        P_w * Real.exp (-(κ_w * ν * t / c ^ 2)) * (1 + ξ ^ 2)⁻¹ := by
    intro t ht ξ
    have h := hDecay_w ν hν hν_w_le tr htr t ht ξ
    simp only [iteratedDeriv_zero] at h
    rw [le_mul_inv_iff₀ (by positivity)]
    calc (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ| * (1 + ξ ^ 2)
        = (1 + ξ ^ 2) ^ (m + N + 2) * |meanStress tr t ξ| := by
          rw [show m + N + 2 = (m + N + 1) + 1 by omega, pow_succ]; ring
      _ ≤ P_w * Real.exp (-(κ_w * ν * t / c ^ 2)) := h
  have h_ms_1 : ∀ t : ℝ, 0 < t → ∀ ξ : ℝ, (1 + ξ ^ 2) * |meanStress tr t ξ| ≤ P_w := by
    intro t ht ξ
    have h := h_ms_w t ht ξ
    rw [le_mul_inv_iff₀ (by positivity)] at h
    have h1 : 1 + ξ ^ 2 ≤ (1 + ξ ^ 2) ^ (m + N + 1) * (1 + ξ ^ 2) :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by linarith [sq_nonneg ξ]))
    have hexp1 : Real.exp (-(κ_w * ν * t / c ^ 2)) ≤ 1 := by
      rw [← Real.exp_zero]; apply Real.exp_le_exp.2
      have : 0 ≤ κ_w * ν * t / c ^ 2 := by positivity
      linarith
    calc (1 + ξ ^ 2) * |meanStress tr t ξ|
        ≤ (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ| * (1 + ξ ^ 2) := by
          nlinarith [abs_nonneg (meanStress tr t ξ)]
      _ ≤ P_w * Real.exp (-(κ_w * ν * t / c ^ 2)) := h
      _ ≤ P_w * 1 := mul_le_mul_of_nonneg_left hexp1 hPw_nn
      _ = P_w := mul_one _
  have h_int_w : ∀ t : ℝ, 0 < t →
      Integrable (fun ξ : ℝ => (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|) volume ∧
      (∫ ξ : ℝ, (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|) ≤
        Real.pi * P_w * Real.exp (-(κ_w * ν * t / c ^ 2)) := by
    intro t ht
    have hdom : Integrable
        (fun ξ : ℝ => P_w * Real.exp (-(κ_w * ν * t / c ^ 2)) * (1 + ξ ^ 2)⁻¹) volume :=
      integrable_inv_one_add_sq.const_mul _
    have hcont : Continuous (fun ξ : ℝ => (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|) :=
      ((continuous_const.add (continuous_pow 2)).pow _).mul
        (PartI_T23.continuous_meanStress hc0.le tr ht.le).abs
    have hint : Integrable (fun ξ : ℝ => (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|) volume := by
      refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact h_ms_w t ht ξ
    refine ⟨hint, ?_⟩
    calc (∫ ξ : ℝ, (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|)
        ≤ ∫ ξ : ℝ, P_w * Real.exp (-(κ_w * ν * t / c ^ 2)) * (1 + ξ ^ 2)⁻¹ :=
          integral_mono hint hdom (fun ξ => h_ms_w t ht ξ)
      _ = Real.pi * P_w * Real.exp (-(κ_w * ν * t / c ^ 2)) := by
          rw [integral_const_mul, integral_univ_inv_one_add_sq]; ring
  obtain ⟨hD_near_deriv, hD_near_cd, hD_near_int⟩ := iteratedDeriv_D_near b hν hc0 tr h_ms_1 hs
  obtain ⟨hD_far_cd, hD_far_bd⟩ := hD_far_all ν hν hν_dfar_le tr htr s hs
  obtain ⟨hInt_w_on, hInt_w_bd⟩ := hInt_w hν hc1
  have hexp_half : ∀ t : ℝ, 0 < t →
      Real.exp (-(κ_w * ν * t / c ^ 2)) ≤ Real.exp (-(κ_w / 2 * ν * t / c ^ 2)) := by
    intro t ht
    apply Real.exp_le_exp.2
    have hpos : 0 ≤ κ_w * ν * t / c ^ 2 := by positivity
    have heq : κ_w / 2 * ν * t / c ^ 2 = (κ_w * ν * t / c ^ 2) / 2 := by ring
    linarith only [hpos, heq]
  -- Integrability and splitting of `meanSourceCoeff tr j` for `j ≤ N`
  have hCoeff_split : ∀ j ≤ N,
      IntervalIntegrable (meanSourceCoeff_integrand tr j) volume 0 (s / 2) ∧
      IntegrableOn (meanSourceCoeff_integrand tr j) (Ioi (s / 2)) volume ∧
      meanSourceCoeff tr j = meanSourceCoeff_near tr j s + meanSourceCoeff_far tr j s ∧
      |meanSourceCoeff_far tr j s| ≤
        ((N : ℝ) + 1) * Real.pi * P_w * polyP C_ti_w M_ti_w ν c *
          Real.exp (-(κ_w / 4 * ν * s / c ^ 2)) := by
    intro j hj
    set K_c : ℝ := ((N : ℝ) + 1) * Real.pi * P_w
    have hKc_nn : 0 ≤ K_c := by dsimp only [K_c]; positivity
    have hpt_Ioi : ∀ t : ℝ, 0 < t →
        |meanSourceCoeff_integrand tr j t| ≤
          K_c * ((1 + t ^ (N + 1)) * Real.exp (-(κ_w * ν * t / c ^ 2))) := by
      intro t ht
      have h := abs_meanSourceCoeff_integrand_le hν hν1 hc0 tr hj ht
        (h_int_w t ht).1 (h_int_w t ht).2
      calc |meanSourceCoeff_integrand tr j t|
          ≤ ((N : ℝ) + 1) * (1 + t ^ (N + 1)) *
              (Real.pi * P_w * Real.exp (-(κ_w * ν * t / c ^ 2))) := h
        _ = K_c * ((1 + t ^ (N + 1)) * Real.exp (-(κ_w * ν * t / c ^ 2))) := by
            dsimp only [K_c]; ring
    have hint_Ioi : IntegrableOn (meanSourceCoeff_integrand tr j) (Ioi 0) volume := by
      refine (hInt_w_on.const_mul K_c).mono'
        (aestronglyMeasurable_meanSourceCoeff_integrand hc0 tr j measurableSet_Ioi Subset.rfl) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      rw [Real.norm_eq_abs]
      exact (hpt_Ioi t ht0).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hexp_half t ht0) (by have := ht0.le; positivity)) hKc_nn)
    have hint_Ioc : IntegrableOn (meanSourceCoeff_integrand tr j) (Ioc 0 (s / 2)) volume :=
      hint_Ioi.mono_set Ioc_subset_Ioi_self
    have hint_far : IntegrableOn (meanSourceCoeff_integrand tr j) (Ioi (s / 2)) volume :=
      hint_Ioi.mono_set (Ioi_subset_Ioi hs2)
    have hsplit : meanSourceCoeff tr j =
        meanSourceCoeff_near tr j s + meanSourceCoeff_far tr j s := by
      change (∫ t in Ioi (0 : ℝ), meanSourceCoeff_integrand tr j t) =
        (∫ t in (0 : ℝ)..(s / 2), meanSourceCoeff_integrand tr j t) +
          (∫ t in Ioi (s / 2), meanSourceCoeff_integrand tr j t)
      rw [intervalIntegral.integral_of_le hs2, ← Ioc_union_Ioi_eq_Ioi hs2,
        setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint_Ioc hint_far]
    have hfar_bd : |meanSourceCoeff_far tr j s| ≤
        K_c * polyP C_ti_w M_ti_w ν c * Real.exp (-(κ_w / 4 * ν * s / c ^ 2)) := by
      unfold meanSourceCoeff_far
      rw [← Real.norm_eq_abs]
      set E_s : ℝ := Real.exp (-(κ_w / 4 * ν * s / c ^ 2))
      have hdom_far : IntegrableOn
          (fun t : ℝ => (K_c * E_s) * ((1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2))))
          (Ioi (s / 2)) volume :=
        (hInt_w_on.mono_set (Ioi_subset_Ioi hs2)).const_mul (K_c * E_s)
      have hpt_far : ∀ t ∈ Ioi (s / 2),
          ‖meanSourceCoeff_integrand tr j t‖ ≤
            (K_c * E_s) * ((1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2))) := by
        intro t ht
        have ht0 : 0 < t := lt_of_le_of_lt hs2 ht
        rw [Real.norm_eq_abs]
        have hexp_split : Real.exp (-(κ_w * ν * t / c ^ 2)) ≤
            E_s * Real.exp (-(κ_w / 2 * ν * t / c ^ 2)) := by
          dsimp only [E_s]
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          have ht_gt : s / 2 < t := ht
          have h1 : κ_w / 4 * ν * s ≤ κ_w / 2 * ν * t := by
            rw [show κ_w / 4 * ν * s = (κ_w * ν) * (s / 4) by ring,
                show κ_w / 2 * ν * t = (κ_w * ν) * (t / 2) by ring]
            exact mul_le_mul_of_nonneg_left (by linarith only [ht_gt]) (by positivity)
          have h2 : κ_w / 4 * ν * s / c ^ 2 ≤ κ_w / 2 * ν * t / c ^ 2 :=
            div_le_div_of_nonneg_right h1 (sq_nonneg c)
          have heq : κ_w / 2 * ν * t / c ^ 2 = (κ_w * ν * t / c ^ 2) / 2 := by ring
          linarith only [h2, heq]
        calc |meanSourceCoeff_integrand tr j t|
            ≤ K_c * ((1 + t ^ (N + 1)) * Real.exp (-(κ_w * ν * t / c ^ 2))) := hpt_Ioi t ht0
          _ ≤ K_c * ((1 + t ^ (N + 1)) * (E_s * Real.exp (-(κ_w / 2 * ν * t / c ^ 2)))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hexp_split (by positivity)) hKc_nn
          _ = (K_c * E_s) * ((1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2))) := by ring
      calc ‖∫ t in Ioi (s / 2), meanSourceCoeff_integrand tr j t‖
          ≤ ∫ t in Ioi (s / 2),
              (K_c * E_s) * ((1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2))) :=
            norm_integral_le_of_norm_le hdom_far ((ae_restrict_mem measurableSet_Ioi).mono hpt_far)
        _ = (K_c * E_s) *
              ∫ t in Ioi (s / 2), (1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2)) :=
            integral_const_mul _ _
        _ ≤ (K_c * E_s) *
              ∫ t in Ioi (0 : ℝ), (1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by dsimp only [E_s]; positivity)
            exact setIntegral_mono_set hInt_w_on
              ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
                have : 0 < t := ht; positivity)
              (Eventually.of_forall (Ioi_subset_Ioi hs2))
        _ ≤ (K_c * E_s) * polyP C_ti_w M_ti_w ν c :=
            mul_le_mul_of_nonneg_left hInt_w_bd (by dsimp only [E_s]; positivity)
        _ = K_c * polyP C_ti_w M_ti_w ν c * E_s := by ring
    exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hs2).2 hint_Ioc,
      hint_far, hsplit, hfar_bd⟩
  -- Decomposition of `iteratedDeriv b (meanSourceRemainder tr N s) η`
  have hP_near_cd : ContDiff ℝ ∞ (P_near tr N s) :=
    ContDiff.sum fun j _ => contDiff_const.mul
      (contDiff_iteratedDeriv _ (contDiff_heatKernel1 (ν * s)) (2 * j))
  have hP_far_cd : ContDiff ℝ ∞ (P_far tr N s) :=
    ContDiff.sum fun j _ => contDiff_const.mul
      (contDiff_iteratedDeriv _ (contDiff_heatKernel1 (ν * s)) (2 * j))
  have hP_near_deriv : iteratedDeriv b (P_near tr N s) η =
      ∑ j ∈ Finset.range (N + 1),
        meanSourceCoeff_near tr j s * iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η := by
    unfold P_near
    rw [iteratedDeriv_finset_sum (Finset.range (N + 1)) _ b η fun j _ =>
      (contDiff_const.mul
        (contDiff_iteratedDeriv _ (contDiff_heatKernel1 (ν * s)) (2 * j))).contDiffAt]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_iteratedDeriv]
  have hP_far_deriv : iteratedDeriv b (P_far tr N s) η =
      ∑ j ∈ Finset.range (N + 1),
        meanSourceCoeff_far tr j s * iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η := by
    unfold P_far
    rw [iteratedDeriv_finset_sum (Finset.range (N + 1)) _ b η fun j _ =>
      (contDiff_const.mul
        (contDiff_iteratedDeriv _ (contDiff_heatKernel1 (ν * s)) (2 * j))).contDiffAt]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_iteratedDeriv]
  have hrem_fun : meanSourceRemainder tr N s =
      ((D_near tr s - P_near tr N s) - P_far tr N s) + D_far tr s := by
    funext e
    change meanSourceRemainder tr N s e =
      ((D_near tr s e - P_near tr N s e) - P_far tr N s e) + D_far tr s e
    unfold meanSourceRemainder P_near P_far
    rw [meanSourceDuhamel_eq_add hν hc0 tr htr hs e]
    have hsum_split : (∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) e) =
        (∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff_near tr j s * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) e) +
        (∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff_far tr j s * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) e) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [(hCoeff_split j hj').2.2.1, add_mul]
    rw [hsum_split]
    ring
  have hrem_deriv : iteratedDeriv b (meanSourceRemainder tr N s) η =
      (iteratedDeriv b (D_near tr s) η - iteratedDeriv b (P_near tr N s) η) -
        iteratedDeriv b (P_far tr N s) η + iteratedDeriv b (D_far tr s) η := by
    have h1 : ContDiffAt ℝ b (D_near tr s) η := hD_near_cd.contDiffAt
    have h2 : ContDiffAt ℝ b (P_near tr N s) η :=
      hP_near_cd.contDiffAt.of_le (by exact_mod_cast le_top)
    have h3 : ContDiffAt ℝ b (P_far tr N s) η :=
      hP_far_cd.contDiffAt.of_le (by exact_mod_cast le_top)
    have h4 : ContDiffAt ℝ b (D_far tr s) η := hD_far_cd.contDiffAt
    have h12 : ContDiffAt ℝ b (D_near tr s - P_near tr N s) η := h1.sub h2
    have h123 : ContDiffAt ℝ b ((D_near tr s - P_near tr N s) - P_far tr N s) η := h12.sub h3
    rw [hrem_fun, iteratedDeriv_add h123 h4,
      iteratedDeriv_sub h12 h3, iteratedDeriv_sub h1 h2]
  -- Bound Piece 1: `|η| ^ m * |iteratedDeriv b (D_near tr s) η - iteratedDeriv b (P_near tr N s) η|`
  have hPiece1 : |η| ^ m *
      |iteratedDeriv b (D_near tr s) η - iteratedDeriv b (P_near tr N s) η| ≤
      polyP C_near M_near ν c * s ^ α := by
    rw [hD_near_deriv η, hP_near_deriv]
    have hP_int_eq : (∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff_near tr j s * iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η) =
        ∫ t in (0 : ℝ)..(s / 2),
          ∑ j ∈ Finset.range (N + 1),
            meanSourceCoeff_integrand tr j t *
              iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η := by
      unfold meanSourceCoeff_near
      simp_rw [← intervalIntegral.integral_mul_const]
      exact (intervalIntegral.integral_finsetSum fun j hj =>
        ((hCoeff_split j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).1).mul_const _).symm
    have hD_int := hD_near_int η
    have hP_int : IntervalIntegrable
        (fun t => ∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff_integrand tr j t *
            iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η)
        volume 0 (s / 2) := by
      simpa only [Finset.sum_fn] using IntervalIntegrable.sum (Finset.range (N + 1)) fun j hj =>
        ((hCoeff_split j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).1).mul_const
          (iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η)
    rw [hP_int_eq, ← intervalIntegral.integral_sub hD_int hP_int,
      intervalIntegral.integral_of_le hs2]
    set K_band : ℝ := polyP D_band (B + 1) ν c * s ^ (((m : ℝ) - (B : ℕ) - 1) / 2)
    have hK_band_nn : 0 ≤ K_band := by dsimp only [K_band, polyP]; positivity
    set K_t : ℝ := ((N : ℝ) + 2) * (2 : ℝ) ^ m * (Real.pi * P_w) * K_band
    have hK_t_nn : 0 ≤ K_t := by dsimp only [K_t]; positivity
    have hdom_t : IntegrableOn
        (fun t : ℝ => K_t * ((1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2))))
        (Ioc 0 (s / 2)) volume :=
      (hInt_w_on.mono_set Ioc_subset_Ioi_self).const_mul K_t
    have hpt_t : ∀ t ∈ Ioc (0 : ℝ) (s / 2),
        ‖|η| ^ m *
          ((∫ ξ : ℝ, iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) * meanStress tr t ξ) -
            ∑ j ∈ Finset.range (N + 1),
              meanSourceCoeff_integrand tr j t *
                iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η)‖ ≤
          K_t * ((1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2))) := by
      intro t ht
      have hat : 0 < ν * (s - t) := by
        have : 0 < s - t := by linarith only [ht.2, hs0]
        exact mul_pos hν this
      obtain ⟨hint_rem, hslice_eq⟩ := near_time_slice_eq hc0 tr N m b hat ht.1 (h_int_w t ht.1).1 η
      rw [hslice_eq, ← integral_const_mul]
      set C_ξ : ℝ := ((N : ℝ) + 2) * (2 : ℝ) ^ m * (1 + t ^ (N + 1)) * K_band
      have hC_ξ_nn : 0 ≤ C_ξ := by dsimp only [C_ξ]; have := ht.1.le; positivity
      have hdom_ξ : Integrable
          (fun ξ : ℝ => C_ξ * ((1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|)) volume :=
        ((h_int_w t ht.1).1).const_mul C_ξ
      have hpt_ξ : ∀ ξ : ℝ,
          ‖|η| ^ m * (nearTaylorRem ν N b s t η ξ * meanStress tr t ξ)‖ ≤
            C_ξ * ((1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|) := by
        intro ξ
        rw [Real.norm_eq_abs, ← mul_assoc, abs_mul, abs_mul,
          abs_of_nonneg (pow_nonneg (abs_nonneg η) m)]
        have hrem_bd := near_taylor_kernel_bound N m b hD_band_pos hBand hν hν1 hc0.le hs ht η ξ
        calc (|η| ^ m * |nearTaylorRem ν N b s t η ξ|) * |meanStress tr t ξ|
            ≤ (((N : ℝ) + 2) * (2 : ℝ) ^ m * (1 + t ^ (N + 1)) *
                (1 + ξ ^ 2) ^ (m + N + 1) * K_band) * |meanStress tr t ξ| :=
              mul_le_mul_of_nonneg_right hrem_bd (abs_nonneg _)
          _ = C_ξ * ((1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|) := by
              dsimp only [C_ξ]; ring
      calc ‖∫ ξ : ℝ, |η| ^ m * (nearTaylorRem ν N b s t η ξ * meanStress tr t ξ)‖
          ≤ ∫ ξ : ℝ, C_ξ * ((1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ|) :=
            norm_integral_le_of_norm_le hdom_ξ (Eventually.of_forall hpt_ξ)
        _ = C_ξ * ∫ ξ : ℝ, (1 + ξ ^ 2) ^ (m + N + 1) * |meanStress tr t ξ| :=
            integral_const_mul _ _
        _ ≤ C_ξ * (Real.pi * P_w * Real.exp (-(κ_w * ν * t / c ^ 2))) :=
            mul_le_mul_of_nonneg_left (h_int_w t ht.1).2 hC_ξ_nn
        _ ≤ C_ξ * (Real.pi * P_w * Real.exp (-(κ_w / 2 * ν * t / c ^ 2))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hexp_half t ht.1) (by positivity)) hC_ξ_nn
        _ = K_t * ((1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2))) := by
            dsimp only [C_ξ, K_t]; ring
    rw [← abs_of_nonneg (pow_nonneg (abs_nonneg η) m), ← abs_mul, ← integral_const_mul,
      ← Real.norm_eq_abs]
    calc ‖∫ t in Ioc 0 (s / 2),
          |η| ^ m *
            ((∫ ξ : ℝ, iteratedDeriv b (heatKernel1 (ν * (s - t))) (η - ξ) * meanStress tr t ξ) -
              ∑ j ∈ Finset.range (N + 1),
                meanSourceCoeff_integrand tr j t *
                  iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η)‖
        ≤ ∫ t in Ioc 0 (s / 2),
            K_t * ((1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2))) :=
          norm_integral_le_of_norm_le hdom_t ((ae_restrict_mem measurableSet_Ioc).mono hpt_t)
      _ = K_t * ∫ t in Ioc 0 (s / 2), (1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2)) :=
          integral_const_mul _ _
      _ ≤ K_t * ∫ t in Ioi (0 : ℝ), (1 + t ^ (N + 1)) * Real.exp (-(κ_w / 2 * ν * t / c ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK_t_nn
          exact setIntegral_mono_set hInt_w_on
            ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
              have : 0 < t := ht; positivity)
            (Eventually.of_forall Ioc_subset_Ioi_self)
      _ ≤ K_t * polyP C_ti_w M_ti_w ν c :=
          mul_le_mul_of_nonneg_left hInt_w_bd hK_t_nn
      _ = polyP C_near M_near ν c * s ^ α := by
          dsimp only [K_t, K_band, P_w, C_near, M_near]
          rw [hα_B]
          unfold polyP
          rw [pow_add, pow_add]
          ring
  -- Bound Piece 2: `|η| ^ m * |iteratedDeriv b (P_far tr N s) η|`
  have hPiece2 : |η| ^ m * |iteratedDeriv b (P_far tr N s) η| ≤
      polyP C_pfar M_pfar ν c * s ^ α := by
    rw [hP_far_deriv]
    set K_c_far : ℝ := ((N : ℝ) + 1) * Real.pi * P_w * polyP C_ti_w M_ti_w ν c
    have hKc_far_nn : 0 ≤ K_c_far := by dsimp only [K_c_far, polyP]; positivity
    have hterm_far : ∀ j ∈ Finset.range (N + 1),
        |η| ^ m * |meanSourceCoeff_far tr j s *
          iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η| ≤
          K_c_far * polyP (D_jet j) (b + 2 * N + 1) ν c *
            (s ^ m * Real.exp (-(κ_w / 4 * ν * s / c ^ 2))) := by
      intro j hj
      have hj' : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hcf := (hCoeff_split j hj').2.2.2
      have hjet_j := hJet j hν hν1 hc0.le hs η
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hjet_j
      have hη_le : |η| ^ m ≤ (1 + |η|) ^ m :=
        pow_le_pow_left₀ (abs_nonneg η) (by linarith [abs_nonneg η]) m
      have hpoly_j : polyP (D_jet j) (b + 2 * j + 1) ν c ≤
          polyP (D_jet j) (b + 2 * N + 1) ν c := by
        unfold polyP
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hX1 (by omega)) (hD_jet_pos j).le
      have hexp_j : ((m : ℝ) - (b + 2 * j : ℕ) - 1) / 2 ≤ (m : ℝ) := by
        have : (0 : ℝ) ≤ (b + 2 * j : ℕ) := Nat.cast_nonneg _
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have hrpow_j : s ^ (((m : ℝ) - (b + 2 * j : ℕ) - 1) / 2) ≤ s ^ m := by
        rw [← Real.rpow_natCast s m]
        exact Real.rpow_le_rpow_of_exponent_le hs hexp_j
      have hjet_j' : |η| ^ m * |iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η| ≤
          polyP (D_jet j) (b + 2 * N + 1) ν c * s ^ m := by
        calc |η| ^ m * |iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η|
            ≤ (1 + |η|) ^ m * |iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η| :=
              mul_le_mul_of_nonneg_right hη_le (abs_nonneg _)
          _ ≤ polyP (D_jet j) (b + 2 * j + 1) ν c *
                s ^ (((m : ℝ) - (b + 2 * j : ℕ) - 1) / 2) := hjet_j
          _ ≤ polyP (D_jet j) (b + 2 * N + 1) ν c * s ^ m :=
              mul_le_mul hpoly_j hrpow_j (by positivity)
                (by unfold polyP; have := hD_jet_pos j; positivity)
      rw [abs_mul, show |η| ^ m * (|meanSourceCoeff_far tr j s| *
          |iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η|) =
        |meanSourceCoeff_far tr j s| *
          (|η| ^ m * |iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η|) by ring]
      calc |meanSourceCoeff_far tr j s| *
            (|η| ^ m * |iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η|)
          ≤ (K_c_far * Real.exp (-(κ_w / 4 * ν * s / c ^ 2))) *
              (polyP (D_jet j) (b + 2 * N + 1) ν c * s ^ m) :=
            mul_le_mul hcf hjet_j' (by positivity) (by positivity)
        _ = K_c_far * polyP (D_jet j) (b + 2 * N + 1) ν c *
              (s ^ m * Real.exp (-(κ_w / 4 * ν * s / c ^ 2))) := by ring
    have hsum_poly : (∑ j ∈ Finset.range (N + 1),
          K_c_far * polyP (D_jet j) (b + 2 * N + 1) ν c *
            (s ^ m * Real.exp (-(κ_w / 4 * ν * s / c ^ 2)))) =
        K_c_far * polyP D_sum (b + 2 * N + 1) ν c *
          (s ^ m * Real.exp (-(κ_w / 4 * ν * s / c ^ 2))) := by
      dsimp only [D_sum, polyP]
      rw [Finset.sum_mul, ← Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]
    have habs_p := hAbs_p hν hc0 hs
    calc |η| ^ m * |∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff_far tr j s * iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η|
        ≤ |η| ^ m * ∑ j ∈ Finset.range (N + 1),
            |meanSourceCoeff_far tr j s * iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ = ∑ j ∈ Finset.range (N + 1),
            |η| ^ m * |meanSourceCoeff_far tr j s *
              iteratedDeriv (b + 2 * j) (heatKernel1 (ν * s)) η| :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ Finset.range (N + 1),
            K_c_far * polyP (D_jet j) (b + 2 * N + 1) ν c *
              (s ^ m * Real.exp (-(κ_w / 4 * ν * s / c ^ 2))) :=
          Finset.sum_le_sum hterm_far
      _ = K_c_far * polyP D_sum (b + 2 * N + 1) ν c *
            (s ^ m * Real.exp (-(κ_w / 4 * ν * s / c ^ 2))) := hsum_poly
      _ ≤ K_c_far * polyP D_sum (b + 2 * N + 1) ν c *
            (polyP C_abs_p M_abs_p ν c * s ^ α) :=
          mul_le_mul_of_nonneg_left habs_p
            (mul_nonneg hKc_far_nn (by dsimp only [polyP]; positivity))
      _ = polyP C_pfar M_pfar ν c * s ^ α := by
          dsimp only [K_c_far, P_w, C_pfar, M_pfar]
          unfold polyP
          rw [pow_add, pow_add, pow_add]
          ring
  -- Bound Piece 3: `|η| ^ m * |iteratedDeriv b (D_far tr s) η|`
  have hPiece3 : |η| ^ m * |iteratedDeriv b (D_far tr s) η| ≤
      polyP C_dfar M_dfar ν c * s ^ α := hD_far_bd η
  -- Combine Pieces 1, 2, 3
  have hsα_nn : 0 ≤ s ^ α := Real.rpow_nonneg hs0.le _
  have hP1_le : polyP C_near M_near ν c ≤ polyP C_near M_tot ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hX1 (le_max_left _ _)) hC_near_pos.le
  have hP2_le : polyP C_pfar M_pfar ν c ≤ polyP C_pfar M_tot ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hX1 ((le_max_left _ _).trans (le_max_right _ _)))
      hC_pfar_pos.le
  have hP3_le : polyP C_dfar M_dfar ν c ≤ polyP C_dfar M_tot ν c := by
    unfold polyP
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hX1 ((le_max_right _ _).trans (le_max_right _ _)))
      hC_dfar_pos.le
  have h1' := hPiece1.trans (mul_le_mul_of_nonneg_right hP1_le hsα_nn)
  have h2' := hPiece2.trans (mul_le_mul_of_nonneg_right hP2_le hsα_nn)
  have h3' := hPiece3.trans (mul_le_mul_of_nonneg_right hP3_le hsα_nn)
  have htri : |iteratedDeriv b (meanSourceRemainder tr N s) η| ≤
      |iteratedDeriv b (D_near tr s) η - iteratedDeriv b (P_near tr N s) η| +
        |iteratedDeriv b (P_far tr N s) η| +
        |iteratedDeriv b (D_far tr s) η| := by
    rw [hrem_deriv]
    exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
  calc |η| ^ m * |iteratedDeriv b (meanSourceRemainder tr N s) η|
      ≤ |η| ^ m *
          (|iteratedDeriv b (D_near tr s) η - iteratedDeriv b (P_near tr N s) η| +
            |iteratedDeriv b (P_far tr N s) η| +
            |iteratedDeriv b (D_far tr s) η|) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ = |η| ^ m * |iteratedDeriv b (D_near tr s) η - iteratedDeriv b (P_near tr N s) η| +
          |η| ^ m * |iteratedDeriv b (P_far tr N s) η| +
          |η| ^ m * |iteratedDeriv b (D_far tr s) η| := by ring
    _ ≤ polyP C_near M_tot ν c * s ^ α +
          polyP C_pfar M_tot ν c * s ^ α +
          polyP C_dfar M_tot ν c * s ^ α := add_le_add (add_le_add h1' h2') h3'
    _ = polyP C_tot M_tot ν c * s ^ α := by
        dsimp only [C_tot, polyP]; ring

/-! ### 7. General `ℓ ≥ 0`: mixed-derivative symmetry and 1D heat PDE induction -/

private theorem deriv_age_eq_fderiv {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (e : ℝ) :
    HasDerivAt (fun r => F r e)
      (fderiv ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) (1, 0)) s ∧
    deriv (fun r => F r e) s =
      fderiv ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) (1, 0) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hx : ((s, e) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hs, mem_univ e⟩
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) :=
    (hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hline : HasDerivAt (fun r : ℝ => ((r, e) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s e)
  have hd := hdiff.hasFDerivAt.comp_hasDerivAt s hline
  exact ⟨hd, hd.deriv⟩

private theorem deriv_eta_eq_fderiv {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (e : ℝ) :
    HasDerivAt (fun e' => F s e')
      (fderiv ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) (0, 1)) e ∧
    deriv (fun e' => F s e') e =
      fderiv ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) (0, 1) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hx : ((s, e) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hs, mem_univ e⟩
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × ℝ => F x.1 x.2) (s, e) :=
    (hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hline : HasDerivAt (fun e' : ℝ => ((s, e') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) e :=
    (hasDerivAt_const e s).prodMk (hasDerivAt_id' e)
  have hd := hdiff.hasFDerivAt.comp_hasDerivAt e hline
  exact ⟨hd, hd.deriv⟩

private theorem deriv_age_deriv_eta_comm {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (e : ℝ) :
    deriv (fun r => deriv (F r) e) s =
      deriv (fun e' => deriv (fun r => F r e') s) e := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hx : ((s, e) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hs, mem_univ e⟩
  let Φ : ℝ × ℝ → ℝ := fun x => F x.1 x.2
  have hcd2 : ContDiffAt ℝ 2 Φ (s, e) :=
    (hF.contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  have hfd : DifferentiableAt ℝ (fderiv ℝ Φ) (s, e) :=
    (hcd2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym : IsSymmSndFDerivAt ℝ Φ (s, e) := hcd2.isSymmSndFDerivAt (by simp)
  have hF_eta : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => deriv (F x.1) x.2) (Ioi 0 ×ˢ univ) := by
    simpa [iteratedDeriv_one] using UnforcedLeray.Short.PartIIa.etaDerivIter_contDiffOn F hF 1
  have hF_age : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => deriv (fun r => F r x.2) x.1) (Ioi 0 ×ˢ univ) := by
    simpa [iteratedDeriv_one] using UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 F hF 1
  rw [(deriv_age_eq_fderiv (F := fun s' e' => deriv (F s') e') hF_eta hs e).2,
    (deriv_eta_eq_fderiv (F := fun s' e' => deriv (fun r => F r e') s') hF_age hs e).2]
  have hev_eta : (fun x : ℝ × ℝ => deriv (F x.1) x.2) =ᶠ[𝓝 (s, e)]
      (fun x : ℝ × ℝ => fderiv ℝ Φ x (0, 1)) := by
    filter_upwards [hU.mem_nhds hx] with x hx' using (deriv_eta_eq_fderiv hF hx'.1 x.2).2
  have hev_age : (fun x : ℝ × ℝ => deriv (fun r => F r x.2) x.1) =ᶠ[𝓝 (s, e)]
      (fun x : ℝ × ℝ => fderiv ℝ Φ x (1, 0)) := by
    filter_upwards [hU.mem_nhds hx] with x hx' using (deriv_age_eq_fderiv hF hx'.1 x.2).2
  have hclm (v w : ℝ × ℝ) :
      fderiv ℝ (fun z => fderiv ℝ Φ z v) (s, e) w = fderiv ℝ (fderiv ℝ Φ) (s, e) w v := by
    rw [fderiv_clm_apply hfd (differentiableAt_const v)]
    simp
  rw [hev_eta.fderiv_eq, hev_age.fderiv_eq, hclm, hclm]
  exact hsym (1, 0) (0, 1)

private theorem deriv_age_iteratedDeriv_eta_comm (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (e : ℝ) :
    deriv (fun r => iteratedDeriv k (F r) e) s =
      iteratedDeriv k (fun e' => deriv (fun r => F r e') s) e := by
  induction k generalizing e with
  | zero => simp
  | succ k ih =>
    have hFk : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv k (F x.1) x.2) (Ioi 0 ×ˢ univ) :=
      UnforcedLeray.Short.PartIIa.etaDerivIter_contDiffOn F hF k
    have hfun1 : (fun r => iteratedDeriv (k + 1) (F r) e) =
        fun r => deriv (iteratedDeriv k (F r)) e := by
      funext r; rw [iteratedDeriv_succ]
    have hfun2 : (fun e' => deriv (fun r => iteratedDeriv k (F r) e') s) =
        fun e' => iteratedDeriv k (fun y => deriv (fun r => F r y) s) e' :=
      funext ih
    rw [hfun1, deriv_age_deriv_eta_comm (F := fun r e' => iteratedDeriv k (F r) e') hFk hs e,
      hfun2, ← iteratedDeriv_succ]

private theorem iteratedDeriv_age_iteratedDeriv_eta_comm (ℓ k : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => F x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (e : ℝ) :
    iteratedDeriv ℓ (fun r => iteratedDeriv k (F r) e) s =
      iteratedDeriv k (fun e' => iteratedDeriv ℓ (fun r => F r e') s) e := by
  induction ℓ generalizing F s e with
  | zero => simp
  | succ ℓ ih =>
    have hF' : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => deriv (fun r => F r x.2) x.1) (Ioi 0 ×ˢ univ) := by
      simpa [iteratedDeriv_one] using UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 F hF 1
    have hev : deriv (fun r => iteratedDeriv k (F r) e) =ᶠ[𝓝 s]
        fun r => iteratedDeriv k (fun e' => deriv (fun r' => F r' e') r) e := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
        using deriv_age_iteratedDeriv_eta_comm k hF hr e
    have hfun : (fun e' => iteratedDeriv ℓ (fun r => deriv (fun r' => F r' e') r) s) =
        fun e' => iteratedDeriv (ℓ + 1) (fun r => F r e') s := by
      funext e'; rw [iteratedDeriv_succ']
    rw [iteratedDeriv_succ', hev.iteratedDeriv_eq ℓ,
      ih (F := fun r e' => deriv (fun r' => F r' e') r) hF' hs e, hfun]

private theorem contDiffOn_meanSourceRemainder {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (hD : ∀ r : ℝ, 0 < r → ∀ e : ℝ,
      meanStream tr r e = meanDatumDuhamel tr r e + meanSourceDuhamel tr r e)
    (N : ℕ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanSourceRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hRemSm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartIIa.meanRemainderSmooth_of
      trainMeanEquations_proof UnforcedLeray.Short.PartIIa.heatKernelIterSmooth ν c hν hc0 tr htr N
  have hDatSm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanDatumRemainder tr N x.1 x.2) (Ioi 0 ×ˢ univ) :=
    PartI_T23.contDiffOn_meanDatumRemainder hν hc1 tr N
  refine (hRemSm.sub hDatSm).congr fun x hx => ?_
  have h := PartI_T23.meanRemainder_eq_add_of_duhamel tr N (hD x.1 hx.1 x.2)
  linarith

private theorem contDiffAt_age_slice_of_contDiffOn {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => G x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) (e : ℝ) :
    ContDiffAt ℝ ℓ (fun r : ℝ => G r e) s := by
  have hφ : ContDiff ℝ ∞ (fun r : ℝ => ((r, e) : ℝ × ℝ)) :=
    contDiff_id.prodMk contDiff_const
  have hmaps : MapsTo (fun r : ℝ => ((r, e) : ℝ × ℝ)) (Ioi 0) (Ioi 0 ×ˢ univ) :=
    fun _ hr => ⟨hr, trivial⟩
  have hcomp : ContDiffOn ℝ ∞
      ((fun x : ℝ × ℝ => G x.1 x.2) ∘ (fun r : ℝ => ((r, e) : ℝ × ℝ))) (Ioi 0) :=
    hG.comp hφ.contDiffOn hmaps
  exact (hcomp.contDiffAt (isOpen_Ioi.mem_nhds hs)).of_le (by exact_mod_cast le_top)

private theorem contDiff_eta_slice_of_contDiffOn {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => G x.1 x.2) (Ioi 0 ×ˢ univ))
    (ℓ : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun e : ℝ => iteratedDeriv ℓ (fun r => G r e) s) := by
  have hH : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv ℓ (fun r => G r x.2) x.1)
      (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartIIa.ageDerivSmooth.1 G hG ℓ
  have hφ : ContDiff ℝ ∞ (fun e : ℝ => ((s, e) : ℝ × ℝ)) :=
    contDiff_const.prodMk contDiff_id
  have hmaps : MapsTo (fun e : ℝ => ((s, e) : ℝ × ℝ)) univ (Ioi 0 ×ˢ univ) :=
    fun _ _ => ⟨hs, trivial⟩
  have hcomp : ContDiffOn ℝ ∞
      ((fun x : ℝ × ℝ => iteratedDeriv ℓ (fun r => G r x.2) x.1) ∘ (fun e : ℝ => ((s, e) : ℝ × ℝ)))
      univ :=
    hH.comp (contDiffOn_univ.mpr hφ) hmaps
  exact contDiffOn_univ.mp hcomp

private theorem deriv_age_meanSourceRemainder {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (hD : ∀ r : ℝ, 0 < r → ∀ e : ℝ,
      meanStream tr r e = meanDatumDuhamel tr r e + meanSourceDuhamel tr r e)
    (N : ℕ) {s : ℝ} (hs : 0 < s) (e : ℝ) :
    deriv (fun r => meanSourceRemainder tr N r e) s =
      ν * iteratedDeriv 2 (meanSourceRemainder tr N s) e + meanStress tr s e := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  -- 1. `meanStream` time derivative from `trainMeanEquations_proof`
  have hMean := trainMeanEquations_proof ν c hν hc0 tr htr
  have hS_hd : HasDerivAt (fun r => meanStream tr r e)
      (ν * iteratedDeriv 2 (meanStream tr s) e + meanStress tr s e) s := by
    have hd := (deriv_age_eq_fderiv hMean.1 hs e).1
    have hpde := (hMean.2 s hs e).1
    have h2 : deriv (deriv (meanStream tr s)) e = iteratedDeriv 2 (meanStream tr s) e := by
      rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hd.congr_deriv (by
      rw [← (deriv_age_eq_fderiv hMean.1 hs e).2, ← h2]
      linarith only [hpde])
  -- 2. `vortexMeanStream` time derivative
  have hV_hd : HasDerivAt (fun r => vortexMeanStream ν c r e)
      (ν * iteratedDeriv 2 (vortexMeanStream ν c s) e) s := by
    have ha : 0 < 1 + ν * s := by positivity
    have hlin : HasDerivAt (fun r : ℝ => 1 + ν * r) ν s := by
      exact (((hasDerivAt_id' s).const_mul ν).const_add 1).congr_deriv (by ring)
    have h1 := ((hasDerivAt_iteratedDeriv_heatKernel1_width ha 0 e).comp s hlin).const_mul
      (-(8 * Real.pi * c⁻¹))
    refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)).congr_deriv ?_
    · dsimp
      unfold vortexMeanStream width
      simp [iteratedDeriv_zero]
    · unfold vortexMeanStream width
      rw [iteratedDeriv_const_mul_field, zero_add]
      ring
  -- 3. Polynomial sum time derivative
  have hPoly_hd : HasDerivAt
      (fun r => ∑ j ∈ Finset.range (N + 1),
        meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * r)) e)
      (ν * iteratedDeriv 2
        (fun y => ∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) y) e) s := by
    have hj_hd : ∀ j ∈ Finset.range (N + 1),
        HasDerivAt
          (fun r => meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * r)) e)
          (ν * (meanSourceCoeff tr j *
            iteratedDeriv 2 (iteratedDeriv (2 * j) (heatKernel1 (ν * s))) e)) s := by
      intro j _
      have ha : 0 < ν * s := mul_pos hν hs
      have hlin : HasDerivAt (fun r : ℝ => ν * r) ν s := by
        exact ((hasDerivAt_id' s).const_mul ν).congr_deriv (by ring)
      have h1 := ((hasDerivAt_iteratedDeriv_heatKernel1_width ha (2 * j) e).comp s hlin).const_mul
        (meanSourceCoeff tr j)
      refine h1.congr_deriv ?_
      rw [iteratedDeriv_comp_iteratedDeriv, show 2 + 2 * j = 2 * j + 2 by omega]
      ring
    refine ((HasDerivAt.sum hj_hd).congr_of_eventuallyEq
      (Eventually.of_forall fun r => by simp)).congr_deriv ?_
    rw [iteratedDeriv_finset_sum (Finset.range (N + 1)) _ 2 e fun j _ =>
      (contDiff_const.mul
        (contDiff_iteratedDeriv _ (contDiff_heatKernel1 (ν * s)) (2 * j))).contDiffAt]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDeriv_const_mul_field]
  -- 4. Combine via `meanSourceRemainder = meanStream - vortexMeanStream - sum` on `Ioi 0`
  have hev_rem : (fun r => meanSourceRemainder tr N r e) =ᶠ[𝓝 s]
      fun r => (meanStream tr r e - vortexMeanStream ν c r e) -
        ∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * r)) e := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    unfold meanSourceRemainder
    have hd_r := hD r hr e
    rw [PartI_T23.meanDatumDuhamel_eq_vortexMeanStream hν hc1 tr hr e] at hd_r
    linarith
  have hd_comb := ((hS_hd.sub hV_hd).sub hPoly_hd).congr_of_eventuallyEq hev_rem
  rw [hd_comb.deriv]
  -- Express `iteratedDeriv 2 (meanSourceRemainder tr N s) e` as the combination of the three pieces
  have hrem_s : meanSourceRemainder tr N s =
      (meanStream tr s - vortexMeanStream ν c s) -
        (fun y => ∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) y) := by
    funext y
    change meanSourceRemainder tr N s y =
      (meanStream tr s y - vortexMeanStream ν c s y) -
        ∑ j ∈ Finset.range (N + 1),
          meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) y
    unfold meanSourceRemainder
    have hd_s := hD s hs y
    rw [PartI_T23.meanDatumDuhamel_eq_vortexMeanStream hν hc1 tr hs y] at hd_s
    linarith
  have hS_cd : ContDiffAt ℝ 2 (meanStream tr s) e := by
    have h := contDiff_eta_slice_of_contDiffOn hMean.1 0 hs
    simp only [iteratedDeriv_zero] at h
    exact h.contDiffAt.of_le (by simp)
  have hV_cd : ContDiffAt ℝ 2 (vortexMeanStream ν c s) e := by
    unfold vortexMeanStream
    exact (contDiff_const.mul (contDiff_heatKernel1 _)).contDiffAt.of_le (by simp)
  have hP_cd : ContDiffAt ℝ 2
      (fun y => ∑ j ∈ Finset.range (N + 1),
        meanSourceCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * s)) y) e :=
    (ContDiff.sum fun j _ => contDiff_const.mul
      (contDiff_iteratedDeriv _ (contDiff_heatKernel1 (ν * s)) (2 * j))).contDiffAt.of_le
      (by simp)
  have hSV_cd : ContDiffAt ℝ 2 (meanStream tr s - vortexMeanStream ν c s) e :=
    hS_cd.sub hV_cd
  rw [hrem_s, iteratedDeriv_sub hSV_cd hP_cd, iteratedDeriv_sub hS_cd hV_cd]
  ring

private theorem slice_meanSourceRemainder_succ {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr)
    (hD : ∀ r : ℝ, 0 < r → ∀ e : ℝ,
      meanStream tr r e = meanDatumDuhamel tr r e + meanSourceDuhamel tr r e)
    (N b ℓ : ℕ) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    iteratedDeriv b (fun e => iteratedDeriv (ℓ + 1) (fun r => meanSourceRemainder tr N r e) s) η =
      ν * iteratedDeriv (b + 2)
          (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η +
        iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) η := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hSrcSm := contDiffOn_meanSourceRemainder hν hc1 tr htr hD N
  have hStrSm := PartI_T23.contDiffOn_meanStress hc0 tr
  have hSrc2Sm : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => iteratedDeriv 2 (meanSourceRemainder tr N x.1) x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartIIa.etaDerivIter_contDiffOn (meanSourceRemainder tr N) hSrcSm 2
  have he_eq : ∀ e : ℝ,
      iteratedDeriv (ℓ + 1) (fun r => meanSourceRemainder tr N r e) s =
        ν * iteratedDeriv 2
            (fun e' => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e') s) e +
          iteratedDeriv ℓ (fun r => meanStress tr r e) s := by
    intro e
    have hev : deriv (fun r => meanSourceRemainder tr N r e) =ᶠ[𝓝 s]
        ((fun r => ν * iteratedDeriv 2 (meanSourceRemainder tr N r) e) +
          (fun r => meanStress tr r e)) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
        using deriv_age_meanSourceRemainder hν hc1 tr htr hD N hr e
    have h1_cd : ContDiffAt ℝ ℓ
        (fun r => ν * iteratedDeriv 2 (meanSourceRemainder tr N r) e) s :=
      contDiffAt_const.mul
        (contDiffAt_age_slice_of_contDiffOn
          (G := fun r e' => iteratedDeriv 2 (meanSourceRemainder tr N r) e') hSrc2Sm ℓ hs e)
    have h2_cd : ContDiffAt ℝ ℓ (fun r => meanStress tr r e) s :=
      contDiffAt_age_slice_of_contDiffOn hStrSm ℓ hs e
    rw [iteratedDeriv_succ', hev.iteratedDeriv_eq ℓ, iteratedDeriv_add h1_cd h2_cd,
      iteratedDeriv_const_mul_field,
      iteratedDeriv_age_iteratedDeriv_eta_comm ℓ 2 hSrcSm hs e]
  have hfun : (fun e => iteratedDeriv (ℓ + 1) (fun r => meanSourceRemainder tr N r e) s) =
      ((fun e => ν * iteratedDeriv 2
          (fun e' => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e') s) e) +
        (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s)) :=
    funext he_eq
  have hA_sm : ContDiff ℝ ∞
      (fun e' => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e') s) :=
    contDiff_eta_slice_of_contDiffOn hSrcSm ℓ hs
  have hB_sm : ContDiff ℝ ∞ (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) :=
    contDiff_eta_slice_of_contDiffOn hStrSm ℓ hs
  have hA2_cd : ContDiffAt ℝ b
      (fun e => ν * iteratedDeriv 2
        (fun e' => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e') s) e) η :=
    (contDiff_const.mul (contDiff_iteratedDeriv _ hA_sm 2)).contDiffAt.of_le
      (by exact_mod_cast le_top)
  have hB_cd : ContDiffAt ℝ b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) η :=
    hB_sm.contDiffAt.of_le (by exact_mod_cast le_top)
  rw [hfun, iteratedDeriv_add hA2_cd hB_cd, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_iteratedDeriv]

end SourceRemainderBound

/-- **Main theorem (`PartI:T23/2/3`)**: proves `TrainMeanSourceRemainderBound`. -/
theorem trainMeanSourceRemainderBound_proof
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : TrainFluctuationDecay)
    (hMP : OverlapMeanPrimitive) :
    TrainMeanSourceRemainderBound := by
  intro ρ hρ N m b ℓ
  obtain ⟨ν_duh, hν_duh, hDuh⟩ := trainMeanStreamDuhamel_proof hTails hFD hMP ρ hρ
  induction ℓ generalizing b with
  | zero =>
    obtain ⟨C₀, M₀, ν₀, hC₀, hν₀, hB₀⟩ :=
      SourceRemainderBound.trainMeanSourceRemainderBound_zero hFD ρ hρ N m b
    refine ⟨C₀, M₀, ν₀, hC₀, hν₀, ?_⟩
    intro ν hν hν_le tr htr c s hs η
    simpa [iteratedDeriv_zero, Nat.cast_zero, sub_zero] using hB₀ ν hν hν_le tr htr s hs η
  | succ ℓ ih =>
    obtain ⟨C₁, M₁, ν₁, hC₁, hν₁, hB₁⟩ := ih (b + 2)
    obtain ⟨C_g, M_g, κ_g, ν_g, hC_g, hκ_g, hν_g, hDecay_g⟩ :=
      PartI_T23.meanStress_weighted_jet_decay_of_fluctDecay hFD ρ hρ m b ℓ
    set α : ℝ := ((m : ℝ) - b - 2 * N - 3) / 2 - ((ℓ + 1 : ℕ) : ℝ)
    have hα_ge : -((b + 2 * N + 3 + 2 * (ℓ + 1) : ℕ) : ℝ) ≤ α := by
      dsimp [α]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
      push_cast
      linarith
    obtain ⟨C_abs, M_abs, hC_abs, hAbs⟩ :=
      SourceRemainderBound.rpow_mul_exp_le_polyP_mul_rpow
        hκ_g 0 (b + 2 * N + 3 + 2 * (ℓ + 1)) hα_ge
    set C₂ : ℝ := C_g * C_abs
    set M₂ : ℕ := M_g + M_abs
    set M_tot : ℕ := max M₁ M₂
    set ν_tot : ℝ := min (min 1 ν_duh) (min ν₁ ν_g)
    refine ⟨C₁ + C₂, M_tot, ν_tot, by dsimp [C₂]; positivity,
      lt_min (lt_min one_pos hν_duh) (lt_min hν₁ hν_g), ?_⟩
    intro ν hν hν_le tr htr c s hs η
    have hν1 : ν ≤ 1 := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hν_duh_le : ν ≤ ν_duh := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hν₁_le : ν ≤ ν₁ := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hν_g_le : ν ≤ ν_g := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hc1 : 1 ≤ c := by
      dsimp [c, trainPeriod]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
    have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
    have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      linarith
    have hsα_nn : 0 ≤ s ^ α := Real.rpow_nonneg hs0.le _
    rw [SourceRemainderBound.slice_meanSourceRemainder_succ
      hν hc1 tr htr (hDuh ν hν hν_duh_le tr htr) N b ℓ hs0 η]
    have hα_shift : ((m : ℝ) - ((b + 2 : ℕ) : ℝ) - 2 * N - 3) / 2 - (ℓ : ℝ) = α := by
      dsimp [α]; push_cast; ring
    have hP₁ : polyP C₁ M₁ ν c ≤ polyP C₁ M_tot ν c := by
      unfold polyP
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (le_max_left _ _)) hC₁.le
    have hP₂ : polyP C₂ M₂ ν c ≤ polyP C₂ M_tot ν c := by
      unfold polyP
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hX1 (le_max_right _ _)) (by dsimp [C₂]; positivity)
    have hterm1 : |η| ^ m *
        |ν * iteratedDeriv (b + 2)
          (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η| ≤
        polyP C₁ M_tot ν c * s ^ α := by
      rw [abs_mul, abs_of_pos hν]
      have h1 := hB₁ ν hν hν₁_le tr htr s hs η
      rw [hα_shift] at h1
      calc |η| ^ m * (ν * |iteratedDeriv (b + 2)
              (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η|)
          ≤ |η| ^ m * (1 * |iteratedDeriv (b + 2)
              (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hν1 (abs_nonneg _)) (by positivity)
        _ = |η| ^ m * |iteratedDeriv (b + 2)
              (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η| := by ring
        _ ≤ polyP C₁ M₁ ν c * s ^ α := h1
        _ ≤ polyP C₁ M_tot ν c * s ^ α := mul_le_mul_of_nonneg_right hP₁ hsα_nn
    have hη_jap : |η| ^ m ≤ (1 + η ^ 2) ^ m :=
      SourceRemainderBound.abs_pow_le_one_add_sq_pow (by omega) η
    have hterm2 : |η| ^ m *
        |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) η| ≤
        polyP C₂ M_tot ν c * s ^ α := by
      have hg := hDecay_g ν hν hν_g_le tr htr s hs0 η
      have habs := hAbs hν hc0 hs
      rw [pow_zero, one_mul] at habs
      calc |η| ^ m * |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) η|
          ≤ (1 + η ^ 2) ^ m *
              |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) η| :=
            mul_le_mul_of_nonneg_right hη_jap (abs_nonneg _)
        _ ≤ polyP C_g M_g ν c * Real.exp (-(κ_g * ν * s / c ^ 2)) := hg
        _ ≤ polyP C_g M_g ν c * (polyP C_abs M_abs ν c * s ^ α) :=
            mul_le_mul_of_nonneg_left habs (by unfold polyP; positivity)
        _ = polyP C₂ M₂ ν c * s ^ α := by
            dsimp [C₂, M₂]; unfold polyP; rw [pow_add]; ring
        _ ≤ polyP C₂ M_tot ν c * s ^ α := mul_le_mul_of_nonneg_right hP₂ hsα_nn
    calc |η| ^ m *
          |ν * iteratedDeriv (b + 2)
              (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η +
            iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) η|
        ≤ |η| ^ m *
            (|ν * iteratedDeriv (b + 2)
                (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η| +
              |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) η|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ = |η| ^ m *
            |ν * iteratedDeriv (b + 2)
              (fun e => iteratedDeriv ℓ (fun r => meanSourceRemainder tr N r e) s) η| +
          |η| ^ m *
            |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStress tr r e) s) η| := by
          ring
      _ ≤ polyP C₁ M_tot ν c * s ^ α + polyP C₂ M_tot ν c * s ^ α :=
          add_le_add hterm1 hterm2
      _ = polyP (C₁ + C₂) M_tot ν c * s ^ α := by
          unfold polyP; ring

end UnforcedLeray.Short.PartI
