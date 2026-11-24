import UnforcedLeray.Short.PartI.Sub.PartI_T23_2
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# `PartI:T23/2/2`: Weighted Pointwise Taylor Remainder Bound for `meanDatumRemainder`

Proves `TrainMeanDatumRemainderBound` (`Sub/PartI_T23_2.lean`), the initial-datum Taylor remainder
bound for the 1D heat Duhamel expansion of `meanStream`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set ContDiff
open scoped Topology ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (width)

namespace DatumRemainderBound

/-! ### 1. General 1D derivative-sequence helper on open sets -/

/-- Given a sequence of functions `g : ℕ → ℝ → ℝ` on an open set `U ⊆ ℝ` satisfying
`HasDerivAt (g k) (g (k + 1) y) y` for every `k : ℕ` and `y ∈ U`, the `k`-th iterated derivative
of `g 0` on `U` is `g k` and every `g k` is `C^∞` on `U`. -/
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

/-- Linearity of `iteratedDeriv` over a `Finset.sum` for functions that are `C^∞` at `x`. -/
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

/-! ### 2. 1D heat equation for spatial derivatives of `heatKernel1` -/

/-- `heatKernel1 a` is `C^∞` on `ℝ` for every `a : ℝ`. -/
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

/-- The `k`-th spatial derivative of the unit-width 1D heat kernel `heatKernel1 1`. -/
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

/-- Three-term recurrence for the derivatives of `heatKernel1 1`:
`G1_deriv (k + 2) x = -((k + 1) / 2) * G1_deriv k x - (x / 2) * G1_deriv (k + 1) x`. -/
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

/-- Scaling of the `k`-th spatial derivative of `heatKernel1 a` for `a > 0`. -/
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

/-- Width derivative of the `k`-th spatial derivative of `heatKernel1`:
`∂_a (∂_y^k G_a(y)) = ∂_y^{k+2} G_a(y)` for `a > 0`. -/
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

/-- Iterated `r`-derivative and smoothness of `r ↦ iteratedDeriv m (heatKernel1 (τ + ν * r)) e`
on `Ioi 0` for `ν > 0` and `τ ≥ 0`. -/
private theorem iteratedDeriv_time_heatKernel1 {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 ≤ τ)
    (m ℓ : ℕ) {s : ℝ} (hs : 0 < s) (e : ℝ) :
    iteratedDeriv ℓ (fun r => iteratedDeriv m (heatKernel1 (τ + ν * r)) e) s =
      ν ^ ℓ * iteratedDeriv (m + 2 * ℓ) (heatKernel1 (τ + ν * s)) e ∧
    ContDiffAt ℝ ∞ (fun r => iteratedDeriv m (heatKernel1 (τ + ν * r)) e) s := by
  let g : ℕ → ℝ → ℝ := fun k r =>
    ν ^ k * iteratedDeriv (m + 2 * k) (heatKernel1 (τ + ν * r)) e
  have hd : ∀ k : ℕ, ∀ r ∈ Ioi (0 : ℝ), HasDerivAt (g k) (g (k + 1) r) r := by
    intro k r hr
    have hr0 : 0 < r := hr
    have ha : 0 < τ + ν * r := by positivity
    have hlin : HasDerivAt (fun r' : ℝ => τ + ν * r') ν r := by
      simpa using ((hasDerivAt_id' r).const_mul ν).const_add τ
    have hcomp := (hasDerivAt_iteratedDeriv_heatKernel1_width ha (m + 2 * k) e).comp r hlin
    have hmul := hcomp.const_mul (ν ^ k)
    refine hmul.congr_deriv ?_
    dsimp [g]
    rw [show m + 2 * (k + 1) = m + 2 * k + 2 by omega, pow_succ]
    ring
  obtain ⟨hiter, hcd⟩ := iteratedDeriv_eq_of_hasDerivAt_seq isOpen_Ioi g hd
  have h0 : g 0 = fun r => iteratedDeriv m (heatKernel1 (τ + ν * r)) e := by
    funext r
    simp [g]
  rw [← h0]
  exact ⟨hiter ℓ s hs, (hcd 0).contDiffAt (isOpen_Ioi.mem_nhds hs)⟩

/-- Mixed `(b, ℓ)` slice derivative of `(r, e) ↦ iteratedDeriv m (heatKernel1 (τ + ν * r)) e`
for `ν > 0`, `τ ≥ 0`, `s > 0`. -/
private theorem mixed_slice_heatKernel1 {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 ≤ τ)
    (m b ℓ : ℕ) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    iteratedDeriv b (fun e => iteratedDeriv ℓ
        (fun r => iteratedDeriv m (heatKernel1 (τ + ν * r)) e) s) η =
      ν ^ ℓ * iteratedDeriv (b + (m + 2 * ℓ)) (heatKernel1 (τ + ν * s)) η := by
  have hfun : (fun e => iteratedDeriv ℓ
        (fun r => iteratedDeriv m (heatKernel1 (τ + ν * r)) e) s) =
      fun e => ν ^ ℓ * iteratedDeriv (m + 2 * ℓ) (heatKernel1 (τ + ν * s)) e :=
    funext fun e => (iteratedDeriv_time_heatKernel1 hν hτ m ℓ hs e).1
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_comp_iteratedDeriv]

/-! ### 3. Even Gaussian moments of `heatKernel1 1` and `meanDatumCoeff` -/

private theorem integrable_pow_mul_heatKernel1 (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m * heatKernel1 1 x) volume := by
  have hb : (0 : ℝ) < 1 / 4 := by norm_num
  have hm_gt : (-1 : ℝ) < (m : ℝ) := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h0 := integrable_rpow_mul_exp_neg_mul_sq hb hm_gt
  have h1 : Integrable (fun x : ℝ => x ^ m * Real.exp (-(1 / 4) * x ^ 2)) volume := by
    refine h0.congr (ae_of_all _ fun x => ?_)
    dsimp only
    rw [Real.rpow_natCast]
  have h2 := h1.const_mul (Real.sqrt (4 * Real.pi * 1))⁻¹
  refine h2.congr (ae_of_all _ fun x => ?_)
  dsimp only [heatKernel1]
  rw [show -(x ^ 2) / (4 * 1) = -(1 / 4) * x ^ 2 by ring]
  ring

private theorem tendsto_pow_mul_heatKernel1_cocompact (m : ℕ) :
    Tendsto (fun x : ℝ => -2 * x ^ m * heatKernel1 1 x) (cocompact ℝ) (𝓝 0) := by
  have ha : (0 : ℝ) < 1 / 4 := by norm_num
  have ht := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha (m : ℝ)).const_mul
    (2 * (Real.sqrt (4 * Real.pi * 1))⁻¹)
  rw [mul_zero] at ht
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (g := fun x => 2 * (Real.sqrt (4 * Real.pi * 1))⁻¹ *
      (|x| ^ (m : ℝ) * Real.exp (-(1 / 4) * x ^ 2)))
    (fun _ => norm_nonneg _) (fun x => ?_) ht
  rw [Real.norm_eq_abs]
  unfold heatKernel1
  have hpos : 0 ≤ (Real.sqrt (4 * Real.pi * 1))⁻¹ := by positivity
  have hexp : Real.exp (-(x ^ 2) / (4 * 1)) = Real.exp (-(1 / 4) * x ^ 2) := by
    congr 1; ring
  rw [hexp, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos two_pos, abs_pow, Real.rpow_natCast,
    abs_of_nonneg hpos, abs_of_pos (Real.exp_pos _)]
  ring_nf
  exact le_rfl

/-- Even moments of `heatKernel1 1`:
`(∫ x, x^{2j} G_1(x) dx) / (2j)! = (j!)⁻¹`. -/
private theorem integral_even_pow_mul_heatKernel1 (j : ℕ) :
    (∫ x : ℝ, x ^ (2 * j) * heatKernel1 1 x) / ((2 * j).factorial : ℝ) =
      (j.factorial : ℝ)⁻¹ := by
  induction j with
  | zero =>
    simp [PartI_T23.integral_heatKernel1_eq_one one_pos]
  | succ j ih =>
    set h : ℝ → ℝ := fun x => -2 * x ^ (2 * j + 1) * heatKernel1 1 x
    set h' : ℝ → ℝ := fun x =>
      x ^ (2 * j + 2) * heatKernel1 1 x -
        2 * (((2 * j : ℕ) : ℝ) + 1) * (x ^ (2 * j) * heatKernel1 1 x)
    have hderiv : ∀ x : ℝ, HasDerivAt h (h' x) x := by
      intro x
      have hp : HasDerivAt (fun z : ℝ => -2 * z ^ (2 * j + 1))
          (-2 * ((((2 * j : ℕ) : ℝ) + 1) * x ^ (2 * j))) x := by
        simpa using ((hasDerivAt_id' x).pow (2 * j + 1)).const_mul (-2)
      refine (hp.mul (hasDerivAt_heatKernel1_one x)).congr_deriv ?_
      dsimp [h']
      ring
    have h_top : Tendsto h atTop (𝓝 0) :=
      (tendsto_pow_mul_heatKernel1_cocompact (2 * j + 1)).mono_left atTop_le_cocompact
    have h_bot : Tendsto h atBot (𝓝 0) :=
      (tendsto_pow_mul_heatKernel1_cocompact (2 * j + 1)).mono_left atBot_le_cocompact
    have hint_k2 := integrable_pow_mul_heatKernel1 (2 * j + 2)
    have hint_k := integrable_pow_mul_heatKernel1 (2 * j)
    have hint_h' : Integrable h' volume :=
      hint_k2.sub (hint_k.const_mul (2 * (((2 * j : ℕ) : ℝ) + 1)))
    have hzero := integral_of_hasDerivAt_of_tendsto hderiv hint_h' h_bot h_top
    rw [sub_self] at hzero
    have hrec : (∫ x : ℝ, x ^ (2 * j + 2) * heatKernel1 1 x) =
        2 * (((2 * j : ℕ) : ℝ) + 1) * ∫ x : ℝ, x ^ (2 * j) * heatKernel1 1 x := by
      have hsub : ∫ x : ℝ, h' x =
          (∫ x : ℝ, x ^ (2 * j + 2) * heatKernel1 1 x) -
            2 * (((2 * j : ℕ) : ℝ) + 1) * ∫ x : ℝ, x ^ (2 * j) * heatKernel1 1 x := by
        dsimp [h']
        rw [integral_sub hint_k2 (hint_k.const_mul _), integral_const_mul]
      linarith
    have hk2 : 2 * (j + 1) = 2 * j + 2 := by omega
    have hfact_nat : (2 * (j + 1)).factorial =
        (2 * j + 2) * (2 * j + 1) * (2 * j).factorial := by
      rw [hk2, Nat.factorial_succ (2 * j + 1), Nat.factorial_succ (2 * j)]
      ring
    have hfact : ((2 * (j + 1)).factorial : ℝ) =
        2 * ((j : ℝ) + 1) * (((2 * j : ℕ) : ℝ) + 1) * ((2 * j).factorial : ℝ) := by
      rw [hfact_nat]
      push_cast
      ring
    have hj1_ne : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hk1_ne : (((2 * j : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    have hkf_ne : ((2 * j).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (2 * j))
    calc (∫ x : ℝ, x ^ (2 * (j + 1)) * heatKernel1 1 x) / ((2 * (j + 1)).factorial : ℝ)
        = (2 * (((2 * j : ℕ) : ℝ) + 1) * ∫ x : ℝ, x ^ (2 * j) * heatKernel1 1 x) /
            (2 * ((j : ℝ) + 1) * (((2 * j : ℕ) : ℝ) + 1) * ((2 * j).factorial : ℝ)) := by
          rw [hfact, hk2, hrec]
      _ = ((∫ x : ℝ, x ^ (2 * j) * heatKernel1 1 x) / ((2 * j).factorial : ℝ)) /
            ((j : ℝ) + 1) := by
          field_simp
      _ = (j.factorial : ℝ)⁻¹ / ((j : ℝ) + 1) := by rw [ih]
      _ = ((j + 1).factorial : ℝ)⁻¹ := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          field_simp

/-- Explicit formula for `meanDatumCoeff tr j` for `c ≥ 1`:
`meanDatumCoeff tr j = -(8π c⁻¹) * (j!)⁻¹`. -/
private theorem meanDatumCoeff_eq {ν c : ℝ} (hc1 : 1 ≤ c) (tr : B0140.TrainSol ν c) (j : ℕ) :
    meanDatumCoeff tr j = -(8 * Real.pi * c⁻¹) * (j.factorial : ℝ)⁻¹ := by
  unfold meanDatumCoeff
  have hfun : (fun η : ℝ => η ^ (2 * j) * meanStream tr 0 η) =
      fun η : ℝ => -(8 * Real.pi * c⁻¹) * (η ^ (2 * j) * heatKernel1 1 η) := by
    funext η
    rw [meanStream_zero_eq_vortexMeanStream hc1 tr η]
    unfold vortexMeanStream width
    simp only [mul_zero, add_zero]
    ring
  rw [hfun, integral_const_mul, mul_div_assoc, integral_even_pow_mul_heatKernel1 j]

/-! ### 4. Closed form of the `(b, ℓ)` slice derivative of `meanDatumRemainder` -/

/-- For `ν > 0`, `c ≥ 1`, `s > 0`, and `η ∈ ℝ`, the `(b, ℓ)` mixed slice derivative of
`meanDatumRemainder tr N` at `(s, η)` is `-(8π c⁻¹) * ν^ℓ` times the order-`N` Taylor remainder
of `τ ↦ ∂_η^{b + 2ℓ} G_{ν s + τ}(η)` from `τ = 0` to `τ = 1`. -/
private theorem slice_meanDatumRemainder_eq {ν c : ℝ} (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (N b ℓ : ℕ) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanDatumRemainder tr N r e) s) η =
      -(8 * Real.pi * c⁻¹) * ν ^ ℓ *
        (iteratedDeriv (b + 2 * ℓ) (heatKernel1 (ν * s + 1)) η -
          ∑ j ∈ Finset.range (N + 1),
            (j.factorial : ℝ)⁻¹ *
              iteratedDeriv (b + 2 * ℓ + 2 * j) (heatKernel1 (ν * s)) η) := by
  have hr_eq : ∀ e : ℝ,
      iteratedDeriv ℓ (fun r => meanDatumRemainder tr N r e) s =
        -(8 * Real.pi * c⁻¹) * (ν ^ ℓ * iteratedDeriv (2 * ℓ) (heatKernel1 (1 + ν * s)) e) -
          ∑ j ∈ Finset.range (N + 1),
            meanDatumCoeff tr j *
              (ν ^ ℓ * iteratedDeriv (2 * j + 2 * ℓ) (heatKernel1 (ν * s)) e) := by
    intro e
    have hev : (fun r => meanDatumRemainder tr N r e) =ᶠ[𝓝 s]
        fun r => -(8 * Real.pi * c⁻¹) * heatKernel1 (1 + ν * r) e -
          ∑ j ∈ Finset.range (N + 1),
            meanDatumCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (0 + ν * r)) e := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      unfold meanDatumRemainder
      rw [PartI_T23.meanDatumDuhamel_eq_vortexMeanStream hν hc1 tr hr e]
      unfold vortexMeanStream width
      simp [zero_add]
    rw [hev.iteratedDeriv_eq]
    have h1 := iteratedDeriv_time_heatKernel1 hν zero_le_one 0 ℓ hs e
    have h2 : ∀ j : ℕ,
        iteratedDeriv ℓ (fun r => iteratedDeriv (2 * j) (heatKernel1 (0 + ν * r)) e) s =
          ν ^ ℓ * iteratedDeriv (2 * j + 2 * ℓ) (heatKernel1 (0 + ν * s)) e ∧
        ContDiffAt ℝ ∞ (fun r => iteratedDeriv (2 * j) (heatKernel1 (0 + ν * r)) e) s :=
      fun j => iteratedDeriv_time_heatKernel1 hν le_rfl (2 * j) ℓ hs e
    have hterm1_cd : ContDiffAt ℝ ∞ (fun r => -(8 * Real.pi * c⁻¹) * heatKernel1 (1 + ν * r) e) s :=
      contDiffAt_const.mul h1.2
    have hterm2_cd : ContDiffAt ℝ ∞
        (fun r => ∑ j ∈ Finset.range (N + 1),
          meanDatumCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (0 + ν * r)) e) s :=
      ContDiffAt.sum fun j _ => contDiffAt_const.mul (h2 j).2
    rw [show (fun r => -(8 * Real.pi * c⁻¹) * heatKernel1 (1 + ν * r) e -
          ∑ j ∈ Finset.range (N + 1),
            meanDatumCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (0 + ν * r)) e) =
        (fun r => -(8 * Real.pi * c⁻¹) * heatKernel1 (1 + ν * r) e) -
          (fun r => ∑ j ∈ Finset.range (N + 1),
            meanDatumCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (0 + ν * r)) e) from rfl,
      iteratedDeriv_sub (hterm1_cd.of_le (by exact_mod_cast le_top))
        (hterm2_cd.of_le (by exact_mod_cast le_top))]
    have ht1 : iteratedDeriv ℓ (fun r => -(8 * Real.pi * c⁻¹) * heatKernel1 (1 + ν * r) e) s =
        -(8 * Real.pi * c⁻¹) * (ν ^ ℓ * iteratedDeriv (2 * ℓ) (heatKernel1 (1 + ν * s)) e) := by
      have h0 : (fun r => -(8 * Real.pi * c⁻¹) * heatKernel1 (1 + ν * r) e) =
          fun r => -(8 * Real.pi * c⁻¹) * iteratedDeriv 0 (heatKernel1 (1 + ν * r)) e := rfl
      rw [h0, iteratedDeriv_const_mul_field, h1.1, zero_add]
    have ht2 : iteratedDeriv ℓ
        (fun r => ∑ j ∈ Finset.range (N + 1),
          meanDatumCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (0 + ν * r)) e) s =
        ∑ j ∈ Finset.range (N + 1),
          meanDatumCoeff tr j *
            (ν ^ ℓ * iteratedDeriv (2 * j + 2 * ℓ) (heatKernel1 (ν * s)) e) := by
      rw [iteratedDeriv_finset_sum (Finset.range (N + 1)) _ ℓ s
        (fun j _ => contDiffAt_const.mul (h2 j).2)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [iteratedDeriv_const_mul_field, (h2 j).1, zero_add]
    rw [ht1, ht2]
  have hfun : (fun e => iteratedDeriv ℓ (fun r => meanDatumRemainder tr N r e) s) =
      fun e => -(8 * Real.pi * c⁻¹) * (ν ^ ℓ * iteratedDeriv (2 * ℓ) (heatKernel1 (1 + ν * s)) e) -
        ∑ j ∈ Finset.range (N + 1),
          meanDatumCoeff tr j *
            (ν ^ ℓ * iteratedDeriv (2 * j + 2 * ℓ) (heatKernel1 (ν * s)) e) :=
    funext hr_eq
  rw [hfun]
  have he1_cd : ContDiffAt ℝ ∞
      (fun e => -(8 * Real.pi * c⁻¹) * (ν ^ ℓ * iteratedDeriv (2 * ℓ) (heatKernel1 (1 + ν * s)) e)) η :=
    (contDiff_const.mul (contDiff_const.mul
      (contDiff_iteratedDeriv _ (contDiff_heatKernel1 (1 + ν * s)) (2 * ℓ)))).contDiffAt
  have he2_cd : ContDiffAt ℝ ∞
      (fun e => ∑ j ∈ Finset.range (N + 1),
        meanDatumCoeff tr j *
          (ν ^ ℓ * iteratedDeriv (2 * j + 2 * ℓ) (heatKernel1 (ν * s)) e)) η :=
    ContDiffAt.sum fun j _ =>
      (contDiff_const.mul (contDiff_const.mul
        (contDiff_iteratedDeriv _ (contDiff_heatKernel1 (ν * s)) (2 * j + 2 * ℓ)))).contDiffAt
  rw [show (fun e => -(8 * Real.pi * c⁻¹) * (ν ^ ℓ * iteratedDeriv (2 * ℓ) (heatKernel1 (1 + ν * s)) e) -
        ∑ j ∈ Finset.range (N + 1),
          meanDatumCoeff tr j *
            (ν ^ ℓ * iteratedDeriv (2 * j + 2 * ℓ) (heatKernel1 (ν * s)) e)) =
      (fun e => -(8 * Real.pi * c⁻¹) * (ν ^ ℓ * iteratedDeriv (2 * ℓ) (heatKernel1 (1 + ν * s)) e)) -
        (fun e => ∑ j ∈ Finset.range (N + 1),
          meanDatumCoeff tr j *
            (ν ^ ℓ * iteratedDeriv (2 * j + 2 * ℓ) (heatKernel1 (ν * s)) e)) from rfl,
    iteratedDeriv_sub (he1_cd.of_le (by exact_mod_cast le_top))
      (he2_cd.of_le (by exact_mod_cast le_top))]
  have hb1 : iteratedDeriv b
      (fun e => -(8 * Real.pi * c⁻¹) * (ν ^ ℓ * iteratedDeriv (2 * ℓ) (heatKernel1 (1 + ν * s)) e)) η =
      -(8 * Real.pi * c⁻¹) * ν ^ ℓ *
        iteratedDeriv (b + 2 * ℓ) (heatKernel1 (ν * s + 1)) η := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
      iteratedDeriv_comp_iteratedDeriv, add_comm 1 (ν * s)]
    ring
  have hb2 : iteratedDeriv b
      (fun e => ∑ j ∈ Finset.range (N + 1),
        meanDatumCoeff tr j *
          (ν ^ ℓ * iteratedDeriv (2 * j + 2 * ℓ) (heatKernel1 (ν * s)) e)) η =
      ∑ j ∈ Finset.range (N + 1),
        -(8 * Real.pi * c⁻¹) * ν ^ ℓ *
          ((j.factorial : ℝ)⁻¹ *
            iteratedDeriv (b + 2 * ℓ + 2 * j) (heatKernel1 (ν * s)) η) := by
    rw [iteratedDeriv_finset_sum (Finset.range (N + 1)) _ b η fun j _ =>
      (contDiff_const.mul (contDiff_const.mul
        (contDiff_iteratedDeriv _ (contDiff_heatKernel1 (ν * s)) (2 * j + 2 * ℓ)))).contDiffAt]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
      iteratedDeriv_comp_iteratedDeriv, meanDatumCoeff_eq hc1 tr j,
      show b + (2 * j + 2 * ℓ) = b + 2 * ℓ + 2 * j by omega]
    ring
  rw [hb1, hb2, ← Finset.mul_sum]
  ring

/-- Shifted-time power comparison: for `1 ≤ s`, `s ≤ s' ≤ (1 + c + ν⁻¹) * s`, `0 ≤ c`, `0 < ν`,
and `α ≤ m`, `(s') ^ α ≤ (1 + c + ν⁻¹) ^ m * s ^ α`. -/
private theorem rpow_shift_le {ν c s s' α : ℝ} {m : ℕ}
    (hν : 0 < ν) (hc : 0 ≤ c) (hs : 1 ≤ s) (hss' : s ≤ s')
    (hs'_le : s' ≤ (1 + c + ν⁻¹) * s) (hαm : α ≤ (m : ℝ)) :
    (s') ^ α ≤ (1 + c + ν⁻¹) ^ m * s ^ α := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hs'0 : 0 < s' := lt_of_lt_of_le hs0 hss'
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hXm1 : 1 ≤ (1 + c + ν⁻¹) ^ m := one_le_pow₀ hX1
  rcases le_or_gt α 0 with hα0 | hα0
  · have h1 : (s') ^ α ≤ s ^ α := Real.rpow_le_rpow_of_nonpos hs0 hss' hα0
    exact h1.trans (le_mul_of_one_le_left (Real.rpow_nonneg hs0.le _) hXm1)
  · calc (s') ^ α
        ≤ ((1 + c + ν⁻¹) * s) ^ α := Real.rpow_le_rpow hs'0.le hs'_le hα0.le
      _ = (1 + c + ν⁻¹) ^ α * s ^ α := Real.mul_rpow (by positivity) hs0.le
      _ ≤ (1 + c + ν⁻¹) ^ (m : ℝ) * s ^ α :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hX1 hαm) (Real.rpow_nonneg hs0.le _)
      _ = (1 + c + ν⁻¹) ^ m * s ^ α := by rw [Real.rpow_natCast]

end DatumRemainderBound

/-! ### 5. Main theorem: `trainMeanDatumRemainderBound_proof` -/

theorem trainMeanDatumRemainderBound_proof
    (_hTails : TrainStreamVelocityPressureTails) :
    TrainMeanDatumRemainderBound := by
  intro ρ hρ N m b ℓ
  set B : ℕ := b + 2 * ℓ + 2 * (N + 1)
  obtain ⟨D, hD_pos, hD⟩ := PartI_T23.heatKernel1_weighted_jet_bound m B 0
  refine ⟨8 * Real.pi * D, B + 1 + m, 1, by positivity, one_pos, ?_⟩
  set c_fn := fun ν : ℝ => trainPeriod ρ ν
  intro ν hν hν1 tr _htr c s hs η
  have hc1 : 1 ≤ c := by
    dsimp [c, trainPeriod]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  set α : ℝ := ((m : ℝ) - b - 2 * N - 3) / 2 - ℓ
  have hα_eq : ((m : ℝ) - (B : ℝ) - 1) / 2 - (0 : ℕ) = α := by
    dsimp [B, α]
    push_cast
    ring
  have hα_le_m : α ≤ (m : ℝ) := by
    dsimp [α]
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  -- Define `φ τ := iteratedDeriv (b + 2 * ℓ) (heatKernel1 (ν * s + τ)) η`
  set g : ℕ → ℝ → ℝ := fun k τ =>
    iteratedDeriv (b + 2 * ℓ + 2 * k) (heatKernel1 (ν * s + τ)) η
  have hU_open : IsOpen (Ioi (-(ν * s))) := isOpen_Ioi
  have hd_g : ∀ k : ℕ, ∀ τ ∈ Ioi (-(ν * s)), HasDerivAt (g k) (g (k + 1) τ) τ := by
    intro k τ hτ
    have ha : 0 < ν * s + τ := by linarith [mem_Ioi.1 hτ]
    have hlin : HasDerivAt (fun τ' : ℝ => ν * s + τ') 1 τ := by
      simpa using (hasDerivAt_id τ).const_add (ν * s)
    have hcomp := (DatumRemainderBound.hasDerivAt_iteratedDeriv_heatKernel1_width
      ha (b + 2 * ℓ + 2 * k) η).comp τ hlin
    refine hcomp.congr_deriv ?_
    dsimp [g]
    rw [mul_one, show b + 2 * ℓ + 2 * (k + 1) = b + 2 * ℓ + 2 * k + 2 by omega]
  obtain ⟨hiter_g, hcd_g⟩ := DatumRemainderBound.iteratedDeriv_eq_of_hasDerivAt_seq
    hU_open g hd_g
  set φ : ℝ → ℝ := g 0
  have hIcc_sub : Icc (0 : ℝ) 1 ⊆ Ioi (-(ν * s)) := by
    intro τ hτ
    rw [mem_Ioi]
    have : 0 < ν * s := mul_pos hν hs0
    linarith [hτ.1]
  have hφ_cd_on : ContDiffOn ℝ (N + 1) φ (Icc 0 1) :=
    ((hcd_g 0).mono hIcc_sub).of_le (by exact_mod_cast le_top)
  have hφ_cd_at : ∀ τ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ φ τ :=
    fun τ hτ => (hcd_g 0).contDiffAt (hU_open.mem_nhds (hIcc_sub hτ))
  -- Pointwise bound on `|iteratedDeriv (N + 1) φ τ|` for `τ ∈ Icc 0 1`
  set M_bound : ℝ := ((1 + |η|) ^ m)⁻¹ * (polyP D (B + 1 + m) ν c * s ^ α)
  have hφ_N1_bd : ∀ τ ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (N + 1) φ (Icc 0 1) τ‖ ≤ M_bound := by
    intro τ hτ
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hφ_cd_at τ hτ).of_le (by exact_mod_cast le_top)) hτ,
      hiter_g (N + 1) τ (hIcc_sub hτ), Real.norm_eq_abs]
    dsimp [g]
    set s' : ℝ := s + τ / ν
    have hs_le_s' : s ≤ s' := by
      dsimp [s']
      have : 0 ≤ τ / ν := div_nonneg hτ.1 hν.le
      linarith
    have hs'1 : 1 ≤ s' := hs.trans hs_le_s'
    have hs'_le : s' ≤ (1 + c + ν⁻¹) * s := by
      dsimp [s']
      have h1 : τ / ν ≤ 1 / ν := div_le_div_of_nonneg_right hτ.2 hν.le
      have h2 : 1 / ν ≤ s * ν⁻¹ := by
        rw [one_div]
        exact le_mul_of_one_le_left (inv_nonneg.2 hν.le) hs
      nlinarith
    have hwidth : ν * s + τ = ν * s' := by
      dsimp [s']
      field_simp [hν.ne']
    have hjet := hD hν hν1 hc0 hs'1 η
    simp only [iteratedDeriv_zero] at hjet
    rw [← hwidth, hα_eq] at hjet
    have hrpow := DatumRemainderBound.rpow_shift_le hν hc0 hs hs_le_s' hs'_le hα_le_m
    have hpoly_mul : polyP D (B + 1) ν c * (s') ^ α ≤
        polyP D (B + 1 + m) ν c * s ^ α := by
      calc polyP D (B + 1) ν c * (s') ^ α
          ≤ polyP D (B + 1) ν c * ((1 + c + ν⁻¹) ^ m * s ^ α) :=
            mul_le_mul_of_nonneg_left hrpow (by unfold polyP; positivity)
        _ = polyP D (B + 1 + m) ν c * s ^ α := by
            unfold polyP
            rw [pow_add]
            ring
    have hjet' : (1 + |η|) ^ m * |iteratedDeriv B (heatKernel1 (ν * s + τ)) η| ≤
        polyP D (B + 1 + m) ν c * s ^ α := hjet.trans hpoly_mul
    have hw_pos : 0 < (1 + |η|) ^ m := by positivity
    rw [le_inv_mul_iff₀ hw_pos]
    exact hjet'
  -- Apply Lagrange Taylor remainder bound on `Icc 0 1`
  have htaylor := taylor_mean_remainder_bound (f := φ) (x := 1) zero_le_one
    hφ_cd_on ⟨zero_le_one, le_rfl⟩ hφ_N1_bd
  have htaylor_eval : taylorWithinEval φ N (Icc 0 1) 0 1 =
      ∑ j ∈ Finset.range (N + 1),
        (j.factorial : ℝ)⁻¹ *
          iteratedDeriv (b + 2 * ℓ + 2 * j) (heatKernel1 (ν * s)) η := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [smul_eq_mul, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hφ_cd_at 0 ⟨le_rfl, zero_le_one⟩).of_le (by exact_mod_cast le_top))
      ⟨le_rfl, zero_le_one⟩, hiter_g j 0 (hIcc_sub ⟨le_rfl, zero_le_one⟩)]
    dsimp [g]
    rw [sub_zero, one_pow, mul_one, add_zero]
  rw [htaylor_eval, Real.norm_eq_abs, sub_zero, one_pow, mul_one] at htaylor
  have hM_nn : 0 ≤ M_bound := by
    dsimp [M_bound]
    unfold polyP
    positivity
  have hfact_ge1 : (1 : ℝ) ≤ (N.factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos N)
  have htaylor' : |φ 1 - ∑ j ∈ Finset.range (N + 1),
      (j.factorial : ℝ)⁻¹ * iteratedDeriv (b + 2 * ℓ + 2 * j) (heatKernel1 (ν * s)) η| ≤
      M_bound :=
    htaylor.trans (div_le_self hM_nn hfact_ge1)
  -- Assemble the bound for `meanDatumRemainder`
  rw [DatumRemainderBound.slice_meanDatumRemainder_eq hν hc1 tr N b ℓ hs0 η]
  have hφ1 : φ 1 = iteratedDeriv (b + 2 * ℓ) (heatKernel1 (ν * s + 1)) η := by
    dsimp [φ, g]
  rw [← hφ1, abs_mul, abs_mul, abs_neg,
    abs_of_pos (by positivity : 0 < 8 * Real.pi * c⁻¹),
    abs_of_pos (pow_pos hν ℓ)]
  have hc_inv_le1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
  have hν_pow_le1 : ν ^ ℓ ≤ 1 := pow_le_one₀ hν.le hν1
  have hpref_le : 8 * Real.pi * c⁻¹ * ν ^ ℓ ≤ 8 * Real.pi := by
    have h1 : c⁻¹ * ν ^ ℓ ≤ 1 * 1 :=
      mul_le_mul hc_inv_le1 hν_pow_le1 (pow_nonneg hν.le ℓ) zero_le_one
    nlinarith [Real.pi_pos]
  have hη_pow_le : |η| ^ m ≤ (1 + |η|) ^ m :=
    pow_le_pow_left₀ (abs_nonneg η) (by linarith [abs_nonneg η]) m
  have hw_pos : 0 < (1 + |η|) ^ m := by positivity
  calc |η| ^ m * (8 * Real.pi * c⁻¹ * ν ^ ℓ *
        |φ 1 - ∑ j ∈ Finset.range (N + 1),
          (j.factorial : ℝ)⁻¹ * iteratedDeriv (b + 2 * ℓ + 2 * j) (heatKernel1 (ν * s)) η|)
      ≤ (1 + |η|) ^ m * (8 * Real.pi * M_bound) := by
        refine mul_le_mul hη_pow_le
          (mul_le_mul hpref_le htaylor' (abs_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = 8 * Real.pi * (((1 + |η|) ^ m * ((1 + |η|) ^ m)⁻¹) *
          (polyP D (B + 1 + m) ν c * s ^ α)) := by
        dsimp [M_bound]
        ring
    _ = polyP (8 * Real.pi * D) (B + 1 + m) ν c * s ^ α := by
        rw [mul_inv_cancel₀ hw_pos.ne']
        unfold polyP
        ring

end UnforcedLeray.Short.PartI
