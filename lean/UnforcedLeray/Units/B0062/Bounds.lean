import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Trigonometric

/-!
# B0062 helper: uniform derivative bounds

Helper file of blueprint unit **B0062** (`paper/main.tex` lines 1228–1237, label
`eq:st18-t00051`). The manuscript's sentence "boundedness of the required `r`-weighted
derivatives of `Ω` follows from Gaussian decay" (`paper/main.tex:1232`) is made precise here.

* `CbInf g`: `g` is smooth and every derivative `D^n g` is bounded on the whole space.
* `PolyBd d c`: a family `c t` (`t ∈ ℝ`) of smooth functions with
  `‖D^n (c t)(y)‖ ≤ K_n (1+|t|)^{d+n}` for all `t`, `y`. These are the coefficients of the
  chain rule for `T(t)`; `d` is the degree of polynomial growth in `t`.
* `cbInf_polyGauss`: `s ↦ P(s) e^{-s²/4}` has bounded derivatives of all orders (each
  derivative is again a polynomial times `e^{-s²/4}`, and `|s|^i e^{-s²/4} ≤ 1 + 4^i i!`).
* `polyBd_gexp`: `t ↦ e^{i t w(y)}` is `PolyBd 0` when `w ∈ CbInf` (Faà di Bruno bound
  `norm_iteratedFDeriv_comp_le`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff Nat
open Set

namespace UnforcedLeray.B0062

/-! ### Smooth functions with bounded derivatives -/

section CbInf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `g` is smooth and all its derivatives are bounded (`C_b^∞`). -/
def CbInf (g : E → F) : Prop :=
  ContDiff ℝ ∞ g ∧ ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖iteratedFDeriv ℝ n g y‖ ≤ K

theorem le_top_infty (n : ℕ) : ((n : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

theorem CbInf.const (c : F) : CbInf (fun _ : E => c) := by
  refine ⟨contDiff_const, fun n => ⟨‖c‖, norm_nonneg _, fun y => ?_⟩⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne h.ne' c]
    simp

theorem CbInf.add {g h : E → F} (hg : CbInf g) (hh : CbInf h) : CbInf (fun y => g y + h y) := by
  refine ⟨hg.1.add hh.1, fun n => ?_⟩
  obtain ⟨K₁, hK₁, h₁⟩ := hg.2 n
  obtain ⟨K₂, hK₂, h₂⟩ := hh.2 n
  refine ⟨K₁ + K₂, by positivity, fun y => ?_⟩
  have e := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := n) (x := y)
    (hg.1.contDiffAt.of_le (le_top_infty n)) (hh.1.contDiffAt.of_le (le_top_infty n))
  have e' : iteratedFDeriv ℝ n (fun y => g y + h y) y =
      iteratedFDeriv ℝ n g y + iteratedFDeriv ℝ n h y := e
  rw [e']
  exact (norm_add_le _ _).trans (add_le_add (h₁ y) (h₂ y))

theorem CbInf.clm_comp {g : E → F} (hg : CbInf g) (L : F →L[ℝ] G) :
    CbInf (fun y => L (g y)) := by
  refine ⟨L.contDiff.comp hg.1, fun n => ?_⟩
  obtain ⟨K, hK, h⟩ := hg.2 n
  refine ⟨‖L‖ * K, by positivity, fun y => ?_⟩
  have := L.norm_iteratedFDeriv_comp_left (f := g) (x := y) hg.1.contDiffAt (le_top_infty n)
  exact this.trans (mul_le_mul_of_nonneg_left (h y) (norm_nonneg _))

theorem CbInf.comp_clm {g : E → F} (hg : CbInf g) (L : G →L[ℝ] E) : CbInf (g ∘ L) := by
  refine ⟨hg.1.comp L.contDiff, fun n => ?_⟩
  obtain ⟨K, hK, h⟩ := hg.2 n
  refine ⟨K * ‖L‖ ^ n, by positivity, fun y => ?_⟩
  rw [L.iteratedFDeriv_comp_right hg.1 y (le_top_infty n)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (h _) (by positivity)

theorem CbInf.mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {g h : E → A} (hg : CbInf g)
    (hh : CbInf h) : CbInf (fun y => g y * h y) := by
  refine ⟨hg.1.mul hh.1, fun n => ?_⟩
  choose K₁ hK₁ h₁ using hg.2
  choose K₂ hK₂ h₂ using hh.2
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K₁ i * K₂ (n - i),
    Finset.sum_nonneg fun i _ => by have := hK₁ i; have := hK₂ (n - i); positivity,
    fun y => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hg.1 hh.1 y (le_top_infty n)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have a1 := h₁ i y
  have a2 := h₂ (n - i) y
  have hc : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left (mul_le_mul a1 a2 (norm_nonneg _) (hK₁ i)) hc
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i g y‖ * ‖iteratedFDeriv ℝ (n - i) h y‖
      = (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i g y‖ * ‖iteratedFDeriv ℝ (n - i) h y‖) := by ring
    _ ≤ (n.choose i : ℝ) * (K₁ i * K₂ (n - i)) := this
    _ = (n.choose i : ℝ) * K₁ i * K₂ (n - i) := by ring

/-- Directional derivatives of `C_b^∞` functions are `C_b^∞`. -/
theorem CbInf.dirDeriv {g : E → F} (hg : CbInf g) (v : E) :
    CbInf (fun y => fderiv ℝ g y v) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ g) := hg.1.fderiv_right (m := ∞) (by simp)
  refine ⟨hd.clm_apply contDiff_const, fun n => ?_⟩
  obtain ⟨K, hK, h⟩ := hg.2 (n + 1)
  refine ⟨‖ContinuousLinearMap.apply ℝ F v‖ * K, by positivity, fun y => ?_⟩
  have e : (fun y => fderiv ℝ g y v) = (ContinuousLinearMap.apply ℝ F v) ∘ fderiv ℝ g := rfl
  rw [e]
  refine ((ContinuousLinearMap.apply ℝ F v).norm_iteratedFDeriv_comp_left hd.contDiffAt
    (le_top_infty n)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

/-- The derivative of a `C_b^∞` function is `C_b^∞`. -/
theorem CbInf.fderiv {g : E → F} (hg : CbInf g) : CbInf (fderiv ℝ g) := by
  refine ⟨hg.1.fderiv_right (m := ∞) (by simp), fun n => ?_⟩
  obtain ⟨K, hK, h⟩ := hg.2 (n + 1)
  exact ⟨K, hK, fun y => by rw [norm_iteratedFDeriv_fderiv]; exact h y⟩

end CbInf

/-! ### One-dimensional Gaussians times polynomials -/

/-- The one-dimensional Gaussian `e^{-s²/4}`. -/
def gauss (s : ℝ) : ℝ := Real.exp (-(s ^ 2 / 4))

theorem gauss_pos (s : ℝ) : 0 < gauss s := Real.exp_pos _

theorem gauss_le_one (s : ℝ) : gauss s ≤ 1 := by
  rw [gauss, Real.exp_le_one_iff]
  have := sq_nonneg s
  linarith

theorem contDiff_gauss : ContDiff ℝ ∞ gauss :=
  Real.contDiff_exp.comp ((contDiff_id.pow 2).div_const 4).neg

/-- `P ↦ P' - (s/2) P`: the derivative of `P(s) e^{-s²/4}` is `(dstep P)(s) e^{-s²/4}`. -/
def dstep (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.derivative P - Polynomial.C (1 / 2) * Polynomial.X * P

theorem hasDerivAt_polyGauss (P : Polynomial ℝ) (s : ℝ) :
    HasDerivAt (fun s => P.eval s * gauss s) ((dstep P).eval s * gauss s) s := by
  have h1 := P.hasDerivAt s
  have h2 : HasDerivAt gauss (gauss s * (-(2 * s / 4))) s := by
    have := ((hasDerivAt_pow 2 s).div_const 4).neg.exp
    unfold gauss
    convert this using 1
    simp only [Pi.neg_apply]
    norm_num
  refine (h1.mul h2).congr_deriv ?_
  simp only [dstep, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  ring

theorem iteratedDeriv_polyGauss (n : ℕ) : ∀ P : Polynomial ℝ,
    iteratedDeriv n (fun s => P.eval s * gauss s) = fun s => (dstep^[n] P).eval s * gauss s := by
  induction n with
  | zero => intro P; simp
  | succ n ih =>
    intro P
    have hd : deriv (fun s => P.eval s * gauss s) = fun s => (dstep P).eval s * gauss s :=
      funext fun s => (hasDerivAt_polyGauss P s).deriv
    rw [iteratedDeriv_succ', hd, ih, Function.iterate_succ_apply]

/-- `|s|^i e^{-s²/4} ≤ 1 + 4^i i!`. -/
theorem abs_pow_mul_gauss_le (i : ℕ) (s : ℝ) : |s| ^ i * gauss s ≤ 1 + 4 ^ i * (i ! : ℝ) := by
  set x : ℝ := s ^ 2 / 4 with hx
  have hx0 : 0 ≤ x := by positivity
  have hfac : (0 : ℝ) < i ! := by exact_mod_cast Nat.factorial_pos i
  have h1 : x ^ i ≤ (i ! : ℝ) * Real.exp x := by
    have := Real.pow_div_factorial_le_exp x hx0 i
    rw [div_le_iff₀ hfac] at this
    linarith
  have hg : gauss s = (Real.exp x)⁻¹ := by rw [gauss, Real.exp_neg]
  have h2 : (s ^ 2) ^ i * gauss s ≤ 4 ^ i * (i ! : ℝ) := by
    have e : (s ^ 2) ^ i = 4 ^ i * x ^ i := by rw [hx, div_pow, mul_div_cancel₀]; positivity
    rw [e, hg, mul_assoc, ← div_eq_mul_inv]
    gcongr
    rw [div_le_iff₀ (Real.exp_pos x)]
    exact h1
  have h3 : |s| ^ i ≤ 1 + (s ^ 2) ^ i := by
    have e : (s ^ 2) ^ i = (|s| ^ i) ^ 2 := by
      rw [← sq_abs s]
      ring
    rw [e]
    nlinarith [sq_nonneg (|s| ^ i - 1)]
  have hg0 := (gauss_pos s).le
  calc |s| ^ i * gauss s ≤ (1 + (s ^ 2) ^ i) * gauss s := by gcongr
    _ = gauss s + (s ^ 2) ^ i * gauss s := by ring
    _ ≤ 1 + 4 ^ i * (i ! : ℝ) := add_le_add (gauss_le_one s) h2

/-- A polynomial times `e^{-s²/4}` is bounded. -/
theorem exists_bound_polyGauss (P : Polynomial ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s, |P.eval s * gauss s| ≤ K := by
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * (1 + 4 ^ i * (i ! : ℝ)),
    Finset.sum_nonneg fun i _ => by positivity, fun s => ?_⟩
  rw [abs_mul, abs_of_pos (gauss_pos s), Polynomial.eval_eq_sum_range]
  refine (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (gauss_pos s).le).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul, abs_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_pow_mul_gauss_le i s) (abs_nonneg _)

theorem contDiff_polyEval (P : Polynomial ℝ) : ContDiff ℝ ∞ fun s : ℝ => P.eval s := by
  have := Polynomial.contDiff_aeval (𝕜 := ℝ) P ∞
  simpa [Polynomial.coe_aeval_eq_eval] using this

/-- `s ↦ P(s) e^{-s²/4}` has bounded derivatives of every order. -/
theorem cbInf_polyGauss (P : Polynomial ℝ) : CbInf fun s : ℝ => P.eval s * gauss s := by
  refine ⟨(contDiff_polyEval P).mul contDiff_gauss, fun n => ?_⟩
  obtain ⟨K, hK, h⟩ := exists_bound_polyGauss (dstep^[n] P)
  refine ⟨K, hK, fun s => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_polyGauss, Real.norm_eq_abs]
  exact h s

theorem cbInf_gauss : CbInf gauss := by
  have := cbInf_polyGauss 1
  simpa using this

/-- `s ↦ s e^{-s²/4}`. -/
theorem cbInf_id_mul_gauss : CbInf fun s : ℝ => s * gauss s := by
  have := cbInf_polyGauss Polynomial.X
  simpa using this

/-! ### Families with polynomial growth in `t` -/

section PolyBd

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A family `c t : ℂ → F` (`t ∈ ℝ`) of smooth functions whose `n`-th derivatives are bounded
by `K_n (1 + |t|)^{d + n}`, uniformly in `y`. -/
def PolyBd (d : ℕ) (c : ℝ → ℂ → F) : Prop :=
  (∀ t, ContDiff ℝ ∞ (c t)) ∧
    ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ t y, ‖iteratedFDeriv ℝ n (c t) y‖ ≤ K * (1 + |t|) ^ (d + n)

theorem one_le_one_add_abs (t : ℝ) : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]

theorem PolyBd.of_cbInf {g : ℂ → F} (hg : CbInf g) : PolyBd 0 (fun _ => g) := by
  refine ⟨fun _ => hg.1, fun n => ?_⟩
  obtain ⟨K, hK, h⟩ := hg.2 n
  refine ⟨K, hK, fun t y => (h y).trans ?_⟩
  have := one_le_pow₀ (n := 0 + n) (one_le_one_add_abs t)
  nlinarith

theorem PolyBd.mono {d d' : ℕ} {c : ℝ → ℂ → F} (h : PolyBd d c) (hd : d ≤ d') : PolyBd d' c := by
  refine ⟨h.1, fun n => ?_⟩
  obtain ⟨K, hK, hb⟩ := h.2 n
  refine ⟨K, hK, fun t y => (hb t y).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_one_add_abs t) (by omega)) hK

theorem PolyBd.add {d : ℕ} {a b : ℝ → ℂ → F} (ha : PolyBd d a) (hb : PolyBd d b) :
    PolyBd d (fun t y => a t y + b t y) := by
  refine ⟨fun t => (ha.1 t).add (hb.1 t), fun n => ?_⟩
  obtain ⟨K₁, hK₁, h₁⟩ := ha.2 n
  obtain ⟨K₂, hK₂, h₂⟩ := hb.2 n
  refine ⟨K₁ + K₂, by positivity, fun t y => ?_⟩
  have e := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := n) (x := y)
    ((ha.1 t).contDiffAt.of_le (le_top_infty n)) ((hb.1 t).contDiffAt.of_le (le_top_infty n))
  have e' : iteratedFDeriv ℝ n (fun y => a t y + b t y) y =
      iteratedFDeriv ℝ n (a t) y + iteratedFDeriv ℝ n (b t) y := e
  rw [e', add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h₁ t y) (h₂ t y))

theorem PolyBd.clm_comp {d : ℕ} {c : ℝ → ℂ → F} (h : PolyBd d c) (L : F →L[ℝ] G) :
    PolyBd d (fun t y => L (c t y)) := by
  refine ⟨fun t => L.contDiff.comp (h.1 t), fun n => ?_⟩
  obtain ⟨K, hK, hb⟩ := h.2 n
  refine ⟨‖L‖ * K, by positivity, fun t y => ?_⟩
  have := L.norm_iteratedFDeriv_comp_left (f := c t) (x := y) (h.1 t).contDiffAt (le_top_infty n)
  refine this.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb t y) (norm_nonneg _)

theorem PolyBd.mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {d₁ d₂ : ℕ} {a b : ℝ → ℂ → A}
    (ha : PolyBd d₁ a) (hb : PolyBd d₂ b) : PolyBd (d₁ + d₂) (fun t y => a t y * b t y) := by
  refine ⟨fun t => (ha.1 t).mul (hb.1 t), fun n => ?_⟩
  choose K₁ hK₁ h₁ using ha.2
  choose K₂ hK₂ h₂ using hb.2
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K₁ i * K₂ (n - i),
    Finset.sum_nonneg fun i _ => by have := hK₁ i; have := hK₂ (n - i); positivity,
    fun t y => ?_⟩
  refine (norm_iteratedFDeriv_mul_le (ha.1 t) (hb.1 t) y (le_top_infty n)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have a1 := h₁ i t y
  have a2 := h₂ (n - i) t y
  have hc : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
  have e : (1 + |t|) ^ (d₁ + d₂ + n) = (1 + |t|) ^ (d₁ + i) * (1 + |t|) ^ (d₂ + (n - i)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e]
  have hb0 : 0 ≤ K₁ i * (1 + |t|) ^ (d₁ + i) := (norm_nonneg _).trans a1
  have := mul_le_mul_of_nonneg_left (mul_le_mul a1 a2 (norm_nonneg _) hb0) hc
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (a t) y‖ * ‖iteratedFDeriv ℝ (n - i) (b t) y‖
      = (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i (a t) y‖ * ‖iteratedFDeriv ℝ (n - i) (b t) y‖) := by
        ring
    _ ≤ (n.choose i : ℝ) * ((K₁ i * (1 + |t|) ^ (d₁ + i)) * (K₂ (n - i) * (1 + |t|) ^ (d₂ + (n - i)))) :=
        this
    _ = (n.choose i : ℝ) * K₁ i * K₂ (n - i) * ((1 + |t|) ^ (d₁ + i) * (1 + |t|) ^ (d₂ + (n - i))) := by
        ring

/-- Directional derivatives raise the degree by one. -/
theorem PolyBd.dirDeriv {d : ℕ} {c : ℝ → ℂ → F} (h : PolyBd d c) (v : ℂ) :
    PolyBd (d + 1) (fun t y => fderiv ℝ (c t) y v) := by
  have hd : ∀ t, ContDiff ℝ ∞ (fderiv ℝ (c t)) := fun t => (h.1 t).fderiv_right (m := ∞) (by simp)
  refine ⟨fun t => (hd t).clm_apply contDiff_const, fun n => ?_⟩
  obtain ⟨K, hK, hb⟩ := h.2 (n + 1)
  refine ⟨‖ContinuousLinearMap.apply ℝ F v‖ * K, by positivity, fun t y => ?_⟩
  have e : (fun y => fderiv ℝ (c t) y v) = (ContinuousLinearMap.apply ℝ F v) ∘ fderiv ℝ (c t) :=
    rfl
  show ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ (c t) y v) y‖ ≤ _
  rw [e]
  refine ((ContinuousLinearMap.apply ℝ F v).norm_iteratedFDeriv_comp_left (hd t).contDiffAt
    (le_top_infty n)).trans ?_
  rw [norm_iteratedFDeriv_fderiv, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((hb t y).trans (le_of_eq ?_)) (norm_nonneg _)
  congr 2
  omega

/-- Multiplication by `t` raises the degree by one. -/
theorem PolyBd.smul_t {d : ℕ} {c : ℝ → ℂ → F} (h : PolyBd d c) :
    PolyBd (d + 1) (fun t y => t • c t y) := by
  refine ⟨fun t => (h.1 t).const_smul t, fun n => ?_⟩
  obtain ⟨K, hK, hb⟩ := h.2 n
  refine ⟨K, hK, fun t y => ?_⟩
  rw [iteratedFDeriv_const_smul_apply' ((h.1 t).contDiffAt.of_le (le_top_infty n)), norm_smul,
    Real.norm_eq_abs]
  have h1 : |t| ≤ 1 + |t| := by linarith
  have e : (1 + |t|) ^ (d + 1 + n) = (1 + |t|) * (1 + |t|) ^ (d + n) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [e]
  calc |t| * ‖iteratedFDeriv ℝ n (c t) y‖ ≤ (1 + |t|) * (K * (1 + |t|) ^ (d + n)) :=
        mul_le_mul h1 (hb t y) (norm_nonneg _) (by linarith [abs_nonneg t])
    _ = K * ((1 + |t|) * (1 + |t|) ^ (d + n)) := by ring

/-- Sup bound: `‖c t y‖ ≤ K (1 + |t|)^d`. -/
theorem PolyBd.norm_le {d : ℕ} {c : ℝ → ℂ → F} (h : PolyBd d c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t y, ‖c t y‖ ≤ K * (1 + |t|) ^ d := by
  obtain ⟨K, hK, hb⟩ := h.2 0
  exact ⟨K, hK, fun t y => by simpa [norm_iteratedFDeriv_zero] using hb t y⟩

end PolyBd

/-! ### The unimodular phase `e^{i x}` -/

/-- `x ↦ e^{ix}`, `ℝ → ℂ`. -/
def gexp (x : ℝ) : ℂ := Complex.exp (x * Complex.I)

theorem norm_gexp (x : ℝ) : ‖gexp x‖ = 1 := Complex.norm_exp_ofReal_mul_I x

theorem contDiff_gexp : ContDiff ℝ ∞ gexp := by
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  exact h1.cexp

theorem hasDerivAt_gexp (x : ℝ) : HasDerivAt gexp (Complex.I * gexp x) x := by
  have h := ((hasDerivAt_id x).ofReal_comp.mul_const Complex.I).cexp
  have e : (fun y : ℝ => Complex.exp (((id y : ℝ) : ℂ) * Complex.I)) = gexp := rfl
  rw [e] at h
  refine h.congr_deriv ?_
  simp only [id, Complex.ofReal_one, one_mul, gexp]
  ring

theorem iteratedDeriv_gexp (n : ℕ) : iteratedDeriv n gexp = fun x => Complex.I ^ n * gexp x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul _ (hasDerivAt_gexp x).differentiableAt, (hasDerivAt_gexp x).deriv]
    ring

theorem norm_iteratedFDeriv_gexp (n : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ n gexp x‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_gexp, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, norm_gexp]

/-- If `w ∈ C_b^∞` is real, the phases `y ↦ e^{i t w(y)}` have derivatives of order `n` bounded
by `C_n (1 + |t|)^n` (Faà di Bruno). -/
theorem polyBd_gexp {w : ℂ → ℝ} (hw : CbInf w) : PolyBd 0 (fun t y => gexp (t * w y)) := by
  have hin : ∀ t : ℝ, ContDiff ℝ ∞ (fun y => t * w y) := fun t => contDiff_const.mul hw.1
  refine ⟨fun t => contDiff_gexp.comp (hin t), fun n => ?_⟩
  choose Kw hKw0 hKw using hw.2
  set K : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), Kw i with hKdef
  have hK1 : 1 ≤ K := by
    have := Finset.sum_nonneg (s := Finset.range (n + 1)) fun i _ => hKw0 i
    linarith
  have hKi : ∀ i, i ≤ n → Kw i ≤ K := by
    intro i hi
    have := Finset.single_le_sum (f := Kw) (fun j _ => hKw0 j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    linarith
  refine ⟨(n ! : ℝ) * K ^ n, by positivity, fun t y => ?_⟩
  have hT := one_le_one_add_abs t
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (fun y => t * w y) y‖ ≤ (K * (1 + |t|)) ^ i := by
    intro i hi1 hin'
    have e : iteratedFDeriv ℝ i (fun y => t * w y) y = t • iteratedFDeriv ℝ i w y := by
      rw [show (fun y => t * w y) = fun y => t • w y from rfl]
      exact iteratedFDeriv_const_smul_apply' (hw.1.contDiffAt.of_le (le_top_infty i))
    rw [e, norm_smul, Real.norm_eq_abs]
    have h1 : 1 ≤ K * (1 + |t|) := by nlinarith
    calc |t| * ‖iteratedFDeriv ℝ i w y‖ ≤ (1 + |t|) * K :=
          mul_le_mul (by linarith) ((hKw i y).trans (hKi i hin')) (norm_nonneg _) (by linarith)
      _ = K * (1 + |t|) := by ring
      _ ≤ (K * (1 + |t|)) ^ i := le_self_pow₀ h1 (by omega)
  have hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i gexp (t * w y)‖ ≤ 1 := fun i _ =>
    (norm_iteratedFDeriv_gexp i _).le
  have := norm_iteratedFDeriv_comp_le contDiff_gexp (hin t) (le_top_infty n) y hC hD
  calc ‖iteratedFDeriv ℝ n (fun y => gexp (t * w y)) y‖ ≤ (n ! : ℝ) * 1 * (K * (1 + |t|)) ^ n :=
        this
    _ = (n ! : ℝ) * K ^ n * (1 + |t|) ^ (0 + n) := by rw [mul_pow, zero_add]; ring

end UnforcedLeray.B0062
