import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The regular solution in `s = r²` (INF18 O12, bypass B4)


§4 bypass B4 and §5 target O12. Manuscript `paper/main.tex` lines 1159--1168 (blueprint
unit B0053): near zero put `s = r²`, `φ = r² b(s)`; the equation becomes
`4(s b'' + 3 b') = [k(√s)/(Ω(√s) - c)] b`, and its regular solution is smooth.

The manuscript uses the Frobenius series. Here, for any smooth coefficient `a : ℝ → ℂ`, the
equation `4(s b'' + 3 b') = a b`, `b(0) = 1`, is solved on all of `ℝ` by the Volterra equation
`b(s) = 1 + ∫₀ˢ (1/4) ∫₀¹ u² (a b)(τ u) du dτ` (Picard iteration with factorial bounds); the
solution is `C^∞` by a bootstrap (`contDiff_avgPow`). This is a real-variable, global version
of the scoping signature `exists_regular_analytic` (holomorphic on a small disc): every
consumer uses smoothness only.

Main declarations: `avgPow`, `hasDerivAt_avgPow`, `contDiff_avgPow`, `avgPow_identity`,
`picardOp`, `picardTerm`, `regSol`, `regSol_eq`, `hasDerivAt_regSol`, `contDiff_regSol`,
`regSol_ode`, `exists_regular_solution`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff Nat

namespace UnforcedLeray.ComplexODEC

/-! ### The averaging operator `g ↦ ∫₀¹ uᵖ g(su) du` -/

/-- `avgPow p g s = ∫₀¹ uᵖ g(su) du`. For `s ≠ 0` this is `s^{-p-1} ∫₀ˢ σᵖ g(σ) dσ`. -/
def avgPow (p : ℕ) (g : ℝ → ℂ) (s : ℝ) : ℂ := ∫ u in (0 : ℝ)..1, (u : ℂ) ^ p * g (s * u)

theorem continuous_avgPow_integrand (p : ℕ) {g : ℝ → ℂ} (hg : Continuous g) :
    Continuous (Function.uncurry fun (s u : ℝ) => (u : ℂ) ^ p * g (s * u)) :=
  ((Complex.continuous_ofReal.comp continuous_snd).pow p).mul
    (hg.comp (continuous_fst.mul continuous_snd))

theorem continuous_avgPow (p : ℕ) {g : ℝ → ℂ} (hg : Continuous g) : Continuous (avgPow p g) :=
  continuous_parametric_intervalIntegral_of_continuous' (continuous_avgPow_integrand p hg) 0 1

theorem norm_avgPow_le {p : ℕ} {g : ℝ → ℂ} {s C : ℝ}
    (h : ∀ u ∈ Icc (0 : ℝ) 1, ‖g (s * u)‖ ≤ C) : ‖avgPow p g s‖ ≤ C := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (h 0 ⟨le_rfl, zero_le_one⟩)
  have := norm_integral_le_of_norm_le_const_ae (a := 0) (b := 1) (C := C)
    (f := fun u : ℝ => (u : ℂ) ^ p * g (s * u)) ?_
  · simpa [avgPow] using this
  · refine ae_of_all _ fun u hu => ?_
    rw [uIoc_of_le zero_le_one] at hu
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
    calc u ^ p * ‖g (s * u)‖ ≤ 1 * C :=
          mul_le_mul (pow_le_one₀ hu.1.le hu.2) (h u ⟨hu.1.le, hu.2⟩) (norm_nonneg _)
            zero_le_one
      _ = C := one_mul C

/-- Differentiation under the integral: `(avgPow p g)' = avgPow (p+1) g'`. -/
theorem hasDerivAt_avgPow (p : ℕ) {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g) (s : ℝ) :
    HasDerivAt (avgPow p g) (avgPow (p + 1) (deriv g) s) s := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hg0 : Continuous g := hgd.continuous
  have hgc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Icc (-(|s| + 1)) (|s| + 1), ‖deriv g x‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn hgc.continuousOn
  have hcont : ∀ x : ℝ, Continuous fun u : ℝ => (u : ℂ) ^ p * g (x * u) := fun x => by
    fun_prop
  have hcont' : Continuous fun u : ℝ => (u : ℂ) ^ p * ((u : ℝ) • deriv g (s * u)) := by
    fun_prop
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0) (b := 1)
    (F := fun (x u : ℝ) => (u : ℂ) ^ p * g (x * u))
    (F' := fun (x u : ℝ) => (u : ℂ) ^ p * ((u : ℝ) • deriv g (x * u)))
    (x₀ := s) (s := Metric.ball s 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds s one_pos)
    (Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
    ((hcont s).intervalIntegrable 0 1) hcont'.aestronglyMeasurable
    (ae_of_all _ fun u hu x hx => by
      rw [uIoc_of_le zero_le_one] at hu
      have hxu : x * u ∈ Icc (-(|s| + 1)) (|s| + 1) := by
        have hx' : |x| ≤ |s| + 1 := by
          have h1 := Metric.mem_ball.mp hx
          rw [Real.dist_eq] at h1
          have h2 := abs_sub_abs_le_abs_sub x s
          linarith
        have : |x * u| ≤ |s| + 1 := by
          rw [abs_mul, abs_of_pos hu.1]
          calc |x| * u ≤ |x| * 1 := mul_le_mul_of_nonneg_left hu.2 (abs_nonneg x)
            _ ≤ |s| + 1 := by linarith
        exact abs_le.mp this
      rw [norm_mul, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
      calc u ^ p * (u * ‖deriv g (x * u)‖) = u ^ (p + 1) * ‖deriv g (x * u)‖ := by ring
        _ ≤ 1 * C := mul_le_mul (pow_le_one₀ hu.1.le hu.2) (hC _ hxu) (norm_nonneg _)
            zero_le_one
        _ = C := one_mul C)
    intervalIntegrable_const
    (ae_of_all _ fun u _ x _ => by
      have h1 : HasDerivAt (fun x : ℝ => x * u) u x := hasDerivAt_mul_const u
      exact ((hgd (x * u)).hasDerivAt.scomp x h1).const_mul ((u : ℂ) ^ p))
  have e : (∫ u in (0 : ℝ)..1, (u : ℂ) ^ p * ((u : ℝ) • deriv g (s * u))) =
      avgPow (p + 1) (deriv g) s := by
    unfold avgPow
    refine integral_congr fun u _ => ?_
    simp only [Complex.real_smul]
    ring
  rw [← e]
  exact key.2

/-- `avgPow p g` is `Cⁿ` when `g` is. -/
theorem contDiff_avgPow : ∀ (n : ℕ) (p : ℕ) {g : ℝ → ℂ}, ContDiff ℝ n g →
    ContDiff ℝ n (avgPow p g)
  | 0, p, g, hg => contDiff_zero.2 (continuous_avgPow p (contDiff_zero.1 hg))
  | n + 1, p, g, hg => by
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hd : deriv (avgPow p g) = avgPow (p + 1) (deriv g) :=
      funext fun s => (hasDerivAt_avgPow p hg1 s).deriv
    have hg' : ContDiff ℝ n (deriv g) := by
      have h := hg
      rw [Nat.cast_succ, contDiff_succ_iff_deriv] at h
      exact h.2.2
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun s => (hasDerivAt_avgPow p hg1 s).differentiableAt, by simp, ?_⟩
    rw [hd]
    exact contDiff_avgPow n (p + 1) hg'

theorem contDiff_avgPow_infty (p : ℕ) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (avgPow p g) :=
  contDiff_infty.2 fun n => contDiff_avgPow n p (contDiff_infty.1 hg n)

/-- Integration by parts in `u`: `s · avgPow 3 g' + 3 · avgPow 2 g = g`. -/
theorem avgPow_identity {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g) (s : ℝ) :
    (s : ℂ) * avgPow 3 (deriv g) s + 3 * avgPow 2 g s = g s := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hg0 : Continuous g := hgd.continuous
  have hgc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => (u : ℂ) ^ 3 * g (s * u))
      (3 * (u : ℂ) ^ 2 * g (s * u) + (u : ℂ) ^ 3 * ((s : ℂ) * deriv g (s * u))) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => (u : ℂ) ^ 3) (3 * (u : ℂ) ^ 2) u := by
      have := (hasDerivAt_pow 3 u).ofReal_comp
      simpa using this
    have hlin : HasDerivAt (fun u : ℝ => s * u) s u := by
      simpa using (hasDerivAt_id u).const_mul s
    have h2 : HasDerivAt (fun u : ℝ => g (s * u)) ((s : ℝ) • deriv g (s * u)) u :=
      (hgd (s * u)).hasDerivAt.scomp u hlin
    rw [Complex.real_smul] at h2
    exact h1.mul h2
  have hi1 : IntervalIntegrable (fun u : ℝ => 3 * (u : ℂ) ^ 2 * g (s * u)) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) 0 1
  have hi2 : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ 3 * ((s : ℂ) * deriv g (s * u)))
      volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) 0 1
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv (hi1.add hi2)
  have e1 : ((1 : ℝ) : ℂ) ^ 3 * g (s * 1) - ((0 : ℝ) : ℂ) ^ 3 * g (s * 0) = g s := by simp
  rw [e1, integral_add hi1 hi2] at hFTC
  rw [← hFTC]
  unfold avgPow
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, add_comm]
  congr 1
  · exact integral_congr fun u _ => by ring
  · exact integral_congr fun u _ => by ring

/-! ### Picard iteration -/

/-- The Volterra operator `f ↦ ∫₀ˢ (1/4) avgPow 2 (a f)`. -/
def picardOp (a f : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ τ in (0 : ℝ)..s, avgPow 2 (fun σ => a σ * f σ) τ / 4

/-- The Picard terms `t₀ = 1`, `t_{n+1} = picardOp a tₙ`. -/
def picardTerm (a : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun _ => 1
  | n + 1 => picardOp a (picardTerm a n)

theorem picardTerm_zero (a : ℝ → ℂ) (s : ℝ) : picardTerm a 0 s = 1 := rfl

theorem picardTerm_succ (a : ℝ → ℂ) (n : ℕ) : picardTerm a (n + 1) = picardOp a (picardTerm a n) :=
  rfl

theorem continuous_picardOp {a f : ℝ → ℂ} (ha : Continuous a) (hf : Continuous f) :
    Continuous (picardOp a f) := by
  have hc : Continuous fun τ => avgPow 2 (fun σ => a σ * f σ) τ / 4 :=
    (continuous_avgPow 2 (ha.mul hf)).div_const 4
  exact continuous_primitive (fun x y => hc.intervalIntegrable x y) 0

theorem continuous_picardTerm {a : ℝ → ℂ} (ha : Continuous a) :
    ∀ n, Continuous (picardTerm a n)
  | 0 => continuous_const
  | n + 1 => continuous_picardOp ha (continuous_picardTerm ha n)

/-- `‖∫₀ˢ f‖ ≤ C |s|^{m+1}/(m+1)` when `‖f τ‖ ≤ C |τ|^m` for `|τ| ≤ |s|`. -/
theorem norm_integral_le_pow {f : ℝ → ℂ} (hf : Continuous f) {C : ℝ} {m : ℕ} {s : ℝ}
    (h : ∀ τ, |τ| ≤ |s| → ‖f τ‖ ≤ C * |τ| ^ m) :
    ‖∫ τ in (0 : ℝ)..s, f τ‖ ≤ C * |s| ^ (m + 1) / (m + 1) := by
  rcases le_total 0 s with hs | hs
  · have hb := norm_integral_le_of_norm_le (μ := volume) hs (g := fun τ => C * τ ^ m)
      (ae_of_all _ fun τ hτ => by
        have h' := h τ (by rw [abs_of_pos hτ.1, abs_of_nonneg hs]; exact hτ.2)
        rwa [abs_of_pos hτ.1] at h')
      ((continuous_const.mul (continuous_pow m)).intervalIntegrable 0 s)
    rw [intervalIntegral.integral_const_mul, integral_pow] at hb
    rw [abs_of_nonneg hs]
    have e : C * ((s ^ (m + 1) - 0 ^ (m + 1)) / (m + 1)) = C * s ^ (m + 1) / (m + 1) := by
      rw [zero_pow (Nat.succ_ne_zero m), sub_zero, mul_div_assoc]
    rw [e] at hb
    exact_mod_cast hb
  · rw [integral_symm, norm_neg]
    have hb := norm_integral_le_of_norm_le (μ := volume) hs (g := fun τ => C * (-τ) ^ m)
      (ae_of_all _ fun τ hτ => by
        have hτ0 : τ ≤ 0 := hτ.2
        have h' := h τ (by rw [abs_of_nonpos hτ0, abs_of_nonpos hs]; linarith [hτ.1])
        rwa [abs_of_nonpos hτ0] at h')
      ((continuous_const.mul (continuous_neg.pow m)).intervalIntegrable s 0)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg (fun x : ℝ => x ^ m),
      neg_zero, integral_pow] at hb
    rw [abs_of_nonpos hs]
    have e : C * (((-s) ^ (m + 1) - 0 ^ (m + 1)) / (m + 1)) =
        C * (-s) ^ (m + 1) / (m + 1) := by
      rw [zero_pow (Nat.succ_ne_zero m), sub_zero, mul_div_assoc]
    rw [e] at hb
    exact_mod_cast hb

/-- A bound for the coefficient on `[-L, L]`, in the form `‖a‖ ≤ 4K`. -/
theorem exists_picard_bound {a : ℝ → ℂ} (ha : Continuous a) (L : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ, |σ| ≤ L → ‖a σ‖ ≤ 4 * K := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -L) (b := L)).exists_bound_of_continuousOn
    ha.continuousOn
  refine ⟨max C 0 / 4, by positivity, fun σ hσ => ?_⟩
  have h1 := hC σ ⟨(abs_le.mp hσ).1, (abs_le.mp hσ).2⟩
  have h2 := le_max_left C 0
  linarith

theorem norm_avgPow_picardTerm_le {a : ℝ → ℂ} (ha : Continuous a) {L K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ σ, |σ| ≤ L → ‖a σ‖ ≤ 4 * K) (n : ℕ)
    (hn : ∀ σ, |σ| ≤ L → ‖picardTerm a n σ‖ ≤ (K * |σ|) ^ n / n !) {τ : ℝ} (hτ : |τ| ≤ L) :
    ‖avgPow 2 (fun σ => a σ * picardTerm a n σ) τ‖ ≤ 4 * K * ((K * |τ|) ^ n / n !) := by
  refine norm_avgPow_le fun u hu => ?_
  have hτu : |τ * u| ≤ |τ| := by
    rw [abs_mul, abs_of_nonneg hu.1]
    exact mul_le_of_le_one_right (abs_nonneg τ) hu.2
  rw [norm_mul]
  refine mul_le_mul (hK _ (hτu.trans hτ)) ?_ (norm_nonneg _) (by positivity)
  refine (hn _ (hτu.trans hτ)).trans ?_
  gcongr

/-- Factorial bounds for the Picard terms on `[-L, L]`. -/
theorem norm_picardTerm_le {a : ℝ → ℂ} (ha : Continuous a) {L K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ σ, |σ| ≤ L → ‖a σ‖ ≤ 4 * K) :
    ∀ n s, |s| ≤ L → ‖picardTerm a n s‖ ≤ (K * |s|) ^ n / n ! := by
  intro n
  induction n with
  | zero => intro s _; simp [picardTerm]
  | succ n ih =>
    intro s hs
    show ‖∫ τ in (0 : ℝ)..s, avgPow 2 (fun σ => a σ * picardTerm a n σ) τ / 4‖ ≤ _
    have hb := norm_integral_le_pow (C := K ^ (n + 1) / n !) (m := n) (s := s)
      ((continuous_avgPow 2 (ha.mul (continuous_picardTerm ha n))).div_const 4)
      (fun τ hτ => by
        have h := norm_avgPow_picardTerm_le ha hK0 hK n (fun σ hσ => ih σ hσ)
          (hτ.trans hs)
        rw [norm_div, Complex.norm_ofNat]
        calc ‖avgPow 2 (fun σ => a σ * picardTerm a n σ) τ‖ / 4
            ≤ 4 * K * ((K * |τ|) ^ n / n !) / 4 := by gcongr
          _ = K ^ (n + 1) / n ! * |τ| ^ n := by rw [mul_pow, pow_succ]; ring)
    refine hb.trans (le_of_eq ?_)
    rw [Nat.factorial_succ, mul_pow, pow_succ]
    push_cast
    field_simp

/-! ### The regular solution -/

/-- The regular solution `b = Σₙ tₙ` of `b = 1 + picardOp a b`. -/
def regSol (a : ℝ → ℂ) (s : ℝ) : ℂ := ∑' n, picardTerm a n s

theorem hasSum_regSol {a : ℝ → ℂ} (ha : Continuous a) (s : ℝ) :
    HasSum (fun n => picardTerm a n s) (regSol a s) := by
  obtain ⟨K, hK0, hK⟩ := exists_picard_bound ha |s|
  have hs : Summable fun n => picardTerm a n s :=
    Summable.of_norm_bounded (Real.summable_pow_div_factorial (K * |s|))
      fun n => norm_picardTerm_le ha hK0 hK n s le_rfl
  exact hs.hasSum

theorem continuous_regSol {a : ℝ → ℂ} (ha : Continuous a) : Continuous (regSol a) := by
  refine continuous_iff_continuousAt.2 fun s₀ => ?_
  set L : ℝ := |s₀| + 1
  obtain ⟨K, hK0, hK⟩ := exists_picard_bound ha L
  have hon : ContinuousOn (regSol a) (Ioo (-L) L) := by
    refine continuousOn_tsum (fun n => (continuous_picardTerm ha n).continuousOn)
      (Real.summable_pow_div_factorial (K * L)) fun n x hx => ?_
    have hxL : |x| ≤ L := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    refine (norm_picardTerm_le ha hK0 hK n x hxL).trans ?_
    gcongr
  exact hon.continuousAt (Ioo_mem_nhds (by linarith [abs_nonneg s₀, neg_abs_le s₀])
    (by linarith [le_abs_self s₀]))

theorem hasSum_avgPow_picardTerm {a : ℝ → ℂ} (ha : Continuous a) (τ : ℝ) :
    HasSum (fun n => avgPow 2 (fun σ => a σ * picardTerm a n σ) τ)
      (avgPow 2 (fun σ => a σ * regSol a σ) τ) := by
  obtain ⟨K, hK0, hK⟩ := exists_picard_bound ha |τ|
  have hn := norm_picardTerm_le ha hK0 hK
  refine hasSum_integral_of_dominated_convergence
    (bound := fun n _ => 4 * K * ((K * |τ|) ^ n / n !)) (fun n => ?_) (fun n => ?_)
    (ae_of_all _ fun u _ => (Real.summable_pow_div_factorial (K * |τ|)).mul_left (4 * K))
    intervalIntegrable_const (ae_of_all _ fun u _ => ?_)
  · exact ((continuous_avgPow_integrand 2 (ha.mul (continuous_picardTerm ha n))).comp
      (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · refine ae_of_all _ fun u hu => ?_
    rw [uIoc_of_le zero_le_one] at hu
    have hτu : |τ * u| ≤ |τ| := by
      rw [abs_mul, abs_of_pos hu.1]
      exact mul_le_of_le_one_right (abs_nonneg τ) hu.2
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1, norm_mul]
    calc u ^ 2 * (‖a (τ * u)‖ * ‖picardTerm a n (τ * u)‖)
        ≤ 1 * (4 * K * ((K * |τ|) ^ n / n !)) := by
          refine mul_le_mul (pow_le_one₀ hu.1.le hu.2) ?_ (by positivity) zero_le_one
          refine mul_le_mul (hK _ hτu) ?_ (norm_nonneg _) (by positivity)
          refine (hn n _ hτu).trans ?_
          gcongr
      _ = 4 * K * ((K * |τ|) ^ n / n !) := one_mul _
  · exact (hasSum_regSol ha (τ * u)).mul_left (a (τ * u)) |>.mul_left ((u : ℂ) ^ 2)

theorem hasSum_picardOp {a : ℝ → ℂ} (ha : Continuous a) (s : ℝ) :
    HasSum (fun n => picardOp a (picardTerm a n) s) (picardOp a (regSol a) s) := by
  obtain ⟨K, hK0, hK⟩ := exists_picard_bound ha |s|
  have hn := norm_picardTerm_le ha hK0 hK
  refine hasSum_integral_of_dominated_convergence
    (bound := fun n _ => K * ((K * |s|) ^ n / n !)) (fun n => ?_) (fun n => ?_)
    (ae_of_all _ fun u _ => (Real.summable_pow_div_factorial (K * |s|)).mul_left K)
    intervalIntegrable_const (ae_of_all _ fun τ _ => (hasSum_avgPow_picardTerm ha τ).div_const 4)
  · exact ((continuous_avgPow 2 (ha.mul (continuous_picardTerm ha n))).div_const 4
      ).aestronglyMeasurable
  · refine ae_of_all _ fun τ hτ => ?_
    have hτs : |τ| ≤ |s| := by
      rcases le_total 0 s with h | h
      · rw [uIoc_of_le h] at hτ
        rw [abs_of_pos hτ.1, abs_of_nonneg h]; exact hτ.2
      · rw [uIoc_of_ge h] at hτ
        rw [abs_of_nonpos hτ.2, abs_of_nonpos h]; linarith [hτ.1]
    have h := norm_avgPow_picardTerm_le ha hK0 hK n (fun σ hσ => hn n σ hσ) hτs
    rw [norm_div, Complex.norm_ofNat]
    calc ‖avgPow 2 (fun σ => a σ * picardTerm a n σ) τ‖ / 4
        ≤ 4 * K * ((K * |s|) ^ n / n !) / 4 := by
          refine div_le_div_of_nonneg_right (h.trans ?_) (by norm_num)
          gcongr
      _ = K * ((K * |s|) ^ n / n !) := by ring

/-- The Volterra equation `b = 1 + picardOp a b`. -/
theorem regSol_eq {a : ℝ → ℂ} (ha : Continuous a) (s : ℝ) :
    regSol a s = 1 + picardOp a (regSol a) s := by
  have h1 : HasSum (fun n => picardTerm a (n + 1) s) (picardOp a (regSol a) s) := by
    simp only [picardTerm_succ]
    exact hasSum_picardOp ha s
  have h2 := HasSum.zero_add (f := fun n => picardTerm a n s) h1
  rw [picardTerm_zero] at h2
  exact (hasSum_regSol ha s).unique h2

theorem regSol_zero {a : ℝ → ℂ} (ha : Continuous a) : regSol a 0 = 1 := by
  rw [regSol_eq ha 0, picardOp, integral_same, add_zero]

/-- `b' = (1/4) avgPow 2 (a b)`. -/
theorem hasDerivAt_regSol {a : ℝ → ℂ} (ha : Continuous a) (s : ℝ) :
    HasDerivAt (regSol a) (avgPow 2 (fun σ => a σ * regSol a σ) s / 4) s := by
  have hc : Continuous fun τ => avgPow 2 (fun σ => a σ * regSol a σ) τ / 4 :=
    (continuous_avgPow 2 (ha.mul (continuous_regSol ha))).div_const 4
  have h := ((hc.integral_hasStrictDerivAt 0 s).hasDerivAt).const_add 1
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun s => regSol_eq ha s)

theorem deriv_regSol {a : ℝ → ℂ} (ha : Continuous a) :
    deriv (regSol a) = fun s => avgPow 2 (fun σ => a σ * regSol a σ) s / 4 :=
  funext fun s => (hasDerivAt_regSol ha s).deriv

/-- The regular solution is `C^∞` when the coefficient is. -/
theorem contDiff_regSol {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (regSol a) := by
  have hac := ha.continuous
  refine contDiff_infty.2 fun n => ?_
  induction n with
  | zero => exact contDiff_zero.2 (continuous_regSol hac)
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun s => (hasDerivAt_regSol hac s).differentiableAt, by simp, ?_⟩
    rw [deriv_regSol hac]
    exact (contDiff_avgPow n 2 ((contDiff_infty.1 ha n).mul ih)).div_const 4

/-- **The regular equation** `4(s b'' + 3 b') = a b` on all of `ℝ`. -/
theorem regSol_ode {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (s : ℝ) :
    4 * ((s : ℂ) * deriv (deriv (regSol a)) s + 3 * deriv (regSol a) s) = a s * regSol a s := by
  have hac := ha.continuous
  have hg : ContDiff ℝ ∞ fun σ => a σ * regSol a σ := ha.mul (contDiff_regSol ha)
  have hg1 : ContDiff ℝ 1 fun σ => a σ * regSol a σ := hg.of_le (by exact_mod_cast le_top)
  have hd1 := deriv_regSol hac
  have hd2 : deriv (deriv (regSol a)) s =
      avgPow 3 (deriv fun σ => a σ * regSol a σ) s / 4 := by
    rw [hd1]
    exact ((hasDerivAt_avgPow 2 hg1 s).div_const 4).deriv
  rw [hd2, hd1]
  have hid := avgPow_identity hg1 s
  rw [← hid]
  ring

/-- **O12** (scoping `exists_regular_analytic`, bypass B4; tex lines 1159--1168, unit B0053),
real-variable global form: for a smooth coefficient `a`, the equation `4(s b'' + 3 b') = a b`
has a smooth solution on `ℝ` with `b(0) = 1`. -/
theorem exists_regular_solution {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) :
    ∃ b : ℝ → ℂ, ContDiff ℝ ∞ b ∧ b 0 = 1 ∧
      ∀ s : ℝ, 4 * ((s : ℂ) * deriv (deriv b) s + 3 * deriv b s) = a s * b s :=
  ⟨regSol a, contDiff_regSol ha, regSol_zero ha.continuous, regSol_ode ha⟩

end UnforcedLeray.ComplexODEC
