import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Core differentiation of the periodized harmonic quadrupole

Helper for `HarmSummDiff` (`SummDiff.lean`) and `HarmLatticeIdent` (`LatticeIdent.lean`).
For `c > 0` and `y.2 ≠ 0`, the series `harmPeriodic c` is differentiable at `y` with derivative
`(∑' k, -2 (u_k - i y.2)⁻³) • hcL0`, where `hcL0 v = v.1 - i v.2` and `u_k = y.1 + k c`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric

namespace UnforcedLeray.Short.IIIa

/-- The real-linear map `v ↦ v.1 - i v.2`. -/
def hcL0 : (ℝ × ℝ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (v.1 : ℂ) - (v.2 : ℂ) * Complex.I
      map_add' := by
        intro a b
        simp only [Prod.fst_add, Prod.snd_add, Complex.ofReal_add]
        ring
      map_smul' := by
        intro m v
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply,
          Complex.real_smul, Complex.ofReal_mul]
        ring }

theorem hcL0_apply (v : ℝ × ℝ) : hcL0 v = (v.1 : ℂ) - (v.2 : ℂ) * Complex.I := by
  simp [hcL0]

theorem hcL0_norm_le (v : ℝ × ℝ) : ‖hcL0 v‖ ≤ 2 * ‖v‖ := by
  rw [hcL0_apply]
  have h1 : ‖(v.1 : ℂ) - (v.2 : ℂ) * Complex.I‖ ≤
      ‖(v.1 : ℂ)‖ + ‖(v.2 : ℂ) * Complex.I‖ := norm_sub_le _ _
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real] at h1
  have h2 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h3 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  linarith

theorem hcL0_opNorm_le : ‖hcL0‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound hcL0 (by norm_num) hcL0_norm_le

theorem hc_norm_sq (p η : ℝ) : ‖((p : ℂ) - (η : ℂ) * Complex.I)‖ ^ 2 = p ^ 2 + η ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.sub_im, Complex.mul_im]
  ring

theorem hc_W_eq (c : ℝ) (x : ℝ × ℝ) (k : ℤ) :
    hcL0 x + (((k : ℝ) * c : ℝ) : ℂ) =
      ((x.1 + (k : ℝ) * c : ℝ) : ℂ) - (x.2 : ℂ) * Complex.I := by
  rw [hcL0_apply]
  push_cast
  ring

theorem hc_term_eq (c : ℝ) (z : ℝ × ℝ) (k : ℤ) :
    harmTerm c z k = ((hcL0 z + (((k : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 2 := by
  rw [hc_W_eq]
  rfl

theorem hc_term_norm (c : ℝ) (y : ℝ × ℝ) (k : ℤ) :
    ‖harmTerm c y k‖ = 1 / (((k : ℝ) * c + y.1) ^ 2 + y.2 ^ 2) := by
  unfold harmTerm
  rw [norm_pow, norm_inv, inv_pow, hc_norm_sq, one_div, add_comm ((k : ℝ) * c) y.1]

/-- Summability of the shifted inverse squares `1 / ((k c + a)² + r²)` over `ℤ`. -/
theorem hc_sumShift (c : ℝ) (hc : 0 < c) (a r : ℝ) (hr : 0 < r) :
    Summable (fun k : ℤ => 1 / (((k : ℝ) * c + a) ^ 2 + r ^ 2)) := by
  have hs : Summable (fun k : ℤ => 1 / |(k : ℝ) + a / c| ^ (2 : ℝ)) :=
    (Real.summable_one_div_int_add_rpow (a / c) 2).2 (by norm_num)
  have hfin : {k : ℤ | (k : ℝ) + a / c = 0}.Finite := by
    apply Set.Subsingleton.finite
    intro x hx y hy
    have h2 : (x : ℝ) = y := by
      simp only [Set.mem_setOf_eq] at hx hy
      linarith
    exact_mod_cast h2
  apply Summable.of_norm_bounded_eventually (hs.mul_left (1 / c ^ 2))
  rw [Filter.eventually_cofinite]
  refine hfin.subset ?_
  intro k hk
  simp only [Set.mem_setOf_eq] at hk ⊢
  by_contra h0
  apply hk
  set t : ℝ := (k : ℝ) + a / c with ht
  have ht0 : t ≠ 0 := h0
  have hX : (k : ℝ) * c + a = c * t := by
    rw [ht]
    field_simp
  have hpow : |t| ^ (2 : ℝ) = t ^ 2 := by
    rw [Real.rpow_two, sq_abs]
  have hct : c * t ≠ 0 := mul_ne_zero hc.ne' ht0
  have hd : 0 < (c * t) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hct))
  rw [hpow, Real.norm_of_nonneg (by positivity), hX]
  calc 1 / ((c * t) ^ 2 + r ^ 2) ≤ 1 / (c * t) ^ 2 :=
        one_div_le_one_div_of_le hd (le_add_of_nonneg_right (sq_nonneg r))
    _ = 1 / c ^ 2 * (1 / t ^ 2) := by rw [one_div_mul_one_div, mul_pow]

/-- Summability of the terms of `harmPeriodic` at `y` with `y.2 ≠ 0`. -/
theorem hc_summable_harmTerm (c : ℝ) (hc : 0 < c) (y : ℝ × ℝ) (hy : y.2 ≠ 0) :
    Summable (harmTerm c y) := by
  have hs := hc_sumShift c hc y.1 |y.2| (abs_pos.2 hy)
  refine Summable.of_norm_bounded hs (fun k => ?_)
  rw [hc_term_norm, sq_abs]

/-- Pointwise lower bounds for the lattice variable `W = u_k - i x.2` on the ball. -/
theorem hc_w_facts (c r : ℝ) (hr : 0 < r) (y x : ℝ × ℝ) (hy2 : |y.2| = 2 * r)
    (hx : x ∈ Metric.ball y r) (k : ℤ) :
    r ≤ ‖hcL0 x + (((k : ℝ) * c : ℝ) : ℂ)‖ ∧
      ((k : ℝ) * c + y.1) ^ 2 + r ^ 2 ≤ 4 * ‖hcL0 x + (((k : ℝ) * c : ℝ) : ℂ)‖ ^ 2 := by
  have hsq : ‖hcL0 x + (((k : ℝ) * c : ℝ) : ℂ)‖ ^ 2 = (x.1 + (k : ℝ) * c) ^ 2 + x.2 ^ 2 := by
    rw [hc_W_eq]
    exact hc_norm_sq _ _
  have hd := Metric.mem_ball.mp hx
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hd
  obtain ⟨h1, h2⟩ := hd
  have hx2 : r < |x.2| := by
    have := abs_sub_abs_le_abs_sub y.2 x.2
    rw [abs_sub_comm] at this
    linarith
  have hx2sq : r ^ 2 < x.2 ^ 2 := by
    have := sq_abs x.2
    nlinarith [abs_nonneg x.2]
  have he : (x.1 - y.1) ^ 2 < r ^ 2 := by
    have := sq_abs (x.1 - y.1)
    nlinarith [abs_nonneg (x.1 - y.1)]
  have hA : ((k : ℝ) * c + y.1) ^ 2 ≤ 2 * (x.1 + (k : ℝ) * c) ^ 2 + 2 * (x.1 - y.1) ^ 2 := by
    nlinarith [sq_nonneg ((x.1 + (k : ℝ) * c) + (x.1 - y.1))]
  have hN0 : 0 ≤ ‖hcL0 x + (((k : ℝ) * c : ℝ) : ℂ)‖ := norm_nonneg _
  have hNr : r ≤ ‖hcL0 x + (((k : ℝ) * c : ℝ) : ℂ)‖ := by
    nlinarith [sq_nonneg (x.1 + (k : ℝ) * c)]
  refine ⟨hNr, ?_⟩
  nlinarith [sq_nonneg (x.1 + (k : ℝ) * c)]

/-- The coefficient of the derivative of the `k`-th term is bounded on the ball. -/
theorem hc_coef_bound (c r : ℝ) (hr : 0 < r) (y x : ℝ × ℝ) (hy2 : |y.2| = 2 * r)
    (hx : x ∈ Metric.ball y r) (k : ℤ) :
    ‖-2 * ((hcL0 x + (((k : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 3‖ ≤
      8 / r * (1 / (((k : ℝ) * c + y.1) ^ 2 + r ^ 2)) := by
  obtain ⟨h1, h2⟩ := hc_w_facts c r hr y x hy2 hx k
  set W := hcL0 x + (((k : ℝ) * c : ℝ) : ℂ) with hW
  set N := ‖W‖ with hN
  have hN0 : 0 < N := lt_of_lt_of_le hr h1
  have hprod : r * (((k : ℝ) * c + y.1) ^ 2 + r ^ 2) ≤ 4 * N ^ 3 := by
    have := mul_le_mul h1 h2 (by positivity) hN0.le
    nlinarith [this]
  have hpos : 0 < ((k : ℝ) * c + y.1) ^ 2 + r ^ 2 := by positivity
  have hnorm : ‖-2 * (W⁻¹) ^ 3‖ = 2 / N ^ 3 := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [norm_mul, norm_neg, norm_pow, norm_inv, h2, div_eq_mul_inv, inv_pow]
  rw [hnorm, show 8 / r * (1 / (((k : ℝ) * c + y.1) ^ 2 + r ^ 2)) =
      8 / (r * (((k : ℝ) * c + y.1) ^ 2 + r ^ 2)) by
    field_simp]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hprod]

/-- The derivative of the `k`-th term is bounded on the ball, uniformly in `x`. -/
theorem hc_dterm_bound (c r : ℝ) (hr : 0 < r) (y x : ℝ × ℝ) (hy2 : |y.2| = 2 * r)
    (hx : x ∈ Metric.ball y r) (k : ℤ) :
    ‖(-2 * ((hcL0 x + (((k : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 3) • hcL0‖ ≤
      16 / r * (1 / (((k : ℝ) * c + y.1) ^ 2 + r ^ 2)) := by
  have h := hc_coef_bound c r hr y x hy2 hx k
  calc ‖(-2 * ((hcL0 x + (((k : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 3) • hcL0‖
      ≤ ‖-2 * ((hcL0 x + (((k : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 3‖ * ‖hcL0‖ := norm_smul_le _ _
    _ ≤ (8 / r * (1 / (((k : ℝ) * c + y.1) ^ 2 + r ^ 2))) * 2 :=
        mul_le_mul h hcL0_opNorm_le (norm_nonneg _)
          (mul_nonneg (div_nonneg (by norm_num) hr.le) (by positivity))
    _ = 16 / r * (1 / (((k : ℝ) * c + y.1) ^ 2 + r ^ 2)) := by ring

/-- Derivative of the `k`-th term `((hcL0 z + κ)⁻¹)²` at a point where `hcL0 z + κ ≠ 0`. -/
theorem hc_hasFDerivAt_term (κ : ℂ) (z : ℝ × ℝ) (hw : hcL0 z + κ ≠ 0) :
    HasFDerivAt (fun v : ℝ × ℝ => ((hcL0 v + κ)⁻¹) ^ 2)
      ((-2 * ((hcL0 z + κ)⁻¹) ^ 3) • hcL0) z := by
  have hψ : HasFDerivAt (fun v : ℝ × ℝ => hcL0 v + κ) hcL0 z :=
    hcL0.hasFDerivAt.add_const κ
  have hF : HasDerivAt (fun w : ℂ => (w⁻¹) ^ 2) (-2 * (hcL0 z + κ)⁻¹ ^ 3) (hcL0 z + κ) :=
    ((hasDerivAt_inv hw).fun_pow' 2).congr_deriv
      (by norm_num [Finset.sum_range_succ]; generalize hcL0 z + κ = x; ring)
  have hF' := hF.hasFDerivAt.restrictScalars ℝ
  have hc := hF'.comp z hψ
  have hder : (-2 * ((hcL0 z + κ)⁻¹) ^ 3) • hcL0 =
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-2 * (hcL0 z + κ)⁻¹ ^ 3)).restrictScalars ℝ).comp
        hcL0 := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    simp
    ring
  rw [hder]
  exact hc

/-- The periodized harmonic quadrupole is differentiable at `y` with the termwise derivative. -/
theorem hc_hasFDerivAt_harmPeriodic (c : ℝ) (hc : 0 < c) (y : ℝ × ℝ) (hy : y.2 ≠ 0) :
    HasFDerivAt (harmPeriodic c)
      ((∑' k : ℤ, -2 * ((hcL0 y + (((k : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 3) • hcL0) y := by
  have hpos : 0 < |y.2| := abs_pos.2 hy
  set r : ℝ := |y.2| / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; positivity
  have hy2 : |y.2| = 2 * r := by rw [hr_def]; ring
  have hyb : y ∈ Metric.ball y r := Metric.mem_ball_self hr
  have hf : ∀ n : ℤ, ∀ x ∈ Metric.ball y r,
      HasFDerivAt (fun z : ℝ × ℝ => harmTerm c z n)
        ((-2 * ((hcL0 x + (((n : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 3) • hcL0) x := by
    intro n x hx
    have hW : hcL0 x + (((n : ℝ) * c : ℝ) : ℂ) ≠ 0 := by
      intro h0
      have := (hc_w_facts c r hr y x hy2 hx n).1
      rw [h0, norm_zero] at this
      linarith
    have heq : (fun z : ℝ × ℝ => harmTerm c z n) =
        fun z => ((hcL0 z + (((n : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 2 :=
      funext fun z => hc_term_eq c z n
    rw [heq]
    exact hc_hasFDerivAt_term _ x hW
  have hu : Summable (fun n : ℤ => 16 / r * (1 / (((n : ℝ) * c + y.1) ^ 2 + r ^ 2))) :=
    (hc_sumShift c hc y.1 r hr).mul_left (16 / r)
  have hf' : ∀ n : ℤ, ∀ x ∈ Metric.ball y r,
      ‖(-2 * ((hcL0 x + (((n : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 3) • hcL0‖ ≤
        16 / r * (1 / (((n : ℝ) * c + y.1) ^ 2 + r ^ 2)) :=
    fun n x hx => hc_dterm_bound c r hr y x hy2 hx n
  have hf0 : Summable (fun n : ℤ => harmTerm c y n) := hc_summable_harmTerm c hc y hy
  have key := hasFDerivAt_tsum_of_isPreconnected
    (f := fun (n : ℤ) (z : ℝ × ℝ) => harmTerm c z n)
    (f' := fun (n : ℤ) (x : ℝ × ℝ) => (-2 * ((hcL0 x + (((n : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 3) • hcL0)
    (s := Metric.ball y r) hu Metric.isOpen_ball (convex_ball y r).isPreconnected hf hf' hyb hf0 hyb
  have hcs : Summable (fun n : ℤ => -2 * ((hcL0 y + (((n : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 3) :=
    Summable.of_norm_bounded ((hc_sumShift c hc y.1 r hr).mul_left (8 / r))
      (fun n => hc_coef_bound c r hr y y hy2 hyb n)
  rw [← hcs.tsum_smul_const hcL0]
  exact key

end UnforcedLeray.Short.IIIa
