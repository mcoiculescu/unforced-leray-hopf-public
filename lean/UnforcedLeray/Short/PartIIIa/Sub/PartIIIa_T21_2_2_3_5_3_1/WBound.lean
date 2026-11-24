import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R1.WtBound

/-!
# `PartIII-a:T21/2/2/3/5/3/1`, leaf `PhysWBound` (calculus of the weight)

`physW(r', x) = a(r')³ wtPhys(r', x)` (`a = a(r') > 0`), where `wtPhys = a⁻³ physW` is the weight of
the `E_0` energy with the compiled bound `E0.wtPhysBound`. On a ball where also
`a(r)/2 ≤ a(r') ≤ 3a(r)/2`, the product rule and that bound give the bounds of `physW` and of
its `r`-derivative by `physW(r)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

theorem physW_eq_mul_wtPhys (ν c m q : ℝ) (x : ℝ × ℝ) (hq : 0 < clockA ν q) :
    physW ν c m q x = clockA ν q ^ 3 * E0.wtPhys ν c m q x := by
  unfold physW E0.wtPhys
  have h3 : clockA ν q ^ 3 ≠ 0 := pow_ne_zero 3 hq.ne'
  rw [← mul_assoc, mul_inv_cancel₀ h3, one_mul]

/-- **`PhysWBound`**: local uniform bounds of `physW` and its `r`-derivative. -/
theorem physWBound (m : ℝ) : PhysWBound m := by
  intro ν c r hc ha
  obtain ⟨C, δ, hC0, hδ, hb⟩ := E0.wtPhysBound m ν c r hc ha
  have hε : 0 < clockA ν r / (2 * (|ν| + 1)) := div_pos ha (by positivity)
  refine ⟨C * (4 + 7 * |ν| / clockA ν r), min δ (clockA ν r / (2 * (|ν| + 1))),
    by positivity, lt_min hδ hε, ?_⟩
  intro x r' hr'
  have hr'δ : r' ∈ ball r δ := ball_subset_ball (min_le_left _ _) hr'
  obtain ⟨hdiff, hnn, hle, hder⟩ := hb x r' hr'δ
  have hr'2 : dist r' r < clockA ν r / (2 * (|ν| + 1)) :=
    lt_of_lt_of_le (mem_ball.mp hr') (min_le_right _ _)
  rw [Real.dist_eq] at hr'2
  have hclose : |clockA ν r' - clockA ν r| ≤ clockA ν r / 2 := by
    have e : clockA ν r' - clockA ν r = ν * (r' - r) := by unfold clockA; ring
    rw [e, abs_mul]
    have hmul : |ν| * |r' - r| ≤ (|ν| + 1) * (clockA ν r / (2 * (|ν| + 1))) :=
      mul_le_mul (by linarith [abs_nonneg ν]) hr'2.le (abs_nonneg _) (by positivity)
    have e2 : (|ν| + 1) * (clockA ν r / (2 * (|ν| + 1))) = clockA ν r / 2 := by
      field_simp
    linarith
  have ha'lo : clockA ν r / 2 ≤ clockA ν r' := by linarith [(abs_le.mp hclose).1]
  have ha'hi : clockA ν r' ≤ 3 * clockA ν r / 2 := by linarith [(abs_le.mp hclose).2]
  have ha' : 0 < clockA ν r' := by linarith
  have hcont : Continuous (fun q => clockA ν q) := by unfold clockA; fun_prop
  have hev : (fun q => physW ν c m q x) =ᶠ[𝓝 r']
      (fun q => clockA ν q ^ 3 * E0.wtPhys ν c m q x) := by
    filter_upwards [(hcont.tendsto r').eventually (lt_mem_nhds ha')] with q hq
    exact physW_eq_mul_wtPhys ν c m q x hq
  have hA : HasDerivAt (fun q => clockA ν q) ν r' := by
    have h := ((hasDerivAt_id r').const_mul ν).const_add 1
    simpa [clockA] using h
  have hA3 : HasDerivAt (fun q => clockA ν q ^ 3) ((3 : ℕ) * clockA ν r' ^ (3 - 1) * ν) r' :=
    hA.pow 3
  have hprod : HasDerivAt (fun q => clockA ν q ^ 3 * E0.wtPhys ν c m q x)
      ((3 : ℕ) * clockA ν r' ^ (3 - 1) * ν * E0.wtPhys ν c m r' x +
        clockA ν r' ^ 3 * deriv (fun q => E0.wtPhys ν c m q x) r') r' :=
    hA3.mul hdiff.hasDerivAt
  have hD := hprod.congr_of_eventuallyEq hev
  have hw0 : 0 ≤ E0.wtPhys ν c m r x := (hb x r (mem_ball_self hδ)).2.1
  have hpr : physW ν c m r x = clockA ν r ^ 3 * E0.wtPhys ν c m r x :=
    physW_eq_mul_wtPhys ν c m r x ha
  have hpr' : physW ν c m r' x = clockA ν r' ^ 3 * E0.wtPhys ν c m r' x :=
    physW_eq_mul_wtPhys ν c m r' x ha'
  -- `a'³ ≤ (27/8) a³` and `a'² ≤ (9/4) a²`
  have hc3 : clockA ν r' ^ 3 ≤ 27 / 8 * clockA ν r ^ 3 := by
    have := pow_le_pow_left₀ ha'.le ha'hi 3
    nlinarith
  have hc2 : clockA ν r' ^ 2 ≤ 9 / 4 * clockA ν r ^ 2 := by
    have := pow_le_pow_left₀ ha'.le ha'hi 2
    nlinarith
  have hCw : 0 ≤ C * E0.wtPhys ν c m r x := mul_nonneg hC0 hw0
  refine ⟨hD.differentiableAt, ?_, ?_, ?_⟩
  · rw [hpr']
    exact mul_nonneg (pow_nonneg ha'.le 3) hnn
  · rw [hpr', hpr]
    have h1 : clockA ν r' ^ 3 * E0.wtPhys ν c m r' x ≤
        27 / 8 * clockA ν r ^ 3 * (C * E0.wtPhys ν c m r x) :=
      mul_le_mul hc3 hle hnn (by positivity)
    have h2 : 0 ≤ 7 * |ν| / clockA ν r := by positivity
    have h3 : 0 ≤ clockA ν r ^ 3 * (C * E0.wtPhys ν c m r x) := by positivity
    nlinarith
  · rw [hD.deriv, hpr]
    have e : (3 - 1 : ℕ) = 2 := rfl
    rw [e]
    push_cast
    have habs : |3 * clockA ν r' ^ 2 * ν * E0.wtPhys ν c m r' x +
        clockA ν r' ^ 3 * deriv (fun q => E0.wtPhys ν c m q x) r'| ≤
        3 * clockA ν r' ^ 2 * |ν| * E0.wtPhys ν c m r' x +
          clockA ν r' ^ 3 * |deriv (fun q => E0.wtPhys ν c m q x) r'| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hnn,
        abs_of_nonneg (pow_nonneg ha'.le 2), abs_of_nonneg (pow_nonneg ha'.le 3)]
      norm_num
    refine habs.trans ?_
    have t1 : 3 * clockA ν r' ^ 2 * |ν| * E0.wtPhys ν c m r' x ≤
        3 * (9 / 4 * clockA ν r ^ 2) * |ν| * (C * E0.wtPhys ν c m r x) := by
      have := mul_le_mul hc2 hle hnn (by positivity)
      have hν0 := abs_nonneg ν
      nlinarith
    have t2 : clockA ν r' ^ 3 * |deriv (fun q => E0.wtPhys ν c m q x) r'| ≤
        27 / 8 * clockA ν r ^ 3 * (C * E0.wtPhys ν c m r x) :=
      mul_le_mul hc3 hder (abs_nonneg _) (by positivity)
    have key : 3 * (9 / 4 * clockA ν r ^ 2) * |ν| * (C * E0.wtPhys ν c m r x) +
        27 / 8 * clockA ν r ^ 3 * (C * E0.wtPhys ν c m r x) ≤
        C * (4 + 7 * |ν| / clockA ν r) * (clockA ν r ^ 3 * E0.wtPhys ν c m r x) := by
      have e2 : C * (4 + 7 * |ν| / clockA ν r) * (clockA ν r ^ 3 * E0.wtPhys ν c m r x) =
          4 * clockA ν r ^ 3 * (C * E0.wtPhys ν c m r x) +
            7 * |ν| * clockA ν r ^ 2 * (C * E0.wtPhys ν c m r x) := by
        field_simp
      rw [e2]
      have hν0 := abs_nonneg ν
      have hp2 : 0 ≤ clockA ν r ^ 2 * (C * E0.wtPhys ν c m r x) := by positivity
      have hp3 : 0 ≤ clockA ν r ^ 3 * (C * E0.wtPhys ν c m r x) := by positivity
      nlinarith
    linarith

end UnforcedLeray.Short.IIIa.AdjE1
