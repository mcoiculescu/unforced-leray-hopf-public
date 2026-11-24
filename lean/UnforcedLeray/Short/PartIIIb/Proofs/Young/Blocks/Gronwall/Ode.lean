import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Auxiliary one-dimensional estimates for the block Gronwall step (source 4396-4406)

Helpers for `blockGronwall_holds`: a monotonicity criterion from a derivative sign, the two
exponential-kernel integral bounds, and the integral Gronwall inequality.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.BlockGronwallAux

/-- A function with nonpositive derivative on `(t, T)` and continuous on `[t, T]` does not
increase: `f s ≤ f t` on `[t, T]`. -/
theorem le_start_of_deriv_nonpos {t T : ℝ} {f f' : ℝ → ℝ}
    (hc : ContinuousOn f (Icc t T))
    (hd : ∀ x ∈ Ioo t T, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Ioo t T, f' x ≤ 0) :
    ∀ s ∈ Icc t T, f s ≤ f t := by
  intro s hs
  have hT : t ≤ T := le_trans hs.1 hs.2
  have hanti : AntitoneOn f (Icc t T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t T) hc
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x hx).deriv]
      exact hn x hx
  exact hanti ⟨le_rfl, hT⟩ hs hs.1

/-- Interval integrability of a function continuous on `[t, T]`, on `[t, s]` for `s ∈ [t, T]`. -/
theorem intervalIntegrable_of_cont {X : ℝ → ℝ} {t T s : ℝ} (hX : ContinuousOn X (Icc t T))
    (hs : s ∈ Icc t T) : IntervalIntegrable X volume t s := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hs.1]
  exact hX.mono (Set.Icc_subset_Icc le_rfl hs.2)

/-- `∫_t^s exp(-g(s-u)) du ≤ 1/g`. -/
theorem integral_exp_neg_sub_le {g t s : ℝ} (hg : 0 < g) (hts : t ≤ s) :
    ∫ u in t..s, Real.exp (-g * (s - u)) ≤ 1 / g := by
  have hd : ∀ x ∈ uIcc t s,
      HasDerivAt (fun y => (1 / g) * Real.exp (-g * (s - y))) (Real.exp (-g * (s - x))) x := by
    intro x _
    have h0 : HasDerivAt (fun y => s - y) (-1) x := (hasDerivAt_id' x).const_sub s
    have h1 := h0.const_mul (-g)
    have h2 := (h1.exp).const_mul (1 / g)
    refine HasDerivAt.congr_deriv h2 ?_
    have hg0 : g ≠ 0 := hg.ne'
    field_simp <;> ring
  have hint : IntervalIntegrable (fun u => Real.exp (-g * (s - u))) volume t s := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  have hpos : 0 < Real.exp (-g * (s - t)) := Real.exp_pos _
  have hg1 : 0 < 1 / g := by positivity
  simp only [sub_self, mul_zero, Real.exp_zero]
  nlinarith [mul_pos hg1 hpos]

/-- `∫_t^s exp(-g(u-t)) du ≤ 1/g`. -/
theorem integral_exp_neg_start_le {g t s : ℝ} (hg : 0 < g) (hts : t ≤ s) :
    ∫ u in t..s, Real.exp (-g * (u - t)) ≤ 1 / g := by
  have hd : ∀ x ∈ uIcc t s,
      HasDerivAt (fun y => -(1 / g) * Real.exp (-g * (y - t))) (Real.exp (-g * (x - t))) x := by
    intro x _
    have h1 := ((hasDerivAt_id' x).sub_const t).const_mul (-g)
    have h2 := (h1.exp).const_mul (-(1 / g))
    refine HasDerivAt.congr_deriv h2 ?_
    have hg0 : g ≠ 0 := hg.ne'
    field_simp <;> ring
  have hint : IntervalIntegrable (fun u => Real.exp (-g * (u - t))) volume t s := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  have hpos : 0 < Real.exp (-g * (s - t)) := Real.exp_pos _
  have hg1 : 0 < 1 / g := by positivity
  simp only [sub_self, mul_zero, Real.exp_zero]
  nlinarith [mul_pos hg1 hpos]

/-- Integral Gronwall inequality: if `X ≤ A + c ∫_t^· X` on `[t, T]` with `A, c ≥ 0`, then
`X s ≤ A + c A (s - t) e^{c(s-t)}`. -/
theorem gronwall_int {t T A c : ℝ} {X : ℝ → ℝ}
    (hX : ContinuousOn X (Icc t T)) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hb : ∀ s ∈ Icc t T, X s ≤ A + c * ∫ r in t..s, X r) :
    ∀ s ∈ Icc t T, X s ≤ A + c * (A * (s - t) * Real.exp (c * (s - t))) := by
  intro s hs
  have hT : t ≤ T := le_trans hs.1 hs.2
  have hXT : IntervalIntegrable X volume t T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact hX
  have hvc : ContinuousOn (fun u => ∫ r in t..u, X r) (Icc t T) := by
    have := intervalIntegral.continuousOn_primitive_interval' hXT (Set.left_mem_uIcc)
    rw [Set.uIcc_of_le hT] at this
    exact this
  have hcont : ContinuousOn
      (fun u => (∫ r in t..u, X r) * Real.exp (-c * (u - t)) - A * (u - t)) (Icc t T) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.mul hvc
      exact Continuous.continuousOn (by fun_prop)
    · exact Continuous.continuousOn (by fun_prop)
  have hder : ∀ x ∈ Ioo t T, HasDerivAt
      (fun u => (∫ r in t..u, X r) * Real.exp (-c * (u - t)) - A * (u - t))
      (X x * Real.exp (-c * (x - t)) + (∫ r in t..x, X r) * (Real.exp (-c * (x - t)) * (-c * 1))
        - A * 1) x := by
    intro x hx
    have hxI : x ∈ Icc t T := Ioo_subset_Icc_self hx
    have hXc : ContinuousAt X x := hX.continuousAt (Icc_mem_nhds hx.1 hx.2)
    have hXm : StronglyMeasurableAtFilter X (nhds x) volume :=
      (hX.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
    have hvd : HasDerivAt (fun u => ∫ r in t..u, X r) (X x) x :=
      intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_of_cont hX hxI) hXm hXc
    have hed : HasDerivAt (fun u => Real.exp (-c * (u - t)))
        (Real.exp (-c * (x - t)) * (-c * 1)) x :=
      (((hasDerivAt_id' x).sub_const t).const_mul (-c)).exp
    have hlin : HasDerivAt (fun u => A * (u - t)) (A * 1) x :=
      ((hasDerivAt_id' x).sub_const t).const_mul A
    exact (hvd.mul hed).sub hlin
  have hstart : (∫ r in t..t, X r) * Real.exp (-c * (t - t)) - A * (t - t) = 0 := by
    simp
  have hmono := le_start_of_deriv_nonpos hcont hder ?_ s hs
  · rw [hstart] at hmono
    -- `hmono : v s e(s) - A (s - t) ≤ 0`
    have hsT : t ≤ s := hs.1
    have hE : Real.exp (-c * (s - t)) * Real.exp (c * (s - t)) = 1 := by
      rw [← Real.exp_add, show -c * (s - t) + c * (s - t) = 0 by ring, Real.exp_zero]
    have hv : (∫ r in t..s, X r) ≤ A * (s - t) * Real.exp (c * (s - t)) := by
      have h1 := mul_le_mul_of_nonneg_right
        (show (∫ r in t..s, X r) * Real.exp (-c * (s - t)) ≤ A * (s - t) by linarith)
        (Real.exp_pos (c * (s - t))).le
      calc (∫ r in t..s, X r)
          = (∫ r in t..s, X r) * Real.exp (-c * (s - t)) * Real.exp (c * (s - t)) := by
            rw [mul_assoc, hE, mul_one]
        _ ≤ A * (s - t) * Real.exp (c * (s - t)) := h1
    have h2 := mul_le_mul_of_nonneg_left (hb s hs) (le_refl (0:ℝ))
    have h3 := mul_le_mul_of_nonneg_left hv hc
    linarith [hb s hs, h3]
  · intro x hx
    have hxI : x ∈ Icc t T := Ioo_subset_Icc_self hx
    have hbx := hb x hxI
    have hx0 : 0 ≤ x - t := by linarith [hx.1]
    have he0 : 0 ≤ Real.exp (-c * (x - t)) := (Real.exp_pos _).le
    have he1 : Real.exp (-c * (x - t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    have h1 := mul_le_mul_of_nonneg_right hbx he0
    nlinarith [mul_nonneg hA (sub_nonneg.2 he1)]

end UnforcedLeray.Short.PartIIIb.BlockGronwallAux
