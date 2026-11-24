import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6_axis

/-!
# `PartIII-b:C/rep/8/2/pres/6/axis/3`: the ring lift has a limit at the axis (`axisEvNvLimit`)

Source `the November 2 reference manuscript`:
lines 1205-1235 and 1310-1323 (smoothness through the axis).

Off the axis, `N_v b(τ, y') = √s (b₀ e_r + b₁ e₃)` at the chart point of `y'`, where
`s = R²/ϱ(y')²`, `√s = R/ϱ(y')` and `η = R y'₃/ϱ(y') = √s · y'₃` (`Lib/Axisymmetric/RingChart.lean`).
Near `y ∈ axis` the age `s` is large, so `√s b₀ → 0` and `√s b₁ → g(y₃)` (`AxisEvDecay`), while
`e_r` is a unit vector and the axial coordinate `y'₃` is continuous. Hence `N_v b → g(y₃) e₃`.

Route: `Metric.tendsto_nhdsWithin_nhds`; the three error terms are each bounded by `e/4`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace AxisEvNv

/-- A real `a` with `a² ≤ n²` and `n ≥ 0` satisfies `|a| ≤ n`. -/
theorem abs_le_of_sq_le {a n : ℝ} (hn : 0 ≤ n) (h : a ^ 2 ≤ n ^ 2) : |a| ≤ n := by
  nlinarith [sq_abs a, abs_nonneg a]

end AxisEvNv

/-- **`PartIII-b:C/rep/8/2/pres/6/axis/3`: the ring lift has a limit at the axis** (geometry;
source 1205-1235, 1310-1323): `N_v b(τ, ·) → g(y₃) e₃` at each axis point `y`, from off the axis. -/
theorem axisEvNvLimit : AxisEvNvLimit := by
  intro R b g hR hd τ y hy
  obtain ⟨hg, h0, h1⟩ := hd
  have hy0 : y 0 = 0 := hy.1
  have hy1 : y 1 = 0 := hy.2
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  obtain ⟨S0, hS0⟩ := h0 (e / 4) (by linarith)
  obtain ⟨S1, hS1⟩ := h1 (e / 4) (by linarith)
  obtain ⟨dg, hdg, hgd⟩ := Metric.continuous_iff.1 hg (y 2) (e / 4) (by linarith)
  set S : ℝ := max (max S0 S1) 1 with hSdef
  have hSS0 : S0 ≤ S := by
    rw [hSdef]
    exact le_trans (le_max_left S0 S1) (le_max_left _ 1)
  have hSS1 : S1 ≤ S := by
    rw [hSdef]
    exact le_trans (le_max_right S0 S1) (le_max_left _ 1)
  have hS1' : 1 ≤ S := by
    rw [hSdef]
    exact le_max_right _ _
  have hSpos : 0 < Real.sqrt S := Real.sqrt_pos.2 (by linarith)
  refine ⟨min dg (R / Real.sqrt S), lt_min hdg (div_pos hR hSpos), ?_⟩
  intro y' hy' hdist
  have hn : ‖y' - y‖ < R / Real.sqrt S := by
    rw [dist_eq_norm] at hdist
    exact lt_of_lt_of_le hdist (min_le_right _ _)
  have hn2 : ‖y' - y‖ < dg := by
    rw [dist_eq_norm] at hdist
    exact lt_of_lt_of_le hdist (min_le_left _ _)
  have hϱpos : 0 < ϱ y' := ϱ_pos hy'
  -- `ϱ(y') ≤ ‖y' - y‖` and `|y'₃ - y₃| ≤ ‖y' - y‖`
  have hsq : ϱ y' ^ 2 ≤ ‖y' - y‖ ^ 2 := by
    have hid := norm_sq_eq_ϱ_sq_add (y' - y)
    have hϱ : ϱ (y' - y) ^ 2 = ϱ y' ^ 2 := by
      rw [ϱ_sq, ϱ_sq]
      simp [hy0, hy1]
    have hnn : 0 ≤ (y' - y) 2 ^ 2 := sq_nonneg _
    rw [hid, hϱ]
    linarith
  have hϱle : ϱ y' ≤ ‖y' - y‖ := by
    have h := AxisEvNv.abs_le_of_sq_le (norm_nonneg (y' - y)) hsq
    rwa [abs_of_nonneg (ϱ_nonneg y')] at h
  have hcoord : |y' 2 - y 2| ≤ ‖y' - y‖ := by
    have hid := norm_sq_eq_ϱ_sq_add (y' - y)
    have hϱ0 : 0 ≤ ϱ (y' - y) ^ 2 := sq_nonneg _
    have e2 : (y' - y) 2 = y' 2 - y 2 := by simp
    have h2 : (y' 2 - y 2) ^ 2 ≤ ‖y' - y‖ ^ 2 := by
      rw [← e2, hid]
      linarith
    exact AxisEvNv.abs_le_of_sq_le (norm_nonneg _) h2
  -- the age is at least `S`, and `√s = R/ϱ`, `η = √s · y'₃`
  have hs_ge : S ≤ age R y' := by
    have hA : ϱ y' * Real.sqrt S < R := (lt_div_iff₀ hSpos).1 (lt_of_le_of_lt hϱle hn)
    have hB : (ϱ y' * Real.sqrt S) ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hϱpos.le (Real.sqrt_nonneg _)) hA.le 2
    have hC : (ϱ y' * Real.sqrt S) ^ 2 = ϱ y' ^ 2 * S := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
    unfold age
    rw [le_div_iff₀ (pow_pos hϱpos 2), mul_comm]
    linarith [hB, hC]
  have hsqrt : Real.sqrt (age R y') = R / ϱ y' := by
    unfold age
    rw [show R ^ 2 / ϱ y' ^ 2 = (R / ϱ y') ^ 2 by rw [div_pow],
      Real.sqrt_sq (div_nonneg hR.le hϱpos.le)]
  have htrans : UnforcedLeray.Axi.trans R y' = Real.sqrt (age R y') * y' 2 := by
    rw [hsqrt]
    unfold UnforcedLeray.Axi.trans
    ring
  -- the two decay estimates at the chart point of `y'`
  have hB0 : Real.sqrt (age R y') * |b (chart R τ y') 0| ≤ e / 4 :=
    hS0 (age R y') (hSS0.trans hs_ge) (phase R τ y') (UnforcedLeray.Axi.trans R y')
  have hB1 : |Real.sqrt (age R y') * b (chart R τ y') 1 - g (y' 2)| ≤ e / 4 := by
    have h := hS1 (age R y') (hSS1.trans hs_ge) (phase R τ y') (y' 2)
    rw [← htrans] at h
    exact h
  have hgY : |g (y' 2) - g (y 2)| ≤ e / 4 := by
    have hd2 : dist (y' 2) (y 2) < dg := by
      rw [Real.dist_eq]
      linarith [hcoord, hn2]
    have h := hgd (y' 2) hd2
    rw [Real.dist_eq] at h
    exact h.le
  -- the decomposition of `N_v b - g(y₃) e₃`
  have hdec : Nv R b τ y' - g (y 2) • e3 =
      (Real.sqrt (age R y') * b (chart R τ y') 0) • eR y' +
        ((Real.sqrt (age R y') * b (chart R τ y') 1 - g (y' 2)) + (g (y' 2) - g (y 2))) • e3 := by
    unfold Nv
    rw [frameL_apply]
    module
  have hreR : ‖eR y'‖ = 1 := norm_eR hy'
  have he3 : ‖e3‖ = 1 := by
    simp [e3, coordinateVector]
  have hm : |Real.sqrt (age R y') * b (chart R τ y') 0| =
      Real.sqrt (age R y') * |b (chart R τ y') 0| := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hab := abs_add_le (Real.sqrt (age R y') * b (chart R τ y') 1 - g (y' 2))
    (g (y' 2) - g (y 2))
  rw [dist_eq_norm, hdec]
  calc ‖(Real.sqrt (age R y') * b (chart R τ y') 0) • eR y' +
        ((Real.sqrt (age R y') * b (chart R τ y') 1 - g (y' 2)) + (g (y' 2) - g (y 2))) • e3‖
      ≤ ‖(Real.sqrt (age R y') * b (chart R τ y') 0) • eR y'‖ +
        ‖((Real.sqrt (age R y') * b (chart R τ y') 1 - g (y' 2)) + (g (y' 2) - g (y 2))) • e3‖ :=
        norm_add_le _ _
    _ = |Real.sqrt (age R y') * b (chart R τ y') 0| +
        |(Real.sqrt (age R y') * b (chart R τ y') 1 - g (y' 2)) + (g (y' 2) - g (y 2))| := by
        rw [norm_smul, norm_smul, hreR, he3, Real.norm_eq_abs, Real.norm_eq_abs]
        ring
    _ < e := by linarith [hab, hB0, hB1, hgY, hm]

end UnforcedLeray.Short.PartIIIb.Concrete
