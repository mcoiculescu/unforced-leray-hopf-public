import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# Real-number bookkeeping for the ring-lift jets

Source `the November 2 reference manuscript`
lines 2360-2366, 2385-2387.  Pure arithmetic: Leibniz sums with the `t`-weights.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem arith_jets (α π a R Cm t W u0 u1 u2 v0 v1 v2 w0 w1 w2 g0 g1 g2 n1 n2 : ℝ)
    (hα : 0 ≤ α) (hπ : 0 ≤ π) (ha : 1 ≤ a) (hR : 0 < R) (hCm : 0 ≤ Cm) (ht : 0 ≤ t)
    (hW : 1 ≤ W)
    (hu0 : u0 ≤ α * R * t) (hu1 : u1 ≤ α * R * t ^ 2) (hu2 : u2 ≤ α * R * t ^ 3)
    (hu0n : 0 ≤ u0) (hu1n : 0 ≤ u1) (hu2n : 0 ≤ u2)
    (hv0 : v0 ≤ π) (hv1 : v1 ≤ π * t) (hv2 : v2 ≤ π * t ^ 2)
    (hv0n : 0 ≤ v0) (hv1n : 0 ≤ v1) (hv2n : 0 ≤ v2)
    (hw0 : w0 ≤ Cm) (hw1 : w1 ≤ Cm * (a * t * W)) (hw2 : w2 ≤ 2 * Cm * (a * t * W) ^ 2)
    (hw0n : 0 ≤ w0) (hw1n : 0 ≤ w1) (hw2n : 0 ≤ w2)
    (hg0 : g0 ≤ v0 * w0) (hg1 : g1 ≤ v0 * w1 + v1 * w0)
    (hg2 : g2 ≤ v0 * w2 + 2 * (v1 * w1) + v2 * w0)
    (hg0n : 0 ≤ g0) (hg1n : 0 ≤ g1) (hg2n : 0 ≤ g2)
    (hn1 : n1 ≤ u0 * g1 + u1 * g0) (hn2 : n2 ≤ u0 * g2 + 2 * (u1 * g1) + u2 * g0) :
    n1 ≤ (10 * α * π * a ^ 2 * R) * Cm * t ^ 2 * W ∧
    n2 ≤ (10 * α * π * a ^ 2 * R) * Cm * t ^ 3 * W ^ 2 := by
  have hm : 1 ≤ a * W := one_le_mul_of_one_le_of_one_le ha hW
  set m : ℝ := a * W with hmdef
  have hm0 : 0 ≤ m := by linarith
  have hX : 0 ≤ π * Cm * t := by positivity
  have hX2 : 0 ≤ π * Cm * t ^ 2 := by positivity
  have hg0' : g0 ≤ π * Cm := hg0.trans (mul_le_mul hv0 hw0 hw0n hπ)
  have hg1' : g1 ≤ 2 * (π * Cm * t) * m := by
    calc g1 ≤ v0 * w1 + v1 * w0 := hg1
      _ ≤ π * (Cm * (a * t * W)) + (π * t) * Cm :=
        add_le_add (mul_le_mul hv0 hw1 hw1n hπ) (mul_le_mul hv1 hw0 hw0n (by positivity))
      _ = (π * Cm * t) * (m + 1) := by rw [hmdef]; ring
      _ ≤ 2 * (π * Cm * t) * m := by nlinarith [mul_nonneg hX (sub_nonneg.2 hm)]
  have hg2' : g2 ≤ 5 * (π * Cm * t ^ 2) * m ^ 2 := by
    calc g2 ≤ v0 * w2 + 2 * (v1 * w1) + v2 * w0 := hg2
      _ ≤ π * (2 * Cm * (a * t * W) ^ 2) + 2 * ((π * t) * (Cm * (a * t * W))) +
            (π * t ^ 2) * Cm := by
        gcongr
      _ = (π * Cm * t ^ 2) * (2 * m ^ 2 + 2 * m + 1) := by rw [hmdef]; ring
      _ ≤ 5 * (π * Cm * t ^ 2) * m ^ 2 := by
        nlinarith [mul_nonneg hX2 (mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hm)),
          mul_nonneg hX2 (sub_nonneg.2 hm)]
  have hY : 0 ≤ α * π * R * Cm * t ^ 2 := by positivity
  have hZ : 0 ≤ α * π * R * Cm * t ^ 3 := by positivity
  constructor
  · calc n1 ≤ u0 * g1 + u1 * g0 := hn1
      _ ≤ (α * R * t) * (2 * (π * Cm * t) * m) + (α * R * t ^ 2) * (π * Cm) :=
        add_le_add (mul_le_mul hu0 hg1' hg1n (by positivity)) (mul_le_mul hu1 hg0' hg0n (by positivity))
      _ = (α * π * R * Cm * t ^ 2) * (2 * m + 1) := by ring
      _ ≤ (α * π * R * Cm * t ^ 2) * (10 * a ^ 2 * W) := by
        refine mul_le_mul_of_nonneg_left ?_ hY
        have h1 : a ≤ a ^ 2 := le_self_pow₀ ha (by norm_num)
        have e1 : m ≤ a ^ 2 * W := by
          rw [hmdef]; exact mul_le_mul_of_nonneg_right h1 (by linarith)
        linarith
      _ = (10 * α * π * a ^ 2 * R) * Cm * t ^ 2 * W := by ring
  · calc n2 ≤ u0 * g2 + 2 * (u1 * g1) + u2 * g0 := hn2
      _ ≤ (α * R * t) * (5 * (π * Cm * t ^ 2) * m ^ 2) +
            2 * ((α * R * t ^ 2) * (2 * (π * Cm * t) * m)) + (α * R * t ^ 3) * (π * Cm) := by
        gcongr
      _ = (α * π * R * Cm * t ^ 3) * (5 * m ^ 2 + 4 * m + 1) := by ring
      _ ≤ (α * π * R * Cm * t ^ 3) * (10 * (a ^ 2 * W ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hZ
        have e : a ^ 2 * W ^ 2 = m ^ 2 := by rw [hmdef]; ring
        have h1 : 1 ≤ m ^ 2 := one_le_pow₀ hm
        have h2 : m ≤ m ^ 2 := le_self_pow₀ hm (by norm_num)
        rw [e]
        linarith
      _ = (10 * α * π * a ^ 2 * R) * Cm * t ^ 3 * W ^ 2 := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
