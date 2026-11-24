import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.Order.Group

/-!
# Monotonicity and homogeneity of `phaseLr` (task `PartIII-b:C/rep/8/2/pres/4/2/lp/4/2`)

Source `the November 2 reference manuscript` 5134-5139.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise domination of `phaseLr` by a scalar multiple of `phaseLr` of the dominating density. -/
theorem phaseLr_mono_smul {P r k : ℝ} (hr : 0 < r) (hk : 0 ≤ k) {F G : ℝ × Space → ℝ} (h : ∀ x, |F x| ≤ k * |G x|) : phaseLr P r F ≤ ENNReal.ofReal k * phaseLr P r G := by
  have hr0 : 0 ≤ r := hr.le
  have hinv : 0 ≤ 1 / r := one_div_nonneg.mpr hr0
  have hne : ENNReal.ofReal k ^ r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0 ENNReal.ofReal_ne_top
  -- pointwise bound on the integrand
  have hpt : ∀ x : ℝ × Space, ENNReal.ofReal |F x| ^ r ≤
      ENNReal.ofReal k ^ r * ENNReal.ofReal |G x| ^ r := by
    intro x
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hr0, ← ENNReal.ofReal_mul hk]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (h x)) hr0
  -- inner integral
  have hin : ∀ t : ℝ, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ r ≤
      ENNReal.ofReal k ^ r * ∫⁻ y : Space, ENNReal.ofReal |G (t, y)| ^ r := by
    intro t
    rw [← lintegral_const_mul' _ _ hne]
    exact lintegral_mono (fun y => hpt (t, y))
  -- outer integral
  have hout : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ r ≤
      ∫⁻ t in Ioc (0 : ℝ) P, ENNReal.ofReal k ^ r * ∫⁻ y : Space, ENNReal.ofReal |G (t, y)| ^ r :=
    lintegral_mono hin
  rw [lintegral_const_mul' _ _ hne] at hout
  have hroot : (ENNReal.ofReal k ^ r) ^ (1 / r) = ENNReal.ofReal k := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]
  unfold phaseLr
  have hle : ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ r ≤
      ENNReal.ofReal k ^ r * (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |G (t, y)| ^ r) := by
    calc ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ r
        ≤ ENNReal.ofReal P⁻¹ * (ENNReal.ofReal k ^ r * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |G (t, y)| ^ r) :=
          mul_le_mul_of_nonneg_left hout (by positivity)
      _ = ENNReal.ofReal k ^ r * (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |G (t, y)| ^ r) := by
          rw [mul_left_comm]
  calc (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |F (t, y)| ^ r) ^ (1 / r)
      ≤ (ENNReal.ofReal k ^ r * (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |G (t, y)| ^ r)) ^ (1 / r) :=
        ENNReal.rpow_le_rpow hle hinv
    _ = (ENNReal.ofReal k ^ r) ^ (1 / r) * (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |G (t, y)| ^ r) ^ (1 / r) :=
        ENNReal.mul_rpow_of_nonneg _ _ hinv
    _ = ENNReal.ofReal k * (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ENNReal.ofReal |G (t, y)| ^ r) ^ (1 / r) := by
        rw [hroot]

end UnforcedLeray.Short.PartIIIb.Concrete
