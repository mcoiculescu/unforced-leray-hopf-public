import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_14
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!


Route: split `n` into even `n = 2k` (where `Γ(k+1) = k!`) and odd `n = 2k+1` (where
`Γ(k+3/2) ≥ k!/2`, by monotonicity of `Γ` on `[2, ∞)` and `Γ(3/2) ≥ 1/2`), then
`Summable.even_add_odd`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

/-- `Γ(k + 3/2) ≥ k!/2` for every `k : ℕ`. -/
theorem gammaSeries_odd_lower (k : ℕ) :
    ((k.factorial : ℕ) : ℝ) / 2 ≤ Real.Gamma ((k : ℝ) + 3 / 2) := by
  rcases k with _ | m
  · have h32 : Real.Gamma (3 / 2 : ℝ) = 1 / 2 * Real.Gamma (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
    rw [Real.Gamma_one_half_eq] at h32
    have hs : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_nonneg
    have hs0 : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
    have hs1 : 1 ≤ Real.sqrt Real.pi := by nlinarith [Real.pi_gt_three]
    simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, zero_add]
    rw [h32]
    nlinarith
  · have hm1 : ((m + 1 : ℕ) : ℝ) + 1 ∈ Set.Ici (2 : ℝ) := by
      simp only [Set.mem_Ici]
      push_cast
      have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      linarith
    have hm2 : ((m + 1 : ℕ) : ℝ) + 3 / 2 ∈ Set.Ici (2 : ℝ) := by
      simp only [Set.mem_Ici]
      push_cast
      have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      linarith
    have hmono : Real.Gamma (((m + 1 : ℕ) : ℝ) + 1) ≤ Real.Gamma (((m + 1 : ℕ) : ℝ) + 3 / 2) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn hm1 hm2 (by
        have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
        push_cast
        linarith)
    rw [Real.Gamma_nat_eq_factorial] at hmono
    have hf : (0 : ℝ) ≤ ((m + 1).factorial : ℝ) := Nat.cast_nonneg _
    linarith

theorem gammaSeries_even_eq (q : ℝ) (k : ℕ) :
    q ^ (2 * k) / Real.Gamma (((2 * k : ℕ) : ℝ) / 2 + 1) = (q ^ 2) ^ k / ((k.factorial : ℕ) : ℝ) := by
  rw [show (((2 * k : ℕ) : ℝ)) / 2 + 1 = (k : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial, pow_mul]

theorem gammaSeries_odd_le (q : ℝ) (hq : 0 ≤ q) (k : ℕ) :
    q ^ (2 * k + 1) / Real.Gamma (((2 * k + 1 : ℕ) : ℝ) / 2 + 1) ≤
      2 * q * ((q ^ 2) ^ k / ((k.factorial : ℕ) : ℝ)) := by
  have hcast : (((2 * k + 1 : ℕ) : ℝ)) / 2 + 1 = (k : ℝ) + 3 / 2 := by push_cast; ring
  rw [hcast]
  have hG := gammaSeries_odd_lower k
  have hfac : (0 : ℝ) < ((k.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hGpos : 0 < Real.Gamma ((k : ℝ) + 3 / 2) := by linarith
  have hP : 0 ≤ q * (q ^ 2) ^ k := by positivity
  have hkey : q ^ (2 * k + 1) = q * (q ^ 2) ^ k := by
    rw [pow_succ, pow_mul]; ring
  rw [← mul_div_assoc, div_le_div_iff₀ hGpos hfac, hkey]
  have := mul_le_mul_of_nonneg_left hG hP
  nlinarith [this]

/-- **`PartII-b:T22/1/14/7`**: `∑ a q^n / Γ(n/2+1)` converges for `q ≥ 0`. -/
theorem gammaSeriesSummable_proof : UnforcedLeray.Short.IIb.CylPDE.GammaSeriesSummable := by
  intro a q hq
  have hE : Summable (fun k : ℕ => (q ^ 2) ^ k / ((k.factorial : ℕ) : ℝ)) :=
    Real.summable_pow_div_factorial (q ^ 2)
  have hO : Summable (fun k : ℕ => 2 * q * ((q ^ 2) ^ k / ((k.factorial : ℕ) : ℝ))) :=
    hE.mul_left (2 * q)
  have hEv : Summable (fun k : ℕ => q ^ (2 * k) / Real.Gamma (((2 * k : ℕ) : ℝ) / 2 + 1)) :=
    hE.congr (fun k => (gammaSeries_even_eq q k).symm)
  have hOd : Summable (fun k : ℕ => q ^ (2 * k + 1) / Real.Gamma (((2 * k + 1 : ℕ) : ℝ) / 2 + 1)) :=
    Summable.of_nonneg_of_le (fun k => by
        have : (0 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) / 2 + 1 := by positivity
        exact div_nonneg (pow_nonneg hq _) (Real.Gamma_pos_of_pos (by positivity)).le)
      (fun k => gammaSeries_odd_le q hq k) hO
  have hall : Summable (fun n : ℕ => q ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) :=
    Summable.even_add_odd hEv hOd
  exact (hall.mul_left a).congr (fun n => by ring)

end CylPDE

end UnforcedLeray.Short.IIb
