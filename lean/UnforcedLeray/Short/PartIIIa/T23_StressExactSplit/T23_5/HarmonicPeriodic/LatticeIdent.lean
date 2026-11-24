import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1_1
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.HarmonicPeriodic.SummDiff.Core

/-!
# Part III-a, `PartIII-a:T23/5/1/1/3`: `HarmLatticeIdent` (source 2354-2356)

Identification of the periodized quadrupole with the lattice sum `c⁻² S₂(w)`, `w = (ξ - iη)/c`,
and the derivative bound `‖DH_c(y)‖ ≤ 4 c⁻³ ‖S₃(w)‖`. The derivative formula comes from the core
lemma `hc_hasFDerivAt_harmPeriodic` (`SummDiff/Core.lean`).
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Short.IIIa

theorem harmLatticeIdent : UnforcedLeray.Short.IIIa.HarmLatticeIdent := by
  intro c hc y hy
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set w : ℂ := ((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) / (c : ℂ) with hw
  have hkey : ∀ k : ℤ, hcL0 y + (((k : ℝ) * c : ℝ) : ℂ) = (c : ℂ) * (w + (k : ℂ)) := by
    intro k
    rw [hcL0_apply, hw]
    push_cast
    field_simp
  -- part 1: the periodized quadrupole is `c⁻² S₂(w)`
  have h1 : ∀ k : ℤ, harmTerm c y k = ((c : ℂ) ^ 2)⁻¹ * ((w + (k : ℂ)) ^ 2)⁻¹ := by
    intro k
    rw [hc_term_eq, hkey k, mul_inv, mul_pow, ← inv_pow, ← inv_pow]
  have hpart1 : harmPeriodic c y = ((c : ℂ) ^ 2)⁻¹ * latticeSum 2 w := by
    unfold harmPeriodic latticeSum
    rw [← tsum_mul_left]
    exact tsum_congr h1
  -- part 2: the derivative is `(-2 c⁻³ S₃(w)) • hcL0`
  have hd := hc_hasFDerivAt_harmPeriodic c hc y hy
  rw [hd.fderiv]
  have hcoef : ∀ k : ℤ, -2 * ((hcL0 y + (((k : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 3 =
      (-2 * ((c : ℂ)⁻¹) ^ 3) * ((w + (k : ℂ)) ^ 3)⁻¹ := by
    intro k
    rw [hkey k, mul_inv, mul_pow, ← inv_pow (w + (k : ℂ))]
    ring
  have hsum : ∑' k : ℤ, -2 * ((hcL0 y + (((k : ℝ) * c : ℝ) : ℂ))⁻¹) ^ 3 =
      (-2 * ((c : ℂ)⁻¹) ^ 3) * latticeSum 3 w := by
    rw [tsum_congr hcoef]
    unfold latticeSum
    rw [tsum_mul_left]
  rw [hsum]
  have hcn : ‖(c : ℂ)⁻¹‖ = c⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hnorm_a : ‖(-2 * ((c : ℂ)⁻¹) ^ 3) * latticeSum 3 w‖ =
      2 * (c⁻¹) ^ 3 * ‖latticeSum 3 w‖ := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [norm_mul, norm_mul, norm_neg, norm_pow, hcn, h2]
  refine ⟨hpart1, ?_⟩
  calc ‖((-2 * ((c : ℂ)⁻¹) ^ 3) * latticeSum 3 w) • hcL0‖
      ≤ ‖(-2 * ((c : ℂ)⁻¹) ^ 3) * latticeSum 3 w‖ * ‖hcL0‖ := norm_smul_le _ _
    _ ≤ (2 * (c⁻¹) ^ 3 * ‖latticeSum 3 w‖) * 2 :=
        mul_le_mul (le_of_eq hnorm_a) hcL0_opNorm_le (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.2 hc.le) 3))
            (norm_nonneg _))
    _ = 4 * (c ^ 3)⁻¹ * ‖latticeSum 3 w‖ := by
        rw [inv_pow]
        ring
