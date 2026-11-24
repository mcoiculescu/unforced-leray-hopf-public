import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1

/-!
# `HarmonicPeriodicDecay` from three leaves (source 2354-2356)

Source `the November 2 reference manuscript`
2354-2356: `∑_n (w+n)⁻² = π² csc²(πw)` is exponentially small for `|Im w| ≥ 1`; the periodized
quadrupole is `H_c(y) = c⁻² ∑_n (w+n)⁻²`, `w = (ξ - iη)/c`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

/-- The lattice sum `S_k(w) = ∑_{n∈ℤ} (w+n)^{-k}`. -/
def latticeSum (k : ℕ) (w : ℂ) : ℂ := ∑' n : ℤ, ((w + (n : ℂ)) ^ k)⁻¹

/-- **Leaf A** (SP 2354-2356): summability of the terms and differentiability of the periodized
quadrupole off the line `η = 0` (`hasFDerivAt_tsum` on `|η| ≥ δ`, term derivatives
`-2(u-iη)⁻³(1,-i)` bounded by `2/(δ²+u_k²)^{3/2}`). -/
def HarmSummDiff : Prop :=
  ∀ c : ℝ, 0 < c → ∀ y : ℝ × ℝ, y.2 ≠ 0 →
    Summable (harmTerm c y) ∧ DifferentiableAt ℝ (harmPeriodic c) y

/-- **Leaf B** (SP 2354-2356): decay of the cotangent-derivative sums for `|Im w| ≥ 1`
(`iteratedFDerivWithin cot`, `pi_mul_cot_pi_q_exp`; reindex `n ↦ -n` for `Im w ≤ -1`). -/
def LatticeSumDecay : Prop :=
  ∃ C0 : ℝ, ∀ w : ℂ, 1 ≤ |w.im| →
    ‖latticeSum 2 w‖ ≤ C0 * Real.exp (-(2 * Real.pi * |w.im|)) ∧
    ‖latticeSum 3 w‖ ≤ C0 * Real.exp (-(2 * Real.pi * |w.im|))

/-- **Leaf C** (SP 2354-2356): identification of the periodized quadrupole with the lattice sum,
`H_c(y) = c⁻² S₂(w)`, `w = (ξ - iη)/c`, and the derivative bound `‖DH_c(y)‖ ≤ 4 c⁻³ ‖S₃(w)‖`
(`DH_c(y)(a,b) = -2c⁻³ S₃(w)(a - ib)`, `|a|+|b| ≤ 2‖(a,b)‖`). -/
def HarmLatticeIdent : Prop :=
  ∀ c : ℝ, 0 < c → ∀ y : ℝ × ℝ, y.2 ≠ 0 →
    harmPeriodic c y = ((c : ℂ) ^ 2)⁻¹ * latticeSum 2 (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) / c) ∧
    ‖fderiv ℝ (harmPeriodic c) y‖ ≤
      4 * (c ^ 3)⁻¹ * ‖latticeSum 3 (((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) / c)‖

theorem harmonicPeriodicDecay_of (hA : HarmSummDiff) (hB : LatticeSumDecay)
    (hC : HarmLatticeIdent) : HarmonicPeriodicDecay := by
  refine ⟨hA, ?_⟩
  obtain ⟨C0, hC0⟩ := hB
  have hC0' : 0 ≤ C0 := by
    have := (hC0 Complex.I (by simp)).1
    have h2 := norm_nonneg (latticeSum 2 Complex.I)
    have hp : 0 < Real.exp (-(2 * Real.pi * |Complex.I.im|)) := Real.exp_pos _
    by_contra hneg
    rw [not_le] at hneg
    nlinarith
  refine ⟨5 * C0, fun c hc y hy => ?_⟩
  have hc0 : 0 < c := by linarith
  have hy0 : y.2 ≠ 0 := by
    intro h; rw [h, abs_zero] at hy; linarith
  obtain ⟨hid, hder⟩ := hC c hc0 y hy0
  set w : ℂ := ((y.1 : ℂ) - (y.2 : ℂ) * Complex.I) / c with hw
  have hwim : w.im = -(y.2 / c) := by
    rw [hw, Complex.div_ofReal_im]; simp [neg_div]
  have habs : |w.im| = |y.2| / c := by
    rw [hwim, abs_neg, abs_div, abs_of_pos hc0]
  have h1 : 1 ≤ |w.im| := by
    rw [habs, le_div_iff₀ hc0]; linarith
  obtain ⟨b2, b3⟩ := hC0 w h1
  rw [habs] at b2 b3
  set E := Real.exp (-(2 * Real.pi * (|y.2| / c))) with hE
  have hEp : 0 < E := Real.exp_pos _
  have hcinv2 : (c ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hc)
  have hcinv3 : (c ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hc)
  have hcinv2' : 0 ≤ (c ^ 2)⁻¹ := by positivity
  have hcinv3' : 0 ≤ (c ^ 3)⁻¹ := by positivity
  have n1 : ‖harmPeriodic c y‖ ≤ C0 * E := by
    rw [hid, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc0.le]
    calc (c ^ 2)⁻¹ * ‖latticeSum 2 w‖ ≤ 1 * (C0 * E) :=
          mul_le_mul hcinv2 b2 (norm_nonneg _) zero_le_one
      _ = C0 * E := one_mul _
  have n2 : ‖fderiv ℝ (harmPeriodic c) y‖ ≤ 4 * (C0 * E) := by
    refine hder.trans ?_
    have : (c ^ 3)⁻¹ * ‖latticeSum 3 w‖ ≤ 1 * (C0 * E) :=
      mul_le_mul hcinv3 b3 (norm_nonneg _) zero_le_one
    nlinarith
  nlinarith

end UnforcedLeray.Short.IIIa
