import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.Of

/-!
# `PartIII-b:C/asrc/ra/8/1/org` : leaf (G0) `BkMajSummable`

Source of record: `the November 2 reference manuscript` (73 pages), 4963 (`c = ν⁻²`,
`x_j = (q - jc, η)`, `V_j` and `ψ_j` with the Gaussian `e^{-|x_j|²/(4a)}`) and 4978 (summability of
the Gaussian lattice sums).

The lattice majorant `(1 + |x_j|)⁶ e^{-|x_j|²/(4a)}` is summable in `j ∈ ℤ`: by
`1 + |x_j| ≤ (1 + |η|)(1 + |q - jc|)`, `1 + |q - jc| ≤ (1 + |q| + c)(1 + |j|)` and `(1+u)⁶ ≤ 64(1+u⁶)`,
the summand is at most a constant times `e^{-(q-jc)²/(4a)} + |j|⁶ e^{-(q-jc)²/(4a)}`, which is
summable by `gp_gauss_summable` and `gp_gauss_pow_summable` (`Gauss.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `(1 + u)⁶ ≤ 64 (1 + u⁶)` for `u ≥ 0`. -/
lemma bkMaj_pow6_le (u : ℝ) (hu : 0 ≤ u) : (1 + u) ^ 6 ≤ 64 * (1 + u ^ 6) := by
  have h6 : 0 ≤ u ^ 6 := pow_nonneg hu 6
  rcases le_total u 1 with h | h
  · have h1 : (1 + u) ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
    norm_num at h1
    linarith
  · have h1 : (1 + u) ≤ 2 * u := by linarith
    have h2 : (1 + u) ^ 6 ≤ (2 * u) ^ 6 := pow_le_pow_left₀ (by linarith) h1 6
    have h3 : (2 * u) ^ 6 = 64 * u ^ 6 := by ring
    linarith

/-- The Gaussian exponential of `bkMaj` is dominated by the one in the first coordinate
(general `a > 0`; `gp_exp_le` is the same bound with `a = ageA ν s`). -/
lemma bkMaj_exp_le (a : ℝ) (ha : 0 < a) (j : ℤ) (ν : ℝ) (x : ℝ × ℝ) :
    Real.exp (-(sq2 (xj ν j x)) / (4 * a))
      ≤ Real.exp (-(1 / (4 * a)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) := by
  apply Real.exp_le_exp.mpr
  have hsq : sq2 (xj ν j x) = (x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2 := rfl
  have e : -(sq2 (xj ν j x)) / (4 * a) = -(1 / (4 * a)) * sq2 (xj ν j x) := by
    ring
  rw [e, hsq]
  have hq : 0 ≤ 1 / (4 * a) := le_of_lt (div_pos one_pos (by linarith))
  nlinarith [sq_nonneg x.2, mul_nonneg hq (sq_nonneg x.2)]

/-- One summand of the lattice majorant, dominated by a constant times the shifted Gaussian
`e^{-(q-jc)²/(4a)}` and its `|j|⁶`-weighted version (source 4963, 4978). -/
lemma bkMaj_term_le (ν a : ℝ) (hν : 0 < ν) (ha : 0 < a) (j : ℤ) (x : ℝ × ℝ) :
    bkMaj ν a j x ≤ (1 + |x.2|) ^ 6 * ((1 + |x.1| + cOf ν) ^ 6 * 64) *
      (Real.exp (-(1 / (4 * a)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)
        + |(j : ℝ)| ^ 6 * Real.exp (-(1 / (4 * a)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have hc0 : 0 ≤ cOf ν := hc.le
  have hcL : 0 ≤ 1 + |x.1| + cOf ν := by linarith [abs_nonneg x.1]
  -- (i) the polynomial factor `(1 + |x_j|)^6`
  have hA : (1 + ‖xj ν j x‖) ^ 6 ≤ ((1 + |x.2|) * (1 + |x.1 - (j : ℝ) * cOf ν|)) ^ 6 :=
    pow_le_pow_left₀ (by positivity) (gp_one_add_norm ν j x) 6
  rw [mul_pow] at hA
  -- (ii) `1 + |q - jc| ≤ (1 + |q| + c)(1 + |j|)`
  have hu : 1 + |x.1 - (j : ℝ) * cOf ν| ≤ (1 + |x.1| + cOf ν) * (1 + |(j : ℝ)|) := by
    have h1 : |x.1 - (j : ℝ) * cOf ν| ≤ |x.1| + |(j : ℝ)| * cOf ν := by
      have h2 := abs_sub x.1 ((j : ℝ) * cOf ν)
      rw [abs_mul, abs_of_pos hc] at h2
      exact h2
    nlinarith [abs_nonneg x.1, mul_nonneg (abs_nonneg (j : ℝ)) hc0,
      mul_nonneg (abs_nonneg x.1) (abs_nonneg (j : ℝ))]
  have hB : (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 6 ≤
      (1 + |x.1| + cOf ν) ^ 6 * (64 * (1 + |(j : ℝ)| ^ 6)) := by
    calc (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 6
        ≤ ((1 + |x.1| + cOf ν) * (1 + |(j : ℝ)|)) ^ 6 :=
          pow_le_pow_left₀ (by positivity) hu 6
      _ = (1 + |x.1| + cOf ν) ^ 6 * (1 + |(j : ℝ)|) ^ 6 := mul_pow _ _ _
      _ ≤ (1 + |x.1| + cOf ν) ^ 6 * (64 * (1 + |(j : ℝ)| ^ 6)) :=
          mul_le_mul_of_nonneg_left (bkMaj_pow6_le _ (abs_nonneg _)) (pow_nonneg hcL 6)
  -- (iii) the exponential factor
  have hE := bkMaj_exp_le a ha j ν x
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * a)) := (Real.exp_pos _).le
  unfold bkMaj
  calc (1 + ‖xj ν j x‖) ^ 6 * Real.exp (-(sq2 (xj ν j x)) / (4 * a))
      ≤ ((1 + |x.2|) ^ 6 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 6) *
          Real.exp (-(1 / (4 * a)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) :=
        mul_le_mul hA hE hE0 (by positivity)
    _ ≤ ((1 + |x.2|) ^ 6 * ((1 + |x.1| + cOf ν) ^ 6 * (64 * (1 + |(j : ℝ)| ^ 6)))) *
          Real.exp (-(1 / (4 * a)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (1 + |x.2|) ^ 6 * ((1 + |x.1| + cOf ν) ^ 6 * 64) *
          (Real.exp (-(1 / (4 * a)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)
            + |(j : ℝ)| ^ 6 * Real.exp (-(1 / (4 * a)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
        ring

/-- **(G0)** The lattice majorant `(1 + |x_j|)⁶ e^{-|x_j|²/(4a)}` is summable in `j`
(`c = ν⁻² > 0`, source 4963, 4978). -/
theorem bkMajSummable : BkMajSummable := by
  intro ν a x hν ha
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have hα : 0 < 1 / (4 * a) := div_pos one_pos (by linarith)
  have h0 := gp_gauss_summable x.1 (1 / (4 * a)) (cOf ν) hα hc
  have h6 := gp_gauss_pow_summable x.1 (1 / (4 * a)) (cOf ν) hα hc 6
  have hS := (h0.add h6).mul_left ((1 + |x.2|) ^ 6 * ((1 + |x.1| + cOf ν) ^ 6 * 64))
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hS
  · unfold bkMaj
    positivity
  · exact bkMaj_term_le ν a hν ha j x

end UnforcedLeray.Short.PartIIIb.Concrete
