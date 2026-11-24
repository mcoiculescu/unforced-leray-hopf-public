import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Short.PartIIIa.Clock.Frame

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- `(1 + |t|)^2 ≤ 48 exp(t^2/24)`. -/
theorem qf_sq_le_exp (t : ℝ) : (1 + |t|) ^ 2 ≤ 48 * Real.exp (t ^ 2 / 24) := by
  have h1 : |t| ^ 2 = t ^ 2 := sq_abs t
  have h2 : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (|t| - 1)]
  have h3 : 1 + t ^ 2 / 24 ≤ Real.exp (t ^ 2 / 24) := by
    linarith [Real.add_one_le_exp (t ^ 2 / 24)]
  linarith

/-- `exp(-t^2/24) ≤ 48 (1+|t|)^{-2}`. -/
theorem qf_exp_le (t : ℝ) : Real.exp (-(t ^ 2) / 24) ≤ 48 * (1 + |t|) ^ (-(2 : ℝ)) := by
  have hpos : (0 : ℝ) < (1 + |t|) ^ 2 := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have h2 : Real.exp (-(t ^ 2) / 24) * Real.exp (t ^ 2 / 24) = 1 := by
    rw [← Real.exp_add, show -(t ^ 2) / 24 + t ^ 2 / 24 = 0 by ring, Real.exp_zero]
  calc Real.exp (-(t ^ 2) / 24) * (1 + |t|) ^ 2
      ≤ Real.exp (-(t ^ 2) / 24) * (48 * Real.exp (t ^ 2 / 24)) :=
        mul_le_mul_of_nonneg_left (qf_sq_le_exp t) (Real.exp_pos _).le
    _ = 48 * (Real.exp (-(t ^ 2) / 24) * Real.exp (t ^ 2 / 24)) := by ring
    _ = 48 := by rw [h2]; ring

/-- Algebra of the cell-length rescaling. -/
theorem qf_quad (x1 x2 n c r : ℝ) :
    (x1 / r + n * (c / r)) ^ 2 + (x2 / r) ^ 2 = ((x1 + n * c) ^ 2 + x2 ^ 2) / r ^ 2 := by
  rw [show x1 / r + n * (c / r) = (x1 + n * c) / r by ring, div_pow, div_pow, ← add_div]

/-- **`q_{k,s}(x)` is continuous in the age** (source 4352-4356, 4650-4654). -/
theorem qFunPtCont :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.QFunPtCont := by
  intro κ ν c k x hν hc
  obtain ⟨C, hC⟩ := κ.e_decay
  have hc0 : c ≠ 0 := (by linarith : (0 : ℝ) < c).ne'
  -- the age-dependent scale lies in [1, 3]
  have hA : ∀ s, 1 ≤ bandA ν s ∧ bandA ν s ≤ 3 := by
    intro s
    simp only [bandA, IIIa.clockA, bandAge, flatSigma]
    have h0 : 0 ≤ max 0 (min s (2 / ν)) := le_max_left _ _
    have h1 : max 0 (min s (2 / ν)) ≤ 2 / ν :=
      max_le (by positivity) (min_le_right _ _)
    have h2 : ν * (2 / ν) = 2 := by field_simp
    constructor
    · nlinarith [mul_nonneg hν.le h0]
    · nlinarith [mul_le_mul_of_nonneg_left h1 hν.le]
  have hAc : Continuous (fun s => bandA ν s) := by
    simp only [bandA, IIIa.clockA, bandAge, flatSigma]
    exact continuous_const.add (continuous_const.mul
      (continuous_const.max (continuous_id.min continuous_const)))
  have hsq : Continuous (fun s => Real.sqrt (bandA ν s)) :=
    Real.continuous_sqrt.comp hAc
  have hsq0 : ∀ s, Real.sqrt (bandA ν s) ≠ 0 := fun s =>
    (Real.sqrt_pos.2 (show (0 : ℝ) < bandA ν s by linarith [(hA s).1])).ne'
  have hq : ∀ s, qFun κ ν c k s x =
      ((bandA ν s ^ (-2 : ℝ) : ℝ) : ℂ) * ∑' n : ℤ,
        κ.e k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s)) := fun s => rfl
  have hfun : (fun s => qFun κ ν c k s x) = fun s =>
      ((bandA ν s ^ (-2 : ℝ) : ℝ) : ℂ) * ∑' n : ℤ,
        κ.e k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s)) := funext hq
  rw [hfun]
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp
      (Continuous.rpow_const hAc (fun s => Or.inl
        (show (0 : ℝ) < bandA ν s by linarith [(hA s).1]).ne'))
  · have hsum : Summable (fun n : ℤ =>
        (max C 0 * 48) * (1 + |-x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
      (UnforcedLeray.Gaussian.summable_translate (s := 2) (by norm_num) hc0 (-x.1)).mul_left _
    refine continuous_tsum (fun n => ?_) hsum (fun n s => ?_)
    · have hp1 : Continuous fun s =>
          x.1 / Real.sqrt (bandA ν s) + (n : ℝ) * (c / Real.sqrt (bandA ν s)) :=
        (Continuous.div continuous_const hsq hsq0).add
          (continuous_const.mul (Continuous.div continuous_const hsq hsq0))
      have hp2 : Continuous fun s => x.2 / Real.sqrt (bandA ν s) :=
        Continuous.div continuous_const hsq hsq0
      exact (κ.e_cont k).comp (hp1.prodMk hp2)
    · obtain ⟨a1, a3⟩ := hA s
      have hapos : (0 : ℝ) < bandA ν s := by linarith
      have hE : ‖κ.e k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
            x.2 / Real.sqrt (bandA ν s))‖ ≤
          max C 0 * Real.exp (-((x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s))) ^ 2
            + (x.2 / Real.sqrt (bandA ν s)) ^ 2) / 8) :=
        (hC k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
            x.2 / Real.sqrt (bandA ν s))).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      have hsq2 : Real.sqrt (bandA ν s) ^ 2 = bandA ν s := Real.sq_sqrt hapos.le
      have hquad : (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s))) ^ 2
          + (x.2 / Real.sqrt (bandA ν s)) ^ 2 = ((x.1 + n * c) ^ 2 + x.2 ^ 2) / bandA ν s := by
        rw [qf_quad, hsq2]
      have hlow : (x.1 + n * c) ^ 2 / 3 ≤ ((x.1 + n * c) ^ 2 + x.2 ^ 2) / bandA ν s := by
        rw [le_div_iff₀ hapos]
        nlinarith [mul_le_mul_of_nonneg_left a3 (sq_nonneg (x.1 + n * c)), sq_nonneg x.2]
      have hexp : Real.exp (-((x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s))) ^ 2
            + (x.2 / Real.sqrt (bandA ν s)) ^ 2) / 8) ≤ Real.exp (-((x.1 + n * c) ^ 2) / 24) :=
        Real.exp_le_exp.mpr (by linarith [hquad, hlow])
      have hgauss := qf_exp_le (x.1 + n * c)
      have habs : (1 + |-x.1 - (n : ℝ) * c|) = (1 + |x.1 + (n : ℝ) * c|) := by
        rw [show -x.1 - (n : ℝ) * c = -(x.1 + (n : ℝ) * c) by ring, abs_neg]
      calc _ ≤ max C 0 * Real.exp (-((x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s))) ^ 2
            + (x.2 / Real.sqrt (bandA ν s)) ^ 2) / 8) := hE
        _ ≤ max C 0 * Real.exp (-((x.1 + n * c) ^ 2) / 24) :=
            mul_le_mul_of_nonneg_left hexp (le_max_right _ _)
        _ ≤ max C 0 * (48 * (1 + |x.1 + (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hgauss (le_max_right _ _)
        _ = (max C 0 * 48) * (1 + |-x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by
            rw [habs]; ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
