import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Short.PartIIIa.Clock.Frame

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- The age-dependent scale `a = bandA ν s` lies in `[1, 3]` for `ν > 0`. -/
theorem gb_bandA_bounds {ν : ℝ} (hν : 0 < ν) (s : ℝ) : 1 ≤ bandA ν s ∧ bandA ν s ≤ 3 := by
  simp only [bandA, IIIa.clockA, bandAge, flatSigma]
  have h0 : 0 ≤ max 0 (min s (2 / ν)) := le_max_left _ _
  have h1 : max 0 (min s (2 / ν)) ≤ 2 / ν :=
    max_le (by positivity) (min_le_right _ _)
  have h2 : ν * (2 / ν) = 2 := by field_simp
  constructor
  · nlinarith [mul_nonneg hν.le h0]
  · nlinarith [mul_le_mul_of_nonneg_left h1 hν.le]

/-- `(1 + |t|)^2 ≤ 48 exp(t^2/24)`. -/
theorem gb_sq_le_exp (t : ℝ) : (1 + |t|) ^ 2 ≤ 48 * Real.exp (t ^ 2 / 24) := by
  have h1 : |t| ^ 2 = t ^ 2 := sq_abs t
  have h2 : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (|t| - 1)]
  have h3 : 1 + t ^ 2 / 24 ≤ Real.exp (t ^ 2 / 24) := by
    linarith [Real.add_one_le_exp (t ^ 2 / 24)]
  linarith

/-- `exp(-t^2/24) ≤ 48 (1+|t|)^{-2}`. -/
theorem gb_exp_le (t : ℝ) : Real.exp (-(t ^ 2) / 24) ≤ 48 * (1 + |t|) ^ (-(2 : ℝ)) := by
  have hpos : (0 : ℝ) < (1 + |t|) ^ 2 := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have h2 : Real.exp (-(t ^ 2) / 24) * Real.exp (t ^ 2 / 24) = 1 := by
    rw [← Real.exp_add, show -(t ^ 2) / 24 + t ^ 2 / 24 = 0 by ring, Real.exp_zero]
  calc Real.exp (-(t ^ 2) / 24) * (1 + |t|) ^ 2
      ≤ Real.exp (-(t ^ 2) / 24) * (48 * Real.exp (t ^ 2 / 24)) :=
        mul_le_mul_of_nonneg_left (gb_sq_le_exp t) (Real.exp_pos _).le
    _ = 48 * (Real.exp (-(t ^ 2) / 24) * Real.exp (t ^ 2 / 24)) := by ring
    _ = 48 := by rw [h2]; ring

/-- **`q_{k,s}` has uniform Gaussian tails** (source 2894-2899: "direct columns have Gaussian
tails"). -/
theorem qFunGaussBound :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.QFunGaussBound := by
  intro κ ν c k hν hc
  obtain ⟨C, hC⟩ := κ.e_decay
  refine ⟨10 * max C 0, fun s x => ?_⟩
  have hc0 : c ≠ 0 := (by linarith : (0 : ℝ) < c).ne'
  obtain ⟨a1, a3⟩ := gb_bandA_bounds hν s
  have hapos : (0 : ℝ) < bandA ν s := by linarith
  have hr_pos : (0 : ℝ) < Real.sqrt (bandA ν s) := Real.sqrt_pos.2 hapos
  have hsq2 : Real.sqrt (bandA ν s) ^ 2 = bandA ν s := Real.sq_sqrt hapos.le
  -- termwise bound by a Gaussian in `n`
  have hterm : ∀ n : ℤ,
      ‖κ.e k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s))‖ ≤
        max C 0 * Real.exp (-((x.1 + n * c) ^ 2 + x.2 ^ 2) / 24) := by
    intro n
    have hE : ‖κ.e k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
            x.2 / Real.sqrt (bandA ν s))‖ ≤
          max C 0 * Real.exp (-((x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s))) ^ 2
            + (x.2 / Real.sqrt (bandA ν s)) ^ 2) / 8) :=
        (hC k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
            x.2 / Real.sqrt (bandA ν s))).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hquad : (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s))) ^ 2
          + (x.2 / Real.sqrt (bandA ν s)) ^ 2 = ((x.1 + n * c) ^ 2 + x.2 ^ 2) / bandA ν s := by
      rw [show x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s))
          = (x.1 + n * c) / Real.sqrt (bandA ν s) by ring, div_pow, div_pow, ← add_div, hsq2]
    have hQ : ((x.1 + n * c) ^ 2 + x.2 ^ 2) / 3 ≤ ((x.1 + n * c) ^ 2 + x.2 ^ 2) / bandA ν s :=
      div_le_div_of_nonneg_left (by positivity) hapos a3
    have hexp : Real.exp (-((x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s))) ^ 2
            + (x.2 / Real.sqrt (bandA ν s)) ^ 2) / 8) ≤
          Real.exp (-((x.1 + n * c) ^ 2 + x.2 ^ 2) / 24) :=
      Real.exp_le_exp.mpr (by linarith [hquad, hQ])
    exact hE.trans (mul_le_mul_of_nonneg_left hexp (le_max_right _ _))
  -- summable majorant
  have hmaj : Summable (fun n : ℤ => (max C 0 * 48) * (1 + |-x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
    (UnforcedLeray.Gaussian.summable_translate (s := 2) (by norm_num) hc0 (-x.1)).mul_left _
  have hsumt : Summable (fun n : ℤ => max C 0 * Real.exp (-((x.1 + n * c) ^ 2 + x.2 ^ 2) / 24)) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (le_max_right _ _) (Real.exp_pos _).le)
      (fun n => ?_) hmaj
    have hg := gb_exp_le (x.1 + n * c)
    have habs : (1 + |-x.1 - (n : ℝ) * c|) = (1 + |x.1 + (n : ℝ) * c|) := by
      rw [show -x.1 - (n : ℝ) * c = -(x.1 + (n : ℝ) * c) by ring, abs_neg]
    calc max C 0 * Real.exp (-((x.1 + n * c) ^ 2 + x.2 ^ 2) / 24)
        ≤ max C 0 * Real.exp (-((x.1 + n * c) ^ 2) / 24) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by linarith [sq_nonneg x.2])) (le_max_right _ _)
      _ ≤ max C 0 * (48 * (1 + |x.1 + (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hg (le_max_right _ _)
      _ = (max C 0 * 48) * (1 + |-x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by
          rw [habs]; ring
  have hsumN : Summable (fun n : ℤ => ‖κ.e k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s))‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsumt
  -- the real Gaussian whose periodization dominates the sum
  have hF : ∀ z : ℝ × ℝ, ‖(fun z : ℝ × ℝ => max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 24)) z‖ ≤
      max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 6)) := by
    intro z
    rw [Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le)]
    norm_num
  have hper : ∑' n : ℤ, max C 0 * Real.exp (-((x.1 + n * c) ^ 2 + x.2 ^ 2) / 24) =
      UnforcedLeray.Gaussian.periodize c
        (fun z : ℝ × ℝ => max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 24)) x := by
    have hr := ((Equiv.neg ℤ).tsum_eq
      (fun n : ℤ => max C 0 * Real.exp (-((x.1 + n * c) ^ 2 + x.2 ^ 2) / 24))).symm
    rw [hr]
    unfold UnforcedLeray.Gaussian.periodize
    congr 1
    funext n
    simp only [Equiv.neg_apply]
    congr 2
    push_cast
    ring_nf
  have hac : (6 : ℝ) ≤ c ^ 2 := by nlinarith
  have hpbound := UnforcedLeray.Gaussian.norm_periodize_le_of_gauss (f := fun z : ℝ × ℝ =>
      max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 24)) (A := max C 0) (a := 6) (c := c)
      (by norm_num) hac hF x
  -- the bound
  have hpow1 : bandA ν s ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos a1 (by norm_num)
  have hnorm : ‖qFun κ ν c k s x‖ ≤ ∑' n : ℤ,
      max C 0 * Real.exp (-((x.1 + n * c) ^ 2 + x.2 ^ 2) / 24) := by
    have hq : qFun κ ν c k s x = ((bandA ν s ^ (-(2 : ℝ)) : ℝ) : ℂ) * ∑' n : ℤ,
        κ.e k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s)) := rfl
    rw [hq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hapos.le _)]
    calc bandA ν s ^ (-(2 : ℝ)) * ‖∑' n : ℤ,
          κ.e k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
            x.2 / Real.sqrt (bandA ν s))‖
        ≤ 1 * ‖∑' n : ℤ,
          κ.e k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
            x.2 / Real.sqrt (bandA ν s))‖ :=
          mul_le_mul_of_nonneg_right hpow1 (norm_nonneg _)
      _ = ‖∑' n : ℤ,
          κ.e k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
            x.2 / Real.sqrt (bandA ν s))‖ := one_mul _
      _ ≤ ∑' n : ℤ, ‖κ.e k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
            x.2 / Real.sqrt (bandA ν s))‖ := norm_tsum_le_tsum_norm hsumN
      _ ≤ ∑' n : ℤ, max C 0 * Real.exp (-((x.1 + n * c) ^ 2 + x.2 ^ 2) / 24) :=
          Summable.tsum_le_tsum hterm hsumN hsumt
  calc ‖qFun κ ν c k s x‖
      ≤ ∑' n : ℤ, max C 0 * Real.exp (-((x.1 + n * c) ^ 2 + x.2 ^ 2) / 24) := hnorm
    _ = UnforcedLeray.Gaussian.periodize c
        (fun z : ℝ × ℝ => max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 24)) x := hper
    _ ≤ ‖UnforcedLeray.Gaussian.periodize c
        (fun z : ℝ × ℝ => max C 0 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 24)) x‖ := Real.le_norm_self _
    _ ≤ 10 * max C 0 * Real.exp (-x.2 ^ 2 / (4 * 6)) := hpbound
    _ = 10 * max C 0 * Real.exp (-(x.2 ^ 2) / 24) := by norm_num

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
