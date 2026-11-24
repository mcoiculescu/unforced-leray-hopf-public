import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Short.PartIIIa.Clock.Frame

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- The age-dependent scale `a = bandA ν s` lies in `[1, 3]` for `ν > 0`. -/
theorem l0k_bandA_bounds {ν : ℝ} (hν : 0 < ν) (s : ℝ) : 1 ≤ bandA ν s ∧ bandA ν s ≤ 3 := by
  simp only [bandA, IIIa.clockA, bandAge, flatSigma]
  have h0 : 0 ≤ max 0 (min s (2 / ν)) := le_max_left _ _
  have h1 : max 0 (min s (2 / ν)) ≤ 2 / ν :=
    max_le (by positivity) (min_le_right _ _)
  have h2 : ν * (2 / ν) = 2 := by field_simp
  constructor
  · nlinarith [mul_nonneg hν.le h0]
  · nlinarith [mul_le_mul_of_nonneg_left h1 hν.le]

/-- **`a Λ⁰_{d,k}(x/√a)` is continuous in the age** (source 2896-2899, 4352-4356). -/
theorem lam0KerPtCont :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Lam0KerPtCont := by
  intro κ ν c k x hν hc
  obtain ⟨C, hC⟩ := κ.lamP_decay
  have hc0 : c ≠ 0 := (by linarith : (0 : ℝ) < c).ne'
  have hA : ∀ s, 1 ≤ bandA ν s ∧ bandA ν s ≤ 3 := fun s => l0k_bandA_bounds hν s
  have hAc : Continuous (fun s => bandA ν s) := by
    simp only [bandA, IIIa.clockA, bandAge, flatSigma]
    exact continuous_const.add (continuous_const.mul
      (continuous_const.max (continuous_id.min continuous_const)))
  have hsq : Continuous (fun s => Real.sqrt (bandA ν s)) :=
    Real.continuous_sqrt.comp hAc
  have hsq0 : ∀ s, Real.sqrt (bandA ν s) ≠ 0 := fun s =>
    (Real.sqrt_pos.2 (show (0 : ℝ) < bandA ν s by linarith [(hA s).1])).ne'
  have hq : ∀ s, lam0Ker κ ν c k s x =
      (bandA ν s : ℂ) * ∑' n : ℤ,
        κ.lamP k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s)) := fun s => rfl
  have hfun : (fun s => lam0Ker κ ν c k s x) = fun s =>
      (bandA ν s : ℂ) * ∑' n : ℤ,
        κ.lamP k (x.1 / Real.sqrt (bandA ν s) + n * (c / Real.sqrt (bandA ν s)),
          x.2 / Real.sqrt (bandA ν s)) := funext hq
  rw [hfun]
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp hAc
  · have hsum : Summable (fun n : ℤ =>
        (max C 0 * 4) * (1 + |-x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ))) :=
      (UnforcedLeray.Gaussian.summable_translate (s := 2) (by norm_num) hc0 (-x.1)).mul_left _
    refine continuous_tsum (fun n => ?_) hsum (fun n s => ?_)
    · have hp1 : Continuous fun s =>
          x.1 / Real.sqrt (bandA ν s) + (n : ℝ) * (c / Real.sqrt (bandA ν s)) :=
        (Continuous.div continuous_const hsq hsq0).add
          (continuous_const.mul (Continuous.div continuous_const hsq hsq0))
      have hp2 : Continuous fun s => x.2 / Real.sqrt (bandA ν s) :=
        Continuous.div continuous_const hsq hsq0
      exact (κ.lamP_cont k).comp (hp1.prodMk hp2)
    · obtain ⟨a1, a3⟩ := hA s
      have hapos : (0 : ℝ) < bandA ν s := by linarith
      have hr_pos : (0 : ℝ) < Real.sqrt (bandA ν s) := Real.sqrt_pos.2 hapos
      have hr2 : Real.sqrt (bandA ν s) ≤ 2 := by
        nlinarith [Real.sq_sqrt hapos.le, Real.sqrt_nonneg (bandA ν s)]
      have hyinv : (1 + |x.1 / Real.sqrt (bandA ν s) + (n : ℝ) * (c / Real.sqrt (bandA ν s))|
            + |x.2 / Real.sqrt (bandA ν s)|)⁻¹ ≤ ((1 + |x.1 + n * c|) / 2)⁻¹ := by
        apply inv_anti₀ (by positivity)
        have hu : x.1 / Real.sqrt (bandA ν s) + (n : ℝ) * (c / Real.sqrt (bandA ν s)) =
            (x.1 + n * c) / Real.sqrt (bandA ν s) := by ring
        have hy1' : |x.1 + n * c| / 2 ≤
            |x.1 / Real.sqrt (bandA ν s) + (n : ℝ) * (c / Real.sqrt (bandA ν s))| := by
          rw [hu, abs_div, abs_of_pos hr_pos]
          have : |x.1 + n * c| / 2 ≤ |x.1 + n * c| / Real.sqrt (bandA ν s) :=
            div_le_div_of_nonneg_left (abs_nonneg _) hr_pos hr2
          exact this
        have := abs_nonneg (x.2 / Real.sqrt (bandA ν s))
        linarith
      have hpow : (((1 + |x.1 + n * c|) / 2)⁻¹) ^ 2 = 4 * (1 + |x.1 + n * c|) ^ (-(2 : ℝ)) := by
        have hpos : (0 : ℝ) < 1 + |x.1 + n * c| := by positivity
        rw [Real.rpow_neg hpos.le, Real.rpow_two]
        field_simp
        norm_num
      have habs : (1 + |-x.1 - (n : ℝ) * c|) = (1 + |x.1 + (n : ℝ) * c|) := by
        rw [show -x.1 - (n : ℝ) * c = -(x.1 + (n : ℝ) * c) by ring, abs_neg]
      calc _ ≤ max C 0 * (1 + |x.1 / Real.sqrt (bandA ν s) + (n : ℝ) * (c / Real.sqrt (bandA ν s))|
            + |x.2 / Real.sqrt (bandA ν s)|)⁻¹ ^ 2 :=
            (hC k _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
        _ ≤ max C 0 * (((1 + |x.1 + n * c|) / 2)⁻¹) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hyinv 2) (le_max_right _ _)
        _ = (max C 0 * 4) * (1 + |x.1 + (n : ℝ) * c|) ^ (-(2 : ℝ)) := by
            rw [hpow]; ring
        _ = (max C 0 * 4) * (1 + |-x.1 - (n : ℝ) * c|) ^ (-(2 : ℝ)) := by rw [habs]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
