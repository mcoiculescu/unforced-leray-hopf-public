import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialTranslation

/-!
# Uniform axial weight-difference ratio

On each fixed cylinder, the ratio of axial weights at two points separated by a small axial
shift is uniformly close to one, independently of the axial location. This is the key small
factor in the commutator estimate for weighted heat continuity.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)

/-- A one-dimensional bracket comparison with a shift of size at most one. -/
theorem axialWeight_shift_compare {m : ℝ} (hm : 0 ≤ m) {x w : Plane}
    (hw : |w.2| ≤ 1) :
    axialWeight m x ≤ (1 + 2 * |w.2|) ^ (m / 2) * axialWeight m (x - w) := by
  have hr : 0 ≤ |w.2| := abs_nonneg _
  have hbaseOne : 2 * |x.2 - w.2| ≤ 1 + (x.2 - w.2) ^ 2 := by
    nlinarith [sq_nonneg (|x.2 - w.2| - 1), sq_abs (x.2 - w.2)]
  have hcross : 2 * |x.2 - w.2| * |w.2| ≤
      |w.2| * (1 + (x.2 - w.2) ^ 2) := by
    calc
      2 * |x.2 - w.2| * |w.2| =
          |w.2| * (2 * |x.2 - w.2|) := by ring
      _ ≤ |w.2| * (1 + (x.2 - w.2) ^ 2) :=
        mul_le_mul_of_nonneg_left hbaseOne hr
  have hsq : w.2 ^ 2 ≤ |w.2| := by
    have h := mul_le_mul_of_nonneg_left hw hr
    calc
      w.2 ^ 2 = |w.2| ^ 2 := (sq_abs w.2).symm
      _ ≤ |w.2| := by nlinarith [h]
  have hbase : 1 + x.2 ^ 2 ≤
      (1 + 2 * |w.2|) * (1 + (x.2 - w.2) ^ 2) := by
    have hx : x.2 = (x.2 - w.2) + w.2 := by ring
    rw [hx]
    have habs : |2 * (x.2 - w.2) * w.2| =
        2 * |x.2 - w.2| * |w.2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    have hcross' : 2 * (x.2 - w.2) * w.2 ≤
        |w.2| * (1 + (x.2 - w.2) ^ 2) := by
      calc
        2 * (x.2 - w.2) * w.2 ≤ |2 * (x.2 - w.2) * w.2| := le_abs_self _
        _ = 2 * |x.2 - w.2| * |w.2| := habs
        _ ≤ |w.2| * (1 + (x.2 - w.2) ^ 2) := hcross
    nlinarith [hcross', hsq]
  have hA : 0 < 1 + x.2 ^ 2 := by positivity
  have hB : 0 < 1 + (x.2 - w.2) ^ 2 := by positivity
  have hC : 0 < 1 + 2 * |w.2| := by positivity
  rw [axialWeight, axialBracket_rpow, axialWeight, axialBracket_rpow]
  calc
    (1 + x.2 ^ 2) ^ (m / 2) ≤
        ((1 + 2 * |w.2|) * (1 + (x.2 - w.2) ^ 2)) ^ (m / 2) :=
          Real.rpow_le_rpow hA.le hbase (by linarith)
    _ = (1 + 2 * |w.2|) ^ (m / 2) *
          (1 + (x.2 - w.2) ^ 2) ^ (m / 2) :=
        Real.mul_rpow hC.le hB.le

/-- The same comparison for an arbitrary axial shift. The square in the factor is the elementary
one-dimensional bracket inequality `1+(a+b)^2 ≤ (1+2|b|+|b|^2)(1+a^2)`. -/
theorem axialWeight_shift_compare_all {m : ℝ} (hm : 0 ≤ m) {x w : Plane} :
    axialWeight m x ≤ (1 + 2 * |w.2| + |w.2| ^ 2) ^ (m / 2) *
      axialWeight m (x - w) := by
  let h : ℝ := |w.2|
  have hh : 0 ≤ h := abs_nonneg _
  have hbaseOne : 2 * |x.2 - w.2| ≤ 1 + (x.2 - w.2) ^ 2 := by
    nlinarith [sq_nonneg (|x.2 - w.2| - 1), sq_abs (x.2 - w.2)]
  have hcross : 2 * (x.2 - w.2) * w.2 ≤ h * (1 + (x.2 - w.2) ^ 2) := by
    have habs : |2 * (x.2 - w.2) * w.2| = 2 * |x.2 - w.2| * h := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), h]
    calc
      2 * (x.2 - w.2) * w.2 ≤ |2 * (x.2 - w.2) * w.2| := le_abs_self _
      _ = 2 * |x.2 - w.2| * h := habs
      _ ≤ h * (1 + (x.2 - w.2) ^ 2) := by
        calc
          2 * |x.2 - w.2| * h = h * (2 * |x.2 - w.2|) := by ring
          _ ≤ h * (1 + (x.2 - w.2) ^ 2) :=
            mul_le_mul_of_nonneg_left hbaseOne hh
  have hbase : 1 + x.2 ^ 2 ≤
      (1 + 2 * h + h ^ 2) * (1 + (x.2 - w.2) ^ 2) := by
    have hx : x.2 = (x.2 - w.2) + w.2 := by ring
    rw [hx]
    have hsq : w.2 ^ 2 = h ^ 2 := by simp [h, sq_abs]
    nlinarith [hcross, hsq, hh]
  have hA : 0 < 1 + x.2 ^ 2 := by positivity
  have hB : 0 < 1 + (x.2 - w.2) ^ 2 := by positivity
  have hC : 0 < 1 + 2 * h + h ^ 2 := by positivity
  rw [axialWeight, axialBracket_rpow, axialWeight, axialBracket_rpow]
  calc
    (1 + x.2 ^ 2) ^ (m / 2) ≤
        ((1 + 2 * h + h ^ 2) * (1 + (x.2 - w.2) ^ 2)) ^ (m / 2) :=
          Real.rpow_le_rpow hA.le hbase (by linarith)
    _ = (1 + 2 * h + h ^ 2) ^ (m / 2) *
          (1 + (x.2 - w.2) ^ 2) ^ (m / 2) :=
        Real.mul_rpow hC.le hB.le
    _ = (1 + 2 * |w.2| + |w.2| ^ 2) ^ (m / 2) *
          (1 + (x.2 - w.2) ^ 2) ^ (m / 2) := by simp [h]

/-- Arbitrary-shift absolute difference estimate, with a polynomial Gaussian-integrable modulus. -/
theorem axialWeight_sub_le_shift_modulus_all {m : ℝ} (hm : 0 ≤ m) {x w : Plane} :
    |axialWeight m x - axialWeight m (x - w)| ≤
      (((1 + 2 * |w.2| + |w.2| ^ 2) ^ (m / 2)) ^ 2 - 1) *
        axialWeight m (x - w) := by
  let C : ℝ := (1 + 2 * |w.2| + |w.2| ^ 2) ^ (m / 2)
  have hCge : 1 ≤ C := by
    dsimp [C]
    exact Real.one_le_rpow (by nlinarith [abs_nonneg w.2]) (by linarith)
  have hA : 0 ≤ axialWeight m x := by
    dsimp [axialWeight, axialBracket]
    positivity
  have hB : 0 ≤ axialWeight m (x - w) := by
    dsimp [axialWeight, axialBracket]
    positivity
  have hAB := axialWeight_shift_compare_all hm (x := x) (w := w)
  have hBA : axialWeight m (x - w) ≤ C * axialWeight m x := by
    have h := axialWeight_shift_compare_all hm (x := x - w) (w := -w)
    simpa [C] using h
  have hleft : axialWeight m x - axialWeight m (x - w) ≤
      (C ^ 2 - 1) * axialWeight m (x - w) := by
    have h1 : axialWeight m x - axialWeight m (x - w) ≤
        (C - 1) * axialWeight m (x - w) := by
      dsimp [C] at hAB ⊢
      nlinarith
    have h2 : (C - 1) * axialWeight m (x - w) ≤
        (C ^ 2 - 1) * axialWeight m (x - w) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hCge]) hB
    exact h1.trans h2
  have hright : axialWeight m (x - w) - axialWeight m x ≤
      (C ^ 2 - 1) * axialWeight m (x - w) := by
    have h1 : axialWeight m (x - w) - axialWeight m x ≤
        (C - 1) * axialWeight m x := by nlinarith [hBA]
    have h2 : (C - 1) * axialWeight m x ≤ (C - 1) * (C * axialWeight m (x - w)) :=
      mul_le_mul_of_nonneg_left hAB (by linarith [hCge])
    have h3 : (C - 1) * (C * axialWeight m (x - w)) ≤
        (C ^ 2 - 1) * axialWeight m (x - w) := by nlinarith [hB]
    exact h1.trans (h2.trans h3)
  rw [show ((1 + 2 * |w.2| + |w.2| ^ 2) ^ (m / 2)) ^ 2 = C ^ 2 by rfl]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The axial weight difference is bounded by a factor that tends to zero with the shift, times
the weight at the input point. -/
theorem axialWeight_sub_le_shift_modulus {m : ℝ} (hm : 0 ≤ m) {x w : Plane}
    (hw : |w.2| ≤ 1) :
    |axialWeight m x - axialWeight m (x - w)| ≤
      (((1 + 2 * |w.2|) ^ (m / 2)) ^ 2 - 1) * axialWeight m (x - w) := by
  let C : ℝ := (1 + 2 * |w.2|) ^ (m / 2)
  have hCge : 1 ≤ C := by
    dsimp [C]
    exact Real.one_le_rpow (by nlinarith [abs_nonneg w.2]) (by linarith)
  have hCnonneg : 0 ≤ C := le_trans (by norm_num) hCge
  have hA : 0 ≤ axialWeight m x := by
    dsimp [axialWeight, axialBracket]
    positivity
  have hB : 0 ≤ axialWeight m (x - w) := by
    dsimp [axialWeight, axialBracket]
    positivity
  have hAB := axialWeight_shift_compare hm (x := x) (w := w) hw
  have hBA : axialWeight m (x - w) ≤ C * axialWeight m x := by
    have h := axialWeight_shift_compare hm (x := x - w) (w := -w) (by
      simpa using hw)
    simpa [C] using h
  have hleft : axialWeight m x - axialWeight m (x - w) ≤
      (C ^ 2 - 1) * axialWeight m (x - w) := by
    have h1 : axialWeight m x - axialWeight m (x - w) ≤ (C - 1) *
        axialWeight m (x - w) := by
      dsimp [C] at hAB ⊢
      nlinarith
    have h2 : (C - 1) * axialWeight m (x - w) ≤
        (C ^ 2 - 1) * axialWeight m (x - w) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hB
    exact h1.trans h2
  have hright : axialWeight m (x - w) - axialWeight m x ≤
      (C ^ 2 - 1) * axialWeight m (x - w) := by
    have h1 : axialWeight m (x - w) - axialWeight m x ≤
        (C - 1) * axialWeight m x := by nlinarith [hBA]
    have h2 : (C - 1) * axialWeight m x ≤
        (C - 1) * (C * axialWeight m (x - w)) :=
      mul_le_mul_of_nonneg_left hAB (by linarith)
    have h3 : (C - 1) * (C * axialWeight m (x - w)) ≤
        (C ^ 2 - 1) * axialWeight m (x - w) := by nlinarith [hB]
    exact h1.trans (h2.trans h3)
  rw [show ((1 + 2 * |w.2|) ^ (m / 2)) ^ 2 = C ^ 2 by rfl]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.axialWeight_shift_compare
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.axialWeight_sub_le_shift_modulus
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.axialWeight_shift_compare_all
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.axialWeight_sub_le_shift_modulus_all

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
