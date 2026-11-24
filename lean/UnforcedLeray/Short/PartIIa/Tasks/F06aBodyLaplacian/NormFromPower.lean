import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F06_1

/-!
# Part II-a, task `PartII-a:F06/1/7`: from a power bound to a norm bound

Source of record: `the November 2 reference manuscript`, lines 1431-1480.
Proves `NormFromPower` (P6 of `Sub/PartIIa_F06_1.lean`), with constant `K' = 2K`.
Pure real analysis: `a^s ≤ 2 K^s (f^s + (m w)^s)` and `f^s + (m w)^s ≤ (f + m w)^s`
(`Real.add_rpow_le_rpow_add`), so if `a > 2 K (f + m w)` then `(2Kg)^s < a^s ≤ 2 K^s g^s ≤ (2Kg)^s`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

theorem normFromPower : NormFromPower := by
  intro s hs K hK
  refine ⟨2 * K, by positivity, ?_⟩
  intro a f w m ha hf hw hm h
  have hs0 : 0 ≤ s := by linarith
  have hy : 0 ≤ m * w := mul_nonneg hm hw
  have hKs : 0 ≤ K ^ s := Real.rpow_nonneg hK s
  have hfs : 0 ≤ f ^ s := Real.rpow_nonneg hf s
  have hys : 0 ≤ (m * w) ^ s := Real.rpow_nonneg hy s
  have e : ENNReal.ofReal (2 * K ^ s * (f ^ s + (m * w) ^ s)) =
      2 * ENNReal.ofReal K ^ s * (ENNReal.ofReal f ^ s + ENNReal.ofReal m ^ s * ENNReal.ofReal w ^ s) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_add hfs hys, Real.mul_rpow hm hw,
      ENNReal.ofReal_mul (Real.rpow_nonneg hm s), ← ENNReal.ofReal_rpow_of_nonneg hK hs0,
      ← ENNReal.ofReal_rpow_of_nonneg hf hs0, ← ENNReal.ofReal_rpow_of_nonneg hm hs0,
      ← ENNReal.ofReal_rpow_of_nonneg hw hs0]
  rw [← e, ENNReal.ofReal_rpow_of_nonneg ha hs0,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (by norm_num) hKs) (add_nonneg hfs hys))]
    at h
  have hsup : f ^ s + (m * w) ^ s ≤ (f + m * w) ^ s :=
    Real.add_rpow_le_rpow_add hf hy hs.le
  set g := f + m * w with hg
  have hg0 : 0 ≤ g := add_nonneg hf hy
  have hgs : 0 ≤ g ^ s := Real.rpow_nonneg hg0 s
  by_contra hlt
  have hlt := not_le.mp hlt
  have hK2 : 0 ≤ 2 * K * g := by positivity
  have h1 : (2 * K * g) ^ s < a ^ s := Real.rpow_lt_rpow hK2 hlt (by linarith)
  have h2 : (2:ℝ) ≤ 2 ^ s := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs.le
    simpa using this
  have h3 : (2 * K * g) ^ s = 2 ^ s * (K ^ s * g ^ s) := by
    rw [Real.mul_rpow (by positivity) hg0, Real.mul_rpow (by norm_num) hK]
    ring
  have h4 : 2 * (K ^ s * g ^ s) ≤ 2 ^ s * (K ^ s * g ^ s) :=
    mul_le_mul_of_nonneg_right h2 (mul_nonneg hKs hgs)
  have h5 : K ^ s * (f ^ s + (m * w) ^ s) ≤ K ^ s * g ^ s :=
    mul_le_mul_of_nonneg_left hsup hKs
  have h6 : a ^ s ≤ 2 * (K ^ s * g ^ s) := by nlinarith
  linarith
