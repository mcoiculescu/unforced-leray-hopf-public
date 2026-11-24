import UnforcedLeray.Short.PartIIIb.Near

/-!
# Proof of `GainRatioSup` (source: `the November 2 reference manuscript`, lines 3993-4001)

Write `u = √M`, so `1 ≤ u` and `u² = M`. For `ν > 0` and `0 < s ≤ t`,
`ν(t/(1+νt) - s/(1+νs)) = ν(t-s)/((1+νt)(1+νs))`.

* Upper bound. Put `g = (u-1)(1+νt)(1+νs) - ν(t-s)(u+1)`. Using `u² = M`,
  `s(u+1) g = (Ms-t)(1+νs)² + (t-s)(1-uνs)²`, which is `≥ 0` because `s ≤ t ≤ Ms`.
  Hence `g ≥ 0`, i.e. the value is `≤ (u-1)/(u+1)`.
* Attained at `s = 1/(νu)`, `t = Ms = u/ν`. Then `νt = u` and `νs = 1/u`, and the value is
  `(u-1)/(u+1)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

theorem gainRatioSup : UnforcedLeray.Short.PartIIIb.GainRatioSup := by
  intro ν M hν hM
  have hM0 : (0:ℝ) ≤ M := by linarith
  have hu2 : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM0
  have hu1 : 1 ≤ Real.sqrt M := by
    have h := Real.sqrt_le_sqrt hM
    rwa [Real.sqrt_one] at h
  generalize hu : Real.sqrt M = u at hu2 hu1 ⊢
  have hu0 : 0 < u := by linarith
  have hu1pos : 0 < u + 1 := by linarith
  have hsq : 1 ≤ u * u := by nlinarith
  refine ⟨⟨1 / (ν * u), u / ν, div_pos one_pos (mul_pos hν hu0), ?_, ?_, ?_⟩, ?_⟩
  · rw [div_le_div_iff₀ (mul_pos hν hu0) hν]
    nlinarith [mul_le_mul_of_nonneg_left hsq hν.le]
  · have h : M * (1 / (ν * u)) = u / ν := by
      rw [← hu2]
      field_simp
    exact le_of_eq h.symm
  · have e1 : ν * (u / ν) = u := by field_simp
    have e2 : ν * (1 / (ν * u)) = 1 / u := by field_simp
    have hA : u + 1 ≠ 0 := hu1pos.ne'
    have hA' : 1 + u ≠ 0 := by intro h; linarith
    rw [e1, e2]
    field_simp
    ring
  · rintro v ⟨s, t, hs, hst, htM, rfl⟩
    have ht0 : 0 < t := lt_of_lt_of_le hs hst
    have h1 : 0 < 1 + ν * t := by have := mul_pos hν ht0; linarith
    have h2 : 0 < 1 + ν * s := by have := mul_pos hν hs; linarith
    have hval : ν * (t / (1 + ν * t) - s / (1 + ν * s))
        = ν * (t - s) / ((1 + ν * t) * (1 + ν * s)) := by
      rw [div_sub_div _ _ h1.ne' h2.ne']
      ring
    rw [hval, div_le_div_iff₀ (mul_pos h1 h2) hu1pos]
    have key : s * (u + 1) * ((u - 1) * (1 + ν * t) * (1 + ν * s) - ν * (t - s) * (u + 1))
        = (M * s - t) * (1 + ν * s) ^ 2 + (t - s) * (1 - u * ν * s) ^ 2 := by
      linear_combination (s * (1 + ν * s) ^ 2) * hu2
    have hA : 0 ≤ M * s - t := by linarith
    have hB : 0 ≤ t - s := by linarith
    have hR : 0 ≤ (M * s - t) * (1 + ν * s) ^ 2 + (t - s) * (1 - u * ν * s) ^ 2 :=
      add_nonneg (mul_nonneg hA (sq_nonneg _)) (mul_nonneg hB (sq_nonneg _))
    have hpos : 0 < s * (u + 1) := mul_pos hs hu1pos
    have hg : 0 ≤ (u - 1) * (1 + ν * t) * (1 + ν * s) - ν * (t - s) * (u + 1) :=
      (mul_nonneg_iff_of_pos_left hpos).mp (by rw [key]; exact hR)
    nlinarith [hg]

end UnforcedLeray.Short.PartIIIb
