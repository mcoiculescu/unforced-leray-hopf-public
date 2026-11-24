import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrBracket.LapP

/-!
# Part III-a, task `PartIII-a:T21/c2/2/3`: the weight bracket `FmrBracket`

Source of record: `the November 2 reference manuscript`, lines 2947-2954.
With `s = r²/a`, `w = 1 + s`, `W = w^(m-2) > 0` the exact identity is
`(ν/a)(m²+3m+3) p - (νΔp + (3ν/a) p + ∂_σ p) = (ν/a) W m ((m-1)(1-s)² + 5 s (1+s))`,
which is nonnegative for `m ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.IIIa

theorem fmrBracket : FmrBracket := by
  intro m hm ν a hν ha x
  rw [fmrBracket_lapP m a ha x]
  unfold movWeight movWeightDt
  set s := (x.1 ^ 2 + x.2 ^ 2) / a with hs
  have hs0 : 0 ≤ s := div_nonneg (by positivity) ha.le
  have hw : 0 < 1 + s := by linarith
  have hr : x.1 ^ 2 + x.2 ^ 2 = s * a := by rw [hs]; field_simp
  set W := (1 + s) ^ (m - 2) with hW
  have hWpos : 0 < W := Real.rpow_pos_of_pos hw _
  have h1 : (1 + s) ^ (m - 1) = W * (1 + s) := by
    rw [hW, ← Real.rpow_add_one hw.ne']; congr 1; ring
  have h2 : (1 + s) ^ m = W * (1 + s) ^ 2 := by
    rw [hW, ← Real.rpow_natCast (1 + s) 2, ← Real.rpow_add hw]
    congr 1
    norm_num
  rw [h1, h2, hr]
  have hm0 : 0 ≤ m := by linarith
  have hm1 : 0 ≤ m - 1 := by linarith
  have hkey : 0 ≤ ν / a * W * (m * ((m - 1) * (1 - s) ^ 2 + 5 * s * (1 + s))) :=
    mul_nonneg (mul_nonneg (div_nonneg hν ha.le) hWpos.le)
      (mul_nonneg hm0 (add_nonneg (mul_nonneg hm1 (sq_nonneg _))
        (mul_nonneg (mul_nonneg (by norm_num) hs0) hw.le)))
  have hid : ν / a * (m ^ 2 + 3 * m + 3) * (W * (1 + s) ^ 2) -
      (ν * (4 * m / a * (W * (1 + s)) + 4 * m * (m - 1) * (s * a / a ^ 2) * W) +
        3 * ν / a * (W * (1 + s) ^ 2) + -(ν * m / a ^ 2) * (s * a) * (W * (1 + s))) =
      ν / a * W * (m * ((m - 1) * (1 - s) ^ 2 + 5 * s * (1 + s))) := by
    have ha' : a ≠ 0 := ha.ne'
    field_simp
    ring
  linarith

end UnforcedLeray.Short.IIIa
