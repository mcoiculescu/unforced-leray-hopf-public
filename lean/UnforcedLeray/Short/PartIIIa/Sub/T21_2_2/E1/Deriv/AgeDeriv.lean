import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5

/-!
# Part III-a, task `PartIII-a:T21/2/2/3/5/2`: `RevAgeDeriv` (SP 2857)

`revAge ν s ζ = z/(1-νz)` with `z = z_s - ζ`, `z_s = movingZ ν s`. Its `ζ`-derivative is
`-1/(1-νz)²`, and `clockA ν (revAge ν s ζ) = 1/(1-νz)`, so the derivative is `-(clockA ..)²`.
The denominator `1 - νz` is positive because `ζ > 0` gives `z < z_s` and `ν z_s < 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- **`RevAgeDeriv`** (SP 2857): `d(revAge)/dζ = -a(r)²`. -/
theorem revAgeDeriv (m : ℝ) : UnforcedLeray.Short.IIIa.AdjE1.RevAgeDeriv m := by
  intro ν tr t s φ ζ hζ
  obtain ⟨hν, ht0, hts, _, hz⟩ := hζ
  have hs : 0 < s := lt_of_le_of_lt ht0 hts
  have hA : 0 < 1 + ν * s := by positivity
  have hzs : ν * movingZ ν s < 1 := by
    have e : ν * movingZ ν s = ν * s / (1 + ν * s) := by
      unfold movingZ clockA
      rw [mul_div_assoc]
    rw [e, div_lt_one hA]
    linarith
  have hζpos : 0 < ζ := hz.1
  have hνζ : 0 < ν * ζ := mul_pos hν hζpos
  have hd0 : 0 < 1 - ν * (movingZ ν s - ζ) := by nlinarith
  have hne : (1 - ν * (movingZ ν s - ζ)) ≠ 0 := hd0.ne'
  have hc : HasDerivAt (fun ζ' => movingZ ν s - ζ') (-1) ζ :=
    (hasDerivAt_id' ζ).const_sub (movingZ ν s)
  have hd : HasDerivAt (fun ζ' => 1 - ν * (movingZ ν s - ζ')) (-(ν * -1)) ζ :=
    (hc.const_mul ν).const_sub 1
  have hq := hc.div hd hne
  have hfun : revAge ν s = fun ζ' => (movingZ ν s - ζ') / (1 - ν * (movingZ ν s - ζ')) := by
    funext ζ'
    rfl
  have hcl : clockA ν (revAge ν s ζ) = 1 / (1 - ν * (movingZ ν s - ζ)) := by
    unfold clockA revAge ageOfZ
    field_simp
    ring
  have hval : -(clockA ν (revAge ν s ζ)) ^ 2
      = (-1 * (1 - ν * (movingZ ν s - ζ)) - (movingZ ν s - ζ) * -(ν * -1))
          / (1 - ν * (movingZ ν s - ζ)) ^ 2 := by
    rw [hcl]
    field_simp
    ring
  rw [hval, hfun]
  exact hq

end UnforcedLeray.Short.IIIa.AdjE1
