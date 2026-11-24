import UnforcedLeray.Units.B0579
import UnforcedLeray.Lib.ConvIneq.Peetre

/-!
# Centered-cell weight transfer for the Gaussian heat-divergence kernel

For a fixed cylinder, the B0579 radial weight is comparable on the centered cell to the
q-independent axial weight. The lemma below is the exact pointwise transfer needed before applying
Peetre to the Gaussian convolution in the axial variable. Its constant is explicit and may grow
polynomially with `c`; it is intended for fixed-parameter existence only.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.B0579

/-- The axial Japanese bracket, constant along the periodic coordinate. -/
def axialBracket (x : Plane) : ℝ := Real.sqrt (1 + x.2 ^ 2)

theorem axialBracket_rpow (m : ℝ) (x : Plane) :
    axialBracket x ^ m = (1 + x.2 ^ 2) ^ (m / 2) := by
  rw [axialBracket, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 < 1 + x.2 ^ 2).le]
  congr 1
  ring

/-- Axial Peetre inequality, with the translation variable independent of the periodic coordinate. -/
theorem axialBracket_rpow_le_peetre {m : ℝ} (hm : 0 ≤ m) (x y : Plane) :
    axialBracket x ^ m ≤ 2 ^ (m / 2) * axialBracket (x - y) ^ m * axialBracket y ^ m := by
  rw [axialBracket_rpow, axialBracket_rpow, axialBracket_rpow]
  simpa only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, sq_abs] using
    (UnforcedLeray.Conv.one_add_sq_rpow_le m hm x.2 y.2)

/-- The axial weight is dominated by the B0579 radial weight. -/
theorem axialBracket_rpow_le_bracket {m : ℝ} (hm : 0 ≤ m) (x : Plane) :
    axialBracket x ^ m ≤ bracket x ^ m := by
  rw [axialBracket_rpow, bracket_rpow]
  exact Real.rpow_le_rpow (by positivity) (by rw [jb]; nlinarith) (by linarith)

/-- On the centered cell, the B0579 radial weight is bounded by the axial weight with the
explicit finite-cylinder factor. -/
theorem bracket_le_centered_axial {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    {x : Plane} (hx : x ∈ cell c) :
    bracket x ^ m ≤ (1 + c ^ 2 / 4) ^ (m / 2) * axialBracket x ^ m := by
  have hxq : x.1 ^ 2 ≤ c ^ 2 / 4 := by nlinarith [hx.1.1, hx.1.2.le]
  have hbase : jb x ≤ (1 + c ^ 2 / 4) * (1 + x.2 ^ 2) := by
    rw [jb]
    nlinarith
  rw [bracket_rpow, axialBracket_rpow]
  calc
    jb x ^ (m / 2) ≤ ((1 + c ^ 2 / 4) * (1 + x.2 ^ 2)) ^ (m / 2) :=
      Real.rpow_le_rpow (le_of_lt (jb_pos x)) hbase (by linarith)
    _ = (1 + c ^ 2 / 4) ^ (m / 2) * (1 + x.2 ^ 2) ^ (m / 2) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]

/-- On the centered cell, the radial weight at an output point is controlled by the radial weight
at an input point and an axial translation weight. This is the weight comparison behind a
fixed-cylinder weighted Young estimate for the actual Gaussian gradient kernel. -/
theorem bracket_rpow_le_centered_translation {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    {x y : Plane} (hx : x ∈ cell c) (hy : y ∈ cell c) :
    bracket x ^ m ≤
      (2 * (1 + c ^ 2 / 4)) ^ (m / 2) * bracket y ^ m *
        (1 + (x.2 - y.2) ^ 2) ^ (m / 2) := by
  have hxqL : -(c / 2) ≤ x.1 := hx.1.1
  have hxqR : x.1 ≤ c / 2 := hx.1.2.le
  have hyqL : -(c / 2) ≤ y.1 := hy.1.1
  have hyqR : y.1 ≤ c / 2 := hy.1.2.le
  have hxq : x.1 ^ 2 ≤ c ^ 2 / 4 := by nlinarith
  have hyq : 0 ≤ y.1 ^ 2 := sq_nonneg y.1
  have hη' : x.2 = y.2 + (x.2 - y.2) := by ring
  have hax : 1 + x.2 ^ 2 ≤ 2 * (1 + y.2 ^ 2) * (1 + (x.2 - y.2) ^ 2) := by
    rw [hη']
    nlinarith [sq_nonneg (y.2 - (x.2 - y.2)),
      sq_nonneg (y.2 * (x.2 - y.2))]
  have hjb : jb x ≤ 2 * (1 + c ^ 2 / 4) * jb y * (1 + (x.2 - y.2) ^ 2) := by
    rw [jb]
    calc
      1 + x.1 ^ 2 + x.2 ^ 2 ≤ (1 + c ^ 2 / 4) * (1 + x.2 ^ 2) := by nlinarith
      _ ≤ (1 + c ^ 2 / 4) *
          (2 * (1 + y.2 ^ 2) * (1 + (x.2 - y.2) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hax (by positivity)
      _ ≤ 2 * (1 + c ^ 2 / 4) * jb y * (1 + (x.2 - y.2) ^ 2) := by
            have hybase : 1 + y.2 ^ 2 ≤ jb y := by rw [jb]; nlinarith
            rw [show 2 * (1 + c ^ 2 / 4) * jb y * (1 + (x.2 - y.2) ^ 2) =
              (1 + c ^ 2 / 4) * (2 * jb y * (1 + (x.2 - y.2) ^ 2)) by ring]
            gcongr
  have hexp : 0 ≤ m / 2 := by linarith
  have hpow := Real.rpow_le_rpow (le_of_lt (jb_pos x)) hjb hexp
  have hfac : 2 * (1 + c ^ 2 / 4) * jb y * (1 + (x.2 - y.2) ^ 2) =
      (2 * (1 + c ^ 2 / 4)) * (jb y * (1 + (x.2 - y.2) ^ 2)) := by ring
  have hpowSplit : jb x ^ (m / 2) ≤
      (2 ^ (m / 2) * (1 + c ^ 2 / 4) ^ (m / 2)) *
        jb y ^ (m / 2) * (1 + (x.2 - y.2) ^ 2) ^ (m / 2) := by
    have hA : 0 ≤ 1 + c ^ 2 / 4 := by positivity
    have hY : 0 ≤ jb y := (jb_pos y).le
    have hD : 0 ≤ 1 + (x.2 - y.2) ^ 2 := by positivity
    rw [hfac, Real.mul_rpow (mul_nonneg (by norm_num) hA)
        (mul_nonneg hY hD),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hA,
      Real.mul_rpow hY hD] at hpow
    simpa [mul_assoc] using hpow
  have hscale : (2 * (1 + c ^ 2 / 4)) ^ (m / 2) =
      2 ^ (m / 2) * (1 + c ^ 2 / 4) ^ (m / 2) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
  rw [hscale]
  calc
    bracket x ^ m = jb x ^ (m / 2) := bracket_rpow m x
    _ ≤ (2 ^ (m / 2) * (1 + c ^ 2 / 4) ^ (m / 2)) *
          jb y ^ (m / 2) * (1 + (x.2 - y.2) ^ 2) ^ (m / 2) := hpowSplit
    _ = _ := by rw [bracket_rpow m y]

/-- Equivalent comparison in axial-bracket notation, with no cell weight on the translation. -/
theorem bracket_rpow_le_centered_axial_translation {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    {x y : Plane} (hx : x ∈ cell c) (hy : y ∈ cell c) :
    bracket x ^ m ≤
      (2 * (1 + c ^ 2 / 4)) ^ (m / 2) * bracket y ^ m *
        bracket (0, x.2 - y.2) ^ m := by
  simpa [bracket_rpow, jb] using bracket_rpow_le_centered_translation hc hm hx hy

#print axioms bracket_rpow_le_centered_translation
#print axioms bracket_rpow_le_centered_axial_translation
#print axioms axialBracket_rpow_le_bracket
#print axioms bracket_le_centered_axial
#print axioms axialBracket_rpow_le_peetre

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
