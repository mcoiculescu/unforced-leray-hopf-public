import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, task `expPowAbsorb`: absorbing the age power into the exponential

Source of record: `the November 2 reference manuscript`, lines 439-446
(`sct:fluctuation`, route step (iv)): `s^k e^{-κνs/c²} ≤ P e^{-κνs/(2c²)}`, with the polynomial
factor in `c, ν⁻¹` placed into `polyConst`.

Target: `ExpPowAbsorb` (`Sub/R02_2.lean`): for `κ > 0`, `k : ℕ` there are `C ≥ 0`, `N` with
`s^k exp(-(κνs/c²)) ≤ polyConst C N ν c * exp(-(κ/2 νs/c²))` for `0 < ν`, `0 < c`, `0 ≤ s`.

Proof: with `A = κν/c²` and `x = As/2`, `x^k/k! ≤ e^x` gives `s^k ≤ k! (2/A)^k e^{As/2}`, hence
`s^k e^{-As} ≤ k! (2/A)^k e^{-As/2}`. Finally `(2/A)^k = (2/κ)^k (c²)^k (ν⁻¹)^k ≤ (2/κ)^k X^{3k}`
with `X = 1 + c + ν⁻¹`, since `c² ≤ X²` and `ν⁻¹ ≤ X`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- Core estimate: for `A > 0` and `s ≥ 0`, `s^k e^{-As} ≤ k! (2/A)^k e^{-As/2}`. -/
theorem expPowAbsorb_core (A s : ℝ) (k : ℕ) (hA : 0 < A) (hs : 0 ≤ s) :
    s ^ k * Real.exp (-(A * s)) ≤
      (Nat.factorial k : ℝ) * (2 / A) ^ k * Real.exp (-(A * s / 2)) := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hx : 0 ≤ A * s / 2 := by positivity
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hpow : (A * s / 2) ^ k ≤ (Nat.factorial k : ℝ) * Real.exp (A * s / 2) := by
    have h := Real.pow_div_factorial_le_exp (A * s / 2) hx k
    rw [div_le_iff₀ hfac] at h
    linarith [mul_comm (Real.exp (A * s / 2)) (Nat.factorial k : ℝ)]
  have hsB : (A * s / 2) * (2 / A) = s := by
    field_simp
  have hkey : s ^ k = (A * s / 2) ^ k * (2 / A) ^ k := by
    rw [← mul_pow, hsB]
  have hexp : Real.exp (A * s / 2) * Real.exp (-(A * s)) = Real.exp (-(A * s / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc s ^ k * Real.exp (-(A * s))
      = (A * s / 2) ^ k * (2 / A) ^ k * Real.exp (-(A * s)) := by rw [hkey]
    _ ≤ ((Nat.factorial k : ℝ) * Real.exp (A * s / 2)) * (2 / A) ^ k * Real.exp (-(A * s)) := by
        gcongr
    _ = (Nat.factorial k : ℝ) * (2 / A) ^ k * (Real.exp (A * s / 2) * Real.exp (-(A * s))) := by
        ring
    _ = (Nat.factorial k : ℝ) * (2 / A) ^ k * Real.exp (-(A * s / 2)) := by rw [hexp]

/-- **Absorbing a power of the age into the exponential** (`ExpPowAbsorb`, source lines 439-446):
halve `κ`, at the price of the polynomial `k! (2/κ)^k (1 + c + ν⁻¹)^{3k}`. -/
theorem expPowAbsorb : ExpPowAbsorb := by
  unfold ExpPowAbsorb
  intro κ k hκ
  refine ⟨(Nat.factorial k : ℝ) * (2 / κ) ^ k, 3 * k, by positivity, ?_⟩
  intro ν c s hν hc hs
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hν0 : ν ≠ 0 := ne_of_gt hν
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hA : 0 < κ * ν / c ^ 2 := by positivity
  have hcore := expPowAbsorb_core (κ * ν / c ^ 2) s k hA hs
  rw [show -(κ * ν * s / c ^ 2) = -(κ * ν / c ^ 2 * s) by ring,
    show -(κ / 2 * ν * s / c ^ 2) = -(κ * ν / c ^ 2 * s / 2) by ring]
  unfold polyConst
  have hinvpos : 0 < ν⁻¹ := inv_pos.mpr hν
  have hcX : c ≤ 1 + c + ν⁻¹ := by linarith
  have hinv : ν⁻¹ ≤ 1 + c + ν⁻¹ := by linarith
  have hc2 : c ^ 2 ≤ (1 + c + ν⁻¹) ^ 2 := pow_le_pow_left₀ hc.le hcX 2
  have hpowle : (c ^ 2) ^ k * (ν⁻¹) ^ k ≤ (1 + c + ν⁻¹) ^ (3 * k) := by
    have h1 : (c ^ 2) ^ k ≤ ((1 + c + ν⁻¹) ^ 2) ^ k :=
      pow_le_pow_left₀ (by positivity) hc2 k
    have h2 : (ν⁻¹) ^ k ≤ (1 + c + ν⁻¹) ^ k :=
      pow_le_pow_left₀ (by positivity) hinv k
    calc (c ^ 2) ^ k * (ν⁻¹) ^ k
        ≤ ((1 + c + ν⁻¹) ^ 2) ^ k * (1 + c + ν⁻¹) ^ k :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (1 + c + ν⁻¹) ^ (3 * k) := by
          rw [← pow_mul, ← pow_add, show 2 * k + k = 3 * k by ring]
  have hB : (2 / (κ * ν / c ^ 2)) ^ k = (2 / κ) ^ k * ((c ^ 2) ^ k * (ν⁻¹) ^ k) := by
    have h : 2 / (κ * ν / c ^ 2) = (2 / κ) * (c ^ 2 * ν⁻¹) := by
      field_simp
    rw [h, mul_pow, mul_pow]
  have hE : 0 ≤ Real.exp (-(κ * ν / c ^ 2 * s / 2)) := (Real.exp_pos _).le
  calc s ^ k * Real.exp (-(κ * ν / c ^ 2 * s))
      ≤ (Nat.factorial k : ℝ) * (2 / (κ * ν / c ^ 2)) ^ k *
          Real.exp (-(κ * ν / c ^ 2 * s / 2)) := hcore
    _ = (Nat.factorial k : ℝ) * (2 / κ) ^ k * ((c ^ 2) ^ k * (ν⁻¹) ^ k) *
          Real.exp (-(κ * ν / c ^ 2 * s / 2)) := by
        rw [hB]
        ring
    _ ≤ (Nat.factorial k : ℝ) * (2 / κ) ^ k * (1 + c + ν⁻¹) ^ (3 * k) *
          Real.exp (-(κ * ν / c ^ 2 * s / 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpowle (by positivity)) hE

end UnforcedLeray.Short.PartIIa
