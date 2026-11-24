import UnforcedLeray.Short.PartIIIb.Tasks

/-!
# Proof of `T_astarExact` (source: `the November 2 reference manuscript`, lines 5955-5957)

For `0 < ν < 1`, `A_* = ε³ |N_ν| ν^{5+2μ}` with `μ = σ₀ + z/(2|log ν|)` (lines 5936-5946)
equals `e^{-z}/(2‖Cσ‖)`.

* `‖N_ν‖ = e^{λ.re/ν} ν^{-κ.re}`, and `e^{-γ/ν} e^{γ/ν} = 1` with `γ = λ.re`.
* The powers of `ν` combine: the exponents add to `z/|log ν|`, and `ν^t = exp(log ν · t)`
  with `log ν · (z/(-log ν)) = -z` since `log ν < 0`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

theorem astarExact : UnforcedLeray.Short.PartIIIb.T_astarExact := by
  unfold T_astarExact
  intro lam κ Cσ σ₀ ν z _hC hν0 hν1
  have hlog : Real.log ν < 0 := Real.log_neg hν0 hν1
  have hLne : Real.log ν ≠ 0 := ne_of_lt hlog
  have hL : |Real.log ν| = -Real.log ν := abs_of_neg hlog
  have hN : ‖Nnu lam κ ν‖ = Real.exp (lam.re / ν) * ν ^ (-κ.re) := by
    unfold Nnu
    rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hν0,
      Complex.div_ofReal_re, Complex.neg_re]
  have hexp : Real.exp (-lam.re / ν) * Real.exp (lam.re / ν) = 1 := by
    rw [← Real.exp_add]
    have h0 : -lam.re / ν + lam.re / ν = 0 := by ring
    rw [h0, Real.exp_zero]
  have hpow : ν ^ (κ.re - 5 - 2 * σ₀) * ν ^ (-κ.re) *
      ν ^ (5 + 2 * (σ₀ + z / (2 * |Real.log ν|))) = Real.exp (-z) := by
    rw [← Real.rpow_add hν0, ← Real.rpow_add hν0, Real.rpow_def_of_pos hν0, hL]
    congr 1
    have hsum : (κ.re - 5 - 2 * σ₀) + -κ.re + (5 + 2 * (σ₀ + z / (2 * -Real.log ν)))
        = z / (-Real.log ν) := by ring
    have hmul : Real.log ν * (z / (-Real.log ν)) = -z := by
      rw [mul_div_assoc', div_eq_iff (neg_ne_zero.mpr hLne)]
      ring
    rw [hsum, hmul]
  unfold Astar epsCube muWin
  rw [hN]
  have key : Real.exp (-lam.re / ν) * ν ^ (κ.re - 5 - 2 * σ₀) / (2 * ‖Cσ‖) *
      (Real.exp (lam.re / ν) * ν ^ (-κ.re)) *
      ν ^ (5 + 2 * (σ₀ + z / (2 * |Real.log ν|))) =
      (Real.exp (-lam.re / ν) * Real.exp (lam.re / ν)) *
      (ν ^ (κ.re - 5 - 2 * σ₀) * ν ^ (-κ.re) *
      ν ^ (5 + 2 * (σ₀ + z / (2 * |Real.log ν|)))) / (2 * ‖Cσ‖) := by
    ring
  rw [key, hexp, hpow, one_mul]

end UnforcedLeray.Short.PartIIIb
