import UnforcedLeray.Short.PartIIIb.Tasks

/-!
# Proof of `epsPow` (target `T_epsPow`; source: `the November 2 reference manuscript`, lines 4109-4124)

Exponent bookkeeping for `NearParameterChoice`. For `p > 0`, `C_* ∈ [c₁, c₂]`, `|r| ≤ r_max`
and `0 < ν ≤ 1`:

* `(C_* ν^r e^{-d₀/ν})^p = C_*^p ν^{rp} e^{-p d₀/ν}` (`Real.mul_rpow`, `Real.rpow_mul`,
  `Real.exp_mul`), and `e^{-p d₀/ν} e^{x/ν} = e^{-(p d₀ - x)/ν}` (`Real.exp_add`).
* `C_*^p ≤ c₂^p` since `0 < C_*`.
* `ν^{rp} = (ν⁻¹)^{-rp} ≤ (ν⁻¹)^{r_max p} ≤ (ν⁻¹)^k` with `k = ⌈r_max p⌉₊`, because
  `ν⁻¹ ≥ 1` and `-rp ≤ r_max p`.

Witnesses: `C = c₂^p`, `k = ⌈r_max p⌉₊`, `ν₀ = 1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

theorem epsPow : UnforcedLeray.Short.PartIIIb.T_epsPow := by
  unfold UnforcedLeray.Short.PartIIIb.T_epsPow
  intro c1 c2 rmax d0 p x hc1 hc12 _hrmax _hd0 hp
  refine ⟨c2 ^ p, ⌈rmax * p⌉₊, 1, one_pos, ?_⟩
  intro ν hν hν1 Cs hCs r hr
  have hCs0 : 0 < Cs := lt_of_lt_of_le hc1 hCs.1
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  have hM1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hB0 : 0 ≤ ν ^ (r * p) := Real.rpow_nonneg hν.le _
  have hc2p : 0 ≤ c2 ^ p := Real.rpow_nonneg hc2.le p
  have hE0 : 0 ≤ Real.exp (-(p * d0 - x) / ν) := (Real.exp_pos _).le
  have hcp : Cs ^ p ≤ c2 ^ p := Real.rpow_le_rpow hCs0.le hCs.2 hp.le
  have hMk : ν ^ (r * p) ≤ ν⁻¹ ^ ⌈rmax * p⌉₊ := by
    have key : ν ^ (r * p) = ν⁻¹ ^ (-(r * p)) := by
      rw [Real.rpow_neg (inv_nonneg.2 hν.le), Real.inv_rpow hν.le, inv_inv]
    have hle1 : -(r * p) ≤ rmax * p := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ r + rmax by linarith [hr.1]) hp.le]
    have hle2 : rmax * p ≤ (⌈rmax * p⌉₊ : ℝ) := Nat.le_ceil _
    calc ν ^ (r * p) = ν⁻¹ ^ (-(r * p)) := key
      _ ≤ ν⁻¹ ^ (rmax * p) := Real.rpow_le_rpow_of_exponent_le hM1 hle1
      _ ≤ ν⁻¹ ^ ((⌈rmax * p⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 hle2
      _ = ν⁻¹ ^ ⌈rmax * p⌉₊ := Real.rpow_natCast _ _
  have hLHS : (Cs * ν ^ r * Real.exp (-d0 / ν)) ^ p * Real.exp (x / ν)
      = Cs ^ p * ν ^ (r * p) * Real.exp (-(p * d0 - x) / ν) := by
    have h1 : (Cs * ν ^ r * Real.exp (-d0 / ν)) ^ p
        = Cs ^ p * ν ^ (r * p) * Real.exp (-d0 / ν * p) := by
      rw [Real.mul_rpow (mul_nonneg hCs0.le (Real.rpow_nonneg hν.le r)) (Real.exp_pos (-d0 / ν)).le,
        Real.mul_rpow hCs0.le (Real.rpow_nonneg hν.le r), ← Real.rpow_mul hν.le r p,
        ← Real.exp_mul]
    have hexp : Real.exp (-d0 / ν * p) * Real.exp (x / ν)
        = Real.exp (-(p * d0 - x) / ν) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h1, mul_assoc (Cs ^ p * ν ^ (r * p)), hexp]
  rw [hLHS]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hcp hMk hB0 hc2p) hE0

end UnforcedLeray.Short.PartIIIb
