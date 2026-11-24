import UnforcedLeray.Short.PartIIIb.Concrete.YoungBlocks

/-!
# The residual `δ_c` is small (source 4376-4411, residual bounds 4390-4395)

Proves `ConcreteYF.DeltaCSmall`: for `c = ν^{-2}` and `P_ν = K ν^{-p}`,
`δ_c = C_Σ (c^{-2} + P_ν e^{C_Σ/ν - b_Σ c²}) ≤ C ν²` for all small `ν > 0`.

Argument. Put `u = ν⁻¹ ≥ 1`. Then `c⁻¹² = ν⁴ ≤ ν²` for `ν ≤ 1`, and the exponential term is
`u^p exp(C_Σ u - b_Σ u⁴)`. For `u ≥ 1 + 2|C_Σ|/b_Σ` one has `C_Σ u - b_Σ u⁴ ≤ -(b_Σ/2) u⁴`,
and `exp x ≥ x^N/N!` (with `N = p + 2`) gives `u^{p+2} exp(C_Σ u - b_Σ u⁴) ≤ N!/(b_Σ/2)^N`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

/-- `ν^{-2} = (ν⁻¹)²` for `ν > 0`. -/
lemma rpow_neg_two_eq_inv_sq (ν : ℝ) (hν : 0 < ν) : ν ^ (-2 : ℝ) = (ν⁻¹) ^ 2 := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hν.le, Real.rpow_two, inv_pow]

/-- Unfolding `δ_c` at `P_ν = K ν^{-p}`, `c = ν^{-2}`. -/
lemma deltaC_eq_explicit (K CS bS : ℝ) (p : ℕ) (ν : ℝ) (hν : 0 < ν) :
    deltaC (K * ν⁻¹ ^ p) CS bS ν (ν ^ (-2 : ℝ)) =
      CS * (ν ^ 4 + K * ν⁻¹ ^ p * Real.exp (CS / ν - bS * (ν⁻¹) ^ 4)) := by
  unfold deltaC deltaBase
  rw [rpow_neg_two_eq_inv_sq ν hν]
  have h0 : ((ν⁻¹) ^ 2)⁻¹ = ν ^ 2 := by
    rw [inv_pow, inv_inv]
  have h1 : ((ν⁻¹) ^ 2)⁻¹ ^ 2 = ν ^ 4 := by
    rw [h0]; ring
  have h2 : bS * ((ν⁻¹) ^ 2) ^ 2 = bS * (ν⁻¹) ^ 4 := by ring
  rw [h1, h2, div_eq_mul_inv]

/-- Key estimate in the variable `u = ν⁻¹`. -/
lemma key_exp_bound (CS bS : ℝ) (hb : 0 < bS) (p : ℕ) (u : ℝ)
    (hu : 1 + 2 * |CS| / bS ≤ u) :
    u ^ p * Real.exp (CS * u - bS * u ^ 4) * u ^ 2 * (bS / 2) ^ (p + 2) ≤
      (Nat.factorial (p + 2) : ℝ) := by
  have hdiv : 0 ≤ 2 * |CS| / bS := div_nonneg (by positivity) hb.le
  have hu1 : 1 ≤ u := by linarith
  have hupos : 0 < u := by linarith
  -- `2|C_Σ| ≤ b_Σ u`
  have hbu : 2 * |CS| ≤ bS * u := by
    have h1 : 2 * |CS| / bS ≤ u - 1 := by linarith
    have h2 : 2 * |CS| ≤ (u - 1) * bS := (div_le_iff₀ hb).mp h1
    have h3 : bS * u = (u - 1) * bS + bS := by ring
    nlinarith
  -- `u ≤ u³`
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have hu3 : u ≤ u ^ 3 := by
    have e : u ^ 3 = u * u ^ 2 := by ring
    rw [e]
    nlinarith
  have h3 : 2 * |CS| ≤ bS * u ^ 3 :=
    le_trans hbu (mul_le_mul_of_nonneg_left hu3 hb.le)
  have h4 : 2 * |CS| * u ≤ bS * u ^ 4 := by
    have := mul_le_mul_of_nonneg_left h3 hupos.le
    have e : u * (bS * u ^ 3) = bS * u ^ 4 := by ring
    nlinarith
  have h5 : CS * u ≤ |CS| * u := mul_le_mul_of_nonneg_right (le_abs_self CS) hupos.le
  have hA : CS * u - bS * u ^ 4 ≤ -((bS / 2) * u ^ 4) := by nlinarith
  have hexp1 : Real.exp (CS * u - bS * u ^ 4) ≤ Real.exp (-((bS / 2) * u ^ 4)) :=
    Real.exp_le_exp.mpr hA
  -- `x = (b/2) u⁴`, and `exp(-x) x^N ≤ N!`
  have hx0 : 0 ≤ (bS / 2) * u ^ 4 := by positivity
  have hF : (0 : ℝ) < (Nat.factorial (p + 2) : ℝ) := by positivity
  have hfac : ((bS / 2) * u ^ 4) ^ (p + 2) / (Nat.factorial (p + 2) : ℝ)
      ≤ Real.exp ((bS / 2) * u ^ 4) :=
    Real.pow_div_factorial_le_exp _ hx0 (p + 2)
  have h4' : ((bS / 2) * u ^ 4) ^ (p + 2) ≤
      Real.exp ((bS / 2) * u ^ 4) * (Nat.factorial (p + 2) : ℝ) :=
    (div_le_iff₀ hF).mp hfac
  have hexp_neg : Real.exp (-((bS / 2) * u ^ 4)) * Real.exp ((bS / 2) * u ^ 4) = 1 := by
    rw [← Real.exp_add]; simp
  have hE0 : 0 ≤ Real.exp (CS * u - bS * u ^ 4) := (Real.exp_pos _).le
  have h6 : Real.exp (CS * u - bS * u ^ 4) * ((bS / 2) * u ^ 4) ^ (p + 2) ≤
      (Nat.factorial (p + 2) : ℝ) := by
    calc Real.exp (CS * u - bS * u ^ 4) * ((bS / 2) * u ^ 4) ^ (p + 2)
        ≤ Real.exp (-((bS / 2) * u ^ 4)) * ((bS / 2) * u ^ 4) ^ (p + 2) :=
          mul_le_mul_of_nonneg_right hexp1 (by positivity)
      _ ≤ Real.exp (-((bS / 2) * u ^ 4)) *
            (Real.exp ((bS / 2) * u ^ 4) * (Nat.factorial (p + 2) : ℝ)) :=
          mul_le_mul_of_nonneg_left h4' (Real.exp_pos _).le
      _ = (Real.exp (-((bS / 2) * u ^ 4)) * Real.exp ((bS / 2) * u ^ 4)) *
            (Nat.factorial (p + 2) : ℝ) := by ring
      _ = (Nat.factorial (p + 2) : ℝ) := by rw [hexp_neg, one_mul]
  -- `x^N = (b/2)^N u^{4N}`
  have hx_pow : ((bS / 2) * u ^ 4) ^ (p + 2) = (bS / 2) ^ (p + 2) * u ^ (4 * (p + 2)) := by
    rw [mul_pow, ← pow_mul]
  have hu_le : u ^ (p + 2) ≤ u ^ (4 * (p + 2)) := pow_le_pow_right₀ hu1 (by omega)
  have hbN : (0 : ℝ) ≤ (bS / 2) ^ (p + 2) := by positivity
  calc u ^ p * Real.exp (CS * u - bS * u ^ 4) * u ^ 2 * (bS / 2) ^ (p + 2)
      = u ^ (p + 2) * Real.exp (CS * u - bS * u ^ 4) * (bS / 2) ^ (p + 2) := by ring
    _ ≤ u ^ (4 * (p + 2)) * Real.exp (CS * u - bS * u ^ 4) * (bS / 2) ^ (p + 2) := by
          gcongr
    _ = Real.exp (CS * u - bS * u ^ 4) * ((bS / 2) ^ (p + 2) * u ^ (4 * (p + 2))) := by ring
    _ = Real.exp (CS * u - bS * u ^ 4) * ((bS / 2) * u ^ 4) ^ (p + 2) := by rw [hx_pow]
    _ ≤ (Nat.factorial (p + 2) : ℝ) := h6

end ConcreteYF

/-- `δ_c ≤ C ν²` for small `ν` (source 4390-4395). -/
theorem deltaCSmall_holds : ConcreteYF.DeltaCSmall := by
  intro CS bS K p hb
  have hdiv : 0 ≤ 2 * |CS| / bS := div_nonneg (by positivity) hb.le
  set M : ℝ := 1 + 2 * |CS| / bS with hMdef
  have hM : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  set D : ℝ := (Nat.factorial (p + 2) : ℝ) / (bS / 2) ^ (p + 2) with hD
  refine ⟨|CS| * (1 + |K| * D), M⁻¹, inv_pos.mpr hM, ?_⟩
  intro ν hν hνle
  have hνM : M ≤ ν⁻¹ := by
    have := inv_anti₀ hν hνle
    rwa [inv_inv] at this
  have hu : 1 + 2 * |CS| / bS ≤ ν⁻¹ := hνM
  have hν1 : ν ≤ 1 := by
    have h1 : 1 ≤ ν⁻¹ := le_trans hM1 hνM
    have h2 : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν.ne'
    nlinarith [mul_le_mul_of_nonneg_left h1 hν.le]
  rw [ConcreteYF.deltaC_eq_explicit K CS bS p ν hν]
  set u : ℝ := ν⁻¹ with hudef
  have hupos : 0 < u := inv_pos.mpr hν
  have hkey := ConcreteYF.key_exp_bound CS bS hb p u hu
  have hkey' : u ^ p * Real.exp (CS * u - bS * u ^ 4) * u ^ 2 ≤ D := by
    rw [hD, le_div_iff₀ (by positivity)]
    exact hkey
  have hyexp : CS / ν - bS * u ^ 4 = CS * u - bS * u ^ 4 := by
    rw [hudef, div_eq_mul_inv]
  rw [hyexp, show K * u ^ p * Real.exp (CS * u - bS * u ^ 4)
      = K * (u ^ p * Real.exp (CS * u - bS * u ^ 4)) from mul_assoc _ _ _]
  set E : ℝ := Real.exp (CS * u - bS * u ^ 4) with hEdef
  have hP : 0 ≤ u ^ p * E := by positivity
  have hνu : u * ν = 1 := by rw [hudef]; exact inv_mul_cancel₀ hν.ne'
  have hsq : u ^ 2 * ν ^ 2 = 1 := by
    rw [← mul_pow, hνu, one_pow]
  have hE : u ^ p * E = (u ^ p * E * u ^ 2) * ν ^ 2 := by
    calc u ^ p * E = u ^ p * E * (u ^ 2 * ν ^ 2) := by rw [hsq, mul_one]
      _ = (u ^ p * E * u ^ 2) * ν ^ 2 := by ring
  have hE' : u ^ p * E ≤ D * ν ^ 2 := by
    rw [hE]
    exact mul_le_mul_of_nonneg_right hkey' (sq_nonneg ν)
  have hX : |ν ^ 4 + K * (u ^ p * E)| ≤ ν ^ 4 + |K| * (D * ν ^ 2) := by
    have h := abs_add_le (ν ^ 4) (K * (u ^ p * E))
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ν ^ 4), abs_mul, abs_of_nonneg hP] at h
    nlinarith [mul_le_mul_of_nonneg_left hE' (abs_nonneg K)]
  have hν4 : ν ^ 4 ≤ ν ^ 2 := by
    have h1 : ν ^ 2 ≤ 1 := by nlinarith
    calc ν ^ 4 = ν ^ 2 * ν ^ 2 := by ring
      _ ≤ ν ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = ν ^ 2 := mul_one _
  have hbound : ν ^ 4 + |K| * (D * ν ^ 2) ≤ (1 + |K| * D) * ν ^ 2 := by
    have e : (1 + |K| * D) * ν ^ 2 = ν ^ 2 + |K| * (D * ν ^ 2) := by ring
    rw [e]; linarith
  calc CS * (ν ^ 4 + K * (u ^ p * E))
      ≤ |CS * (ν ^ 4 + K * (u ^ p * E))| := le_abs_self _
    _ = |CS| * |ν ^ 4 + K * (u ^ p * E)| := abs_mul _ _
    _ ≤ |CS| * (ν ^ 4 + |K| * (D * ν ^ 2)) :=
        mul_le_mul_of_nonneg_left (le_trans hX le_rfl) (abs_nonneg CS)
    _ ≤ |CS| * ((1 + |K| * D) * ν ^ 2) := mul_le_mul_of_nonneg_left hbound (abs_nonneg CS)
    _ = |CS| * (1 + |K| * D) * ν ^ 2 := by ring

end UnforcedLeray.Short.PartIIIb
