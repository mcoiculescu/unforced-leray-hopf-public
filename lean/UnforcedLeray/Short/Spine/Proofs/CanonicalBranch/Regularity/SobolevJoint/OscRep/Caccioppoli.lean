import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.SobolevJoint.OscRep.EnergyDeriv

/-!


Source of record: `the November 2 reference manuscript`, line 1086 and lines
1134-1140 (local energy estimate for the eigenfunctions of `D`).

## Statement issue (blocks the literal target)

The right-hand side of `OscCaccioppoli` in `Sub/SP_CAN4_4_1.lean` is written without
parentheses:
`2 * ((n : ℝ) + 2) * ∫ r in a'..b', χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2 + 4 * ∫ r in ...`.
The `∫ r in a..b, body` notation takes its body at precedence 60, so the `+ 4 * ∫ ...` term is
absorbed into the body of the first integral. The literal Prop therefore says
`∫ T₁ ≤ 2 (n+2) ∫_{a'}^{b'} (U r + 4 Q) dr = 2 (n+2) P + 8 (n+2) (b'-a') Q`, which is false for
small `b' - a'` (take `φ(r₀) = 0`, `φ'(r₀) = 1` and a narrow bump `χ`). The intended statement
has `(2 * (n+2) * ∫ U) + 4 * ∫ V`. The fix belongs in `Sub/SP_CAN4_4_1.lean` (not edited here):
add parentheses around the first summand. This file proves the intended statement as
`oscCaccioppoli_intended_proof`; once `OscCaccioppoli` is parenthesized, the target is
`oscCaccioppoli_intended_proof`.

## Proof of the intended statement

Write `T₁ = χ² w |φ'|²`, `U = χ² w |φ|²`, `V = χ'² w |φ|²`, and let `G` be the integrand of the
flux derivative `OscEnergyDeriv` with flux `F = w χ² Re(conj φ · φ')`.

1. FTC for `F` on `[a', b']`: `F a' = F b' = 0` because `χ a' = χ b' = 0`, so `∫ G = 0`.
2. Pointwise on `[a', b']`: `½ T₁ - (n+2) U - 2 V ≤ G`. Indeed
   `G - (½ T₁ - (n+2) U - 2 V) = w (½ (χ|φ'|)² + 2 (χ'|φ|)² + 2 χ χ' Re(conj φ φ'))
     + (4/r²) χ² w |φ|²`, and the first bracket is nonnegative because
   `|Re(conj φ φ')| ≤ |φ| |φ'|` (algebraic lemma `oscCaccioppoli_amgm`).
3. Integrate (2) and use (1): `½ ∫T₁ - (n+2) ∫U - 2 ∫V ≤ 0`, which is the claim.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

open UnforcedLeray.Short.Spine

/-- Algebraic core of the Caccioppoli step: if `|R| ≤ p q` then
`½ (u q)² + 2 (v p)² + 2 u v R ≥ 0`. -/
theorem oscCaccioppoli_amgm (u v p q R : ℝ) (hR1 : -(p * q) ≤ R) (hR2 : R ≤ p * q) :
    0 ≤ 1 / 2 * (u * q) ^ 2 + 2 * (v * p) ^ 2 + 2 * u * v * R := by
  rcases le_total 0 (u * v) with h | h
  · nlinarith [sq_nonneg (u * q - 2 * (v * p)), mul_nonneg h (by linarith : (0:ℝ) ≤ R + p * q)]
  · nlinarith [sq_nonneg (u * q + 2 * (v * p)),
      mul_nonneg (by linarith : (0:ℝ) ≤ -(u * v)) (by linarith : (0:ℝ) ≤ p * q - R)]

/-- The Caccioppoli inequality with the right-hand side parenthesized as intended:
`∫ χ² w |φ'|² ≤ 2 (n+2) ∫ χ² w |φ|² + 4 ∫ χ'² w |φ|²` on `[a', b']`. -/
theorem oscCaccioppoli_intended_proof :
    ∀ (n : ℕ) (φ : ℝ → ℂ) (χ : ℝ → ℝ) (a' b' : ℝ), 0 < a' → a' ≤ b' → OscOde n φ →
      ContDiff ℝ ∞ χ → χ a' = 0 → χ b' = 0 →
      ∫ r in a'..b', χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2 ≤
        (2 * ((n : ℝ) + 2) * ∫ r in a'..b', χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2) +
          4 * ∫ r in a'..b', (deriv χ r) ^ 2 * oscWeight r * ‖φ r‖ ^ 2 := by
  intro n φ χ a' b' ha hab hφ hχ hχa hχb
  have hED : OscEnergyDeriv := oscEnergyDeriv_proof
  unfold OscEnergyDeriv at hED
  have hsub : Icc a' b' ⊆ Ioi (0:ℝ) := fun x hx => Set.mem_Ioi.2 (lt_of_lt_of_le ha hx.1)
  have hc0 : ContinuousOn φ (Ioi 0) := hφ.1.continuousOn
  have hc1 : ContinuousOn (deriv φ) (Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 hφ.1).2.continuousOn
  have hχc : Continuous χ := hχ.continuous
  have hχ1 : Continuous (deriv χ) := (contDiff_infty_iff_deriv.1 hχ).2.continuous
  have hw : Continuous oscWeight := by unfold oscWeight; fun_prop
  have hwnn : ∀ x : ℝ, 0 < x → 0 ≤ oscWeight x := fun x hx => by
    unfold oscWeight
    exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) hx.le
  have hq4 : ContinuousOn (fun r : ℝ => 4 / r ^ 2 - 2 - (n : ℝ)) (Ioi 0) := by
    refine ContinuousOn.sub (ContinuousOn.sub ?_ continuousOn_const) continuousOn_const
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro r hr
    exact pow_ne_zero 2 (Set.mem_Ioi.1 hr).ne'
  have hRc : ContinuousOn (fun r => (starRingEnd ℂ (φ r) * deriv φ r).re) (Ioi 0) :=
    Complex.continuous_re.comp_continuousOn
      ((Complex.continuous_conj.comp_continuousOn hc0).mul hc1)
  have hA : ContinuousOn (fun r => χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2) (Ioi 0) := by
    fun_prop
  have hU : ContinuousOn (fun r => χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2) (Ioi 0) := by
    fun_prop
  have hV : ContinuousOn (fun r => deriv χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2) (Ioi 0) := by
    fun_prop
  have hGc : ContinuousOn (fun r => χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2 +
      χ r ^ 2 * oscWeight r * (4 / r ^ 2 - 2 - (n : ℝ)) * ‖φ r‖ ^ 2 +
      2 * oscWeight r * χ r * deriv χ r * (starRingEnd ℂ (φ r) * deriv φ r).re) (Ioi 0) := by
    fun_prop
  have hint : ∀ f : ℝ → ℝ, ContinuousOn f (Ioi 0) → IntervalIntegrable f volume a' b' := by
    intro f hf
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hf.mono hsub
  have hT1i := hint _ hA
  have hUi := hint _ hU
  have hVi := hint _ hV
  have hGi := hint _ hGc
  -- (1) the flux derivative integrates to zero
  have hderiv : ∀ x ∈ uIcc a' b', HasDerivAt
      (fun s : ℝ => oscWeight s * χ s ^ 2 * (starRingEnd ℂ (φ s) * deriv φ s).re)
      (χ x ^ 2 * oscWeight x * ‖deriv φ x‖ ^ 2 +
        χ x ^ 2 * oscWeight x * (4 / x ^ 2 - 2 - (n : ℝ)) * ‖φ x‖ ^ 2 +
        2 * oscWeight x * χ x * deriv χ x * (starRingEnd ℂ (φ x) * deriv φ x).re) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hED n φ χ hφ hχ x (lt_of_lt_of_le ha hx.1)
  have hFTC : ∫ r in a'..b', (χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2 +
      χ r ^ 2 * oscWeight r * (4 / r ^ 2 - 2 - (n : ℝ)) * ‖φ r‖ ^ 2 +
      2 * oscWeight r * χ r * deriv χ r * (starRingEnd ℂ (φ r) * deriv φ r).re) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hGi]
    simp [hχa, hχb]
  -- (2) pointwise bound on [a', b']
  have hpt : ∀ x ∈ Icc a' b',
      1 / 2 * (χ x ^ 2 * oscWeight x * ‖deriv φ x‖ ^ 2) -
        ((n : ℝ) + 2) * (χ x ^ 2 * oscWeight x * ‖φ x‖ ^ 2) -
        2 * (deriv χ x ^ 2 * oscWeight x * ‖φ x‖ ^ 2) ≤
      χ x ^ 2 * oscWeight x * ‖deriv φ x‖ ^ 2 +
        χ x ^ 2 * oscWeight x * (4 / x ^ 2 - 2 - (n : ℝ)) * ‖φ x‖ ^ 2 +
        2 * oscWeight x * χ x * deriv χ x * (starRingEnd ℂ (φ x) * deriv φ x).re := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hw0 := hwnn x hx0
    have hRn : |(starRingEnd ℂ (φ x) * deriv φ x).re| ≤ ‖φ x‖ * ‖deriv φ x‖ := by
      calc |(starRingEnd ℂ (φ x) * deriv φ x).re|
          ≤ ‖starRingEnd ℂ (φ x) * deriv φ x‖ := Complex.abs_re_le_norm _
        _ = ‖φ x‖ * ‖deriv φ x‖ := by rw [norm_mul, Complex.norm_conj]
    obtain ⟨hR1, hR2⟩ := abs_le.1 hRn
    have hkey := oscCaccioppoli_amgm (χ x) (deriv χ x) ‖φ x‖ ‖deriv φ x‖ _ hR1 hR2
    have h2 : 0 ≤ 4 / x ^ 2 * (χ x ^ 2 * oscWeight x * ‖φ x‖ ^ 2) :=
      mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (sq_nonneg _) hw0) (sq_nonneg _))
    nlinarith [mul_nonneg hw0 hkey, h2]
  -- (3) integrate and combine
  have hmono : ∫ r in a'..b', (1 / 2 * (χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2) -
        ((n : ℝ) + 2) * (χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2) -
        2 * (deriv χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2)) ≤
      ∫ r in a'..b', (χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2 +
        χ r ^ 2 * oscWeight r * (4 / r ^ 2 - 2 - (n : ℝ)) * ‖φ r‖ ^ 2 +
        2 * oscWeight r * χ r * deriv χ r * (starRingEnd ℂ (φ r) * deriv φ r).re) :=
    intervalIntegral.integral_mono_on hab
      (((hT1i.const_mul (1 / 2)).sub (hUi.const_mul ((n : ℝ) + 2))).sub (hVi.const_mul 2))
      hGi hpt
  have hsplit : ∫ r in a'..b', (1 / 2 * (χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2) -
        ((n : ℝ) + 2) * (χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2) -
        2 * (deriv χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2)) =
      (1 / 2 * (∫ r in a'..b', χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2)) -
        ((n : ℝ) + 2) * (∫ r in a'..b', χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2) -
        2 * (∫ r in a'..b', deriv χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2) := by
    rw [intervalIntegral.integral_sub
          ((hT1i.const_mul (1 / 2)).sub (hUi.const_mul ((n : ℝ) + 2))) (hVi.const_mul 2),
      intervalIntegral.integral_sub (hT1i.const_mul (1 / 2)) (hUi.const_mul ((n : ℝ) + 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hsplit, hFTC] at hmono
  have e : 2 * ((n : ℝ) + 2) * (∫ r in a'..b', χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2) =
      2 * (((n : ℝ) + 2) * ∫ r in a'..b', χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2) := by ring
  linarith [hmono, e]

/-- The target, now that `OscCaccioppoli` is parenthesized. -/
theorem oscCaccioppoli_proof : UnforcedLeray.Short.Spine.OscCaccioppoli :=
  oscCaccioppoli_intended_proof
