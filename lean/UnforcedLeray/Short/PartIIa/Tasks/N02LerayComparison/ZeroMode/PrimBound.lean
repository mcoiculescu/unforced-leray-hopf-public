import UnforcedLeray.Short.PartIIa.Sub.N02_3

/-!


Source of record: `the November 2 reference manuscript`, lines 1731-1732
("Their suprema ... are bounded by `C‖⟨η⟩f‖₂`"). Prop: `ZeroPrimBound` (`Sub/N02_3.lean`).

Plan. Fix `(s, q)` and write `G t := g (s, q, t)`, which is continuous and vanishes for `|t| > L`.

1. `‖∫_0^η G‖ ≤ ∫ ‖G‖` (interval to whole line, nonnegative integrand).
2. For `l > 0` the pointwise AM-GM inequality
   `2x ≤ l (x² + t² x²) + l⁻¹ (1 + t²)⁻¹` (square `(l (1+t²) x - 1)²`) integrates to
   `2 J ≤ l (I₁ + I₂) + l⁻¹ π`, where `J = ∫ ‖G‖`, `I₁ = ∫ ‖G‖²`, `I₂ = ∫ t² ‖G‖²`, and
   `∫ (1 + t²)⁻¹ = π`.
3. Choosing `l = π / J` (if `J > 0`) gives `J² ≤ π (I₁ + I₂) ≤ π (√I₁ + √I₂)²`.

Only real analysis; no Hilbert space.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

namespace ZeroPrimBoundAux

/-- Pointwise AM-GM: `2x ≤ l (x² + t² x²) + l⁻¹ (1 + t²)⁻¹` for `l > 0`. -/
lemma amgm (l x t : ℝ) (hl : 0 < l) :
    2 * x ≤ l * (x ^ 2 + t ^ 2 * x ^ 2) + l⁻¹ * (1 + t ^ 2)⁻¹ := by
  have hu : 0 < 1 + t ^ 2 := by positivity
  have hlu : 0 < l * (1 + t ^ 2) := mul_pos hl hu
  have key : l * (x ^ 2 + t ^ 2 * x ^ 2) + l⁻¹ * (1 + t ^ 2)⁻¹ - 2 * x
      = (l * (1 + t ^ 2) * x - 1) ^ 2 / (l * (1 + t ^ 2)) := by
    field_simp
    ring
  have hnn : 0 ≤ (l * (1 + t ^ 2) * x - 1) ^ 2 / (l * (1 + t ^ 2)) :=
    div_nonneg (sq_nonneg _) hlu.le
  linarith

/-- Compact support from vanishing outside `[-L, L]`. -/
lemma hasCompactSupport_of_zero (L : ℝ) {F : ℝ → ℝ} (hF : ∀ t, L < |t| → F t = 0) :
    HasCompactSupport F :=
  HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc fun t ht => by
    apply hF
    by_contra hle
    exact ht (abs_le.1 (not_lt.1 hle))

/-- Integrability of `‖G‖`, `‖G‖²`, `t² ‖G‖²` for a continuous fiber `G` supported in `[-L, L]`. -/
lemma fiber_integrable (G : ℝ → ℂ) (hG : Continuous G) (L : ℝ)
    (hzero : ∀ t, L < |t| → G t = 0) :
    Integrable (fun t => ‖G t‖) ∧ Integrable (fun t => ‖G t‖ ^ 2) ∧
      Integrable (fun t => t ^ 2 * ‖G t‖ ^ 2) := by
  have hc0 : Continuous (fun t => ‖G t‖) := hG.norm
  have hc1 : Continuous (fun t => ‖G t‖ ^ 2) := hc0.pow 2
  have hc2 : Continuous (fun t : ℝ => t ^ 2 * ‖G t‖ ^ 2) := (continuous_pow 2).mul hc1
  refine ⟨hc0.integrable_of_hasCompactSupport (hasCompactSupport_of_zero L ?_),
    hc1.integrable_of_hasCompactSupport (hasCompactSupport_of_zero L ?_),
    hc2.integrable_of_hasCompactSupport (hasCompactSupport_of_zero L ?_)⟩
  · intro t ht
    simp [hzero t ht]
  · intro t ht
    simp [hzero t ht]
  · intro t ht
    simp [hzero t ht]

/-- Step 1: the primitive is bounded by the total variation (interval to line). -/
lemma norm_primitive_le (G : ℝ → ℂ) (hI : Integrable (fun t => ‖G t‖)) (η : ℝ) :
    ‖∫ t in (0 : ℝ)..η, G t‖ ≤ ∫ t, ‖G t‖ :=
  le_trans intervalIntegral.norm_integral_le_integral_norm_uIoc
    (setIntegral_le_integral hI (ae_of_all _ fun _ => norm_nonneg _))

/-- Step 3 (algebra): from the integrated AM-GM inequality, `J ≤ √π (√I₁ + √I₂)`. -/
lemma alg_step (J I1 I2 : ℝ) (hJ : 0 ≤ J) (hI1 : 0 ≤ I1) (hI2 : 0 ≤ I2)
    (hkey : ∀ l : ℝ, 0 < l → 2 * J ≤ l * (I1 + I2) + l⁻¹ * Real.pi) :
    J ≤ Real.sqrt Real.pi * (Real.sqrt I1 + Real.sqrt I2) := by
  rcases eq_or_lt_of_le hJ with hJz | hJpos
  · rw [← hJz]
    positivity
  · have hpi : 0 < Real.pi := Real.pi_pos
    have hpne : Real.pi ≠ 0 := hpi.ne'
    have hJne : J ≠ 0 := hJpos.ne'
    have hl : 0 < Real.pi / J := div_pos hpi hJpos
    have hk := hkey _ hl
    have hinv : (Real.pi / J)⁻¹ * Real.pi = J := by
      field_simp
    rw [hinv] at hk
    have h3 : J ≤ Real.pi / J * (I1 + I2) := by linarith
    have h5 := mul_le_mul_of_nonneg_right h3 hJ
    have e : Real.pi / J * (I1 + I2) * J = Real.pi * (I1 + I2) := by
      field_simp
    have h4 : J * J ≤ Real.pi * (I1 + I2) := by linarith
    have ha : Real.sqrt I1 ^ 2 = I1 := Real.sq_sqrt hI1
    have hb : Real.sqrt I2 ^ 2 = I2 := Real.sq_sqrt hI2
    have ha0 : 0 ≤ Real.sqrt I1 := Real.sqrt_nonneg I1
    have hb0 : 0 ≤ Real.sqrt I2 := Real.sqrt_nonneg I2
    have hpi2 : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hpi.le
    have hM0 : 0 ≤ Real.sqrt Real.pi * (Real.sqrt I1 + Real.sqrt I2) := by positivity
    rw [mul_self_le_mul_self_iff hJ hM0]
    have e3 : Real.sqrt Real.pi * (Real.sqrt I1 + Real.sqrt I2)
        * (Real.sqrt Real.pi * (Real.sqrt I1 + Real.sqrt I2))
        = (Real.sqrt Real.pi * Real.sqrt Real.pi) * (Real.sqrt I1 + Real.sqrt I2) ^ 2 := by
      ring
    rw [e3, hpi2]
    have hA : Real.pi * Real.sqrt I1 ^ 2 = Real.pi * I1 := by rw [ha]
    have hB : Real.pi * Real.sqrt I2 ^ 2 = Real.pi * I2 := by rw [hb]
    have hC : 0 ≤ Real.pi * (Real.sqrt I1 * Real.sqrt I2) :=
      mul_nonneg hpi.le (mul_nonneg ha0 hb0)
    nlinarith [h4, hA, hB, hC]

/-- The fiber bound for a continuous `G` supported in `[-L, L]`:
`∫ ‖G‖ ≤ √π (√(∫ ‖G‖²) + √(∫ t² ‖G‖²))`. -/
lemma fiber_bound (G : ℝ → ℂ) (hG : Continuous G) (L : ℝ)
    (hzero : ∀ t, L < |t| → G t = 0) :
    ∫ t, ‖G t‖ ≤ Real.sqrt Real.pi *
      (Real.sqrt (∫ t, ‖G t‖ ^ 2) + Real.sqrt (∫ t, t ^ 2 * ‖G t‖ ^ 2)) := by
  obtain ⟨hI0, hI1, hI2⟩ := fiber_integrable G hG L hzero
  have hJ0 : 0 ≤ ∫ t, ‖G t‖ := integral_nonneg fun t => norm_nonneg _
  have hI10 : 0 ≤ ∫ t, ‖G t‖ ^ 2 := integral_nonneg fun t => by positivity
  have hI20 : 0 ≤ ∫ t, t ^ 2 * ‖G t‖ ^ 2 := integral_nonneg fun t => by positivity
  -- Integrated AM-GM, for every `l > 0`.
  have key : ∀ l : ℝ, 0 < l →
      2 * (∫ t, ‖G t‖) ≤ l * ((∫ t, ‖G t‖ ^ 2) + (∫ t, t ^ 2 * ‖G t‖ ^ 2)) + l⁻¹ * Real.pi := by
    intro l hl
    have hR : Integrable (fun t : ℝ =>
        l * (‖G t‖ ^ 2 + t ^ 2 * ‖G t‖ ^ 2) + l⁻¹ * (1 + t ^ 2)⁻¹) :=
      ((hI1.add hI2).const_mul l).add (integrable_inv_one_add_sq.const_mul l⁻¹)
    have hmono : ∫ t, 2 * ‖G t‖ ≤ ∫ t : ℝ,
        (l * (‖G t‖ ^ 2 + t ^ 2 * ‖G t‖ ^ 2) + l⁻¹ * (1 + t ^ 2)⁻¹) :=
      integral_mono (hI0.const_mul 2) hR fun t => amgm l ‖G t‖ t hl
    have e1 : ∫ t, 2 * ‖G t‖ = 2 * ∫ t, ‖G t‖ := integral_const_mul 2 _
    have hf : Integrable (fun t : ℝ => l * (‖G t‖ ^ 2 + t ^ 2 * ‖G t‖ ^ 2)) :=
      (hI1.add hI2).const_mul l
    have hg : Integrable (fun t : ℝ => l⁻¹ * (1 + t ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul l⁻¹
    have e2 : ∫ t : ℝ, (l * (‖G t‖ ^ 2 + t ^ 2 * ‖G t‖ ^ 2) + l⁻¹ * (1 + t ^ 2)⁻¹)
        = l * ((∫ t, ‖G t‖ ^ 2) + (∫ t, t ^ 2 * ‖G t‖ ^ 2)) + l⁻¹ * Real.pi := by
      rw [integral_add hf hg, integral_const_mul l, integral_const_mul l⁻¹,
        integral_add hI1 hI2, integral_univ_inv_one_add_sq]
    linarith
  exact alg_step _ _ _ hJ0 hI10 hI20 key

end ZeroPrimBoundAux

/-- **L1c (primitive: fiber bound).** `ZeroPrimBound` (`Sub/N02_3.lean`). -/
theorem zeroPrimBound : ZeroPrimBound := by
  unfold ZeroPrimBound
  intro g hg hex p
  obtain ⟨s0, s1, L, _, hsup⟩ := hex
  have hgc : Continuous (fun t : ℝ => g (p.1, p.2.1, t)) :=
    hg.continuous.comp (f := fun t : ℝ => (p.1, p.2.1, t)) (by fun_prop)
  have hzero : ∀ t : ℝ, L < |t| → g (p.1, p.2.1, t) = 0 := by
    intro t ht
    by_contra hne
    exact absurd (hsup (p.1, p.2.1, t) hne).2 (not_le.2 ht)
  obtain ⟨hI0, -, -⟩ :=
    ZeroPrimBoundAux.fiber_integrable (fun t => g (p.1, p.2.1, t)) hgc L hzero
  have hstep := ZeroPrimBoundAux.norm_primitive_le (fun t => g (p.1, p.2.1, t)) hI0 p.2.2
  have hfib := ZeroPrimBoundAux.fiber_bound (fun t => g (p.1, p.2.1, t)) hgc L hzero
  simp only [← Real.sqrt_eq_rpow]
  exact le_trans hstep hfib

end UnforcedLeray.Short.PartIIa
