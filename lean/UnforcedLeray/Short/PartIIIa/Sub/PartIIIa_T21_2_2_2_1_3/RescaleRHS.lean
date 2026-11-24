import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.ChangeVar

/-!
# Part III-a, `PartIII-a:T21/2/2/2/1/3/7`: the right side `RescaleRHS` of the adjoint identity

Source `the November 2 reference manuscript` (SP), lines 3052-3058.
With `Ẽ(y) = a² E(√a y)` one has `∂_jẼ(y) = a² √a (∂_jE)(√a y)` for every `E` (both sides are
`0` when `E` is not differentiable at `√a y`, since then `Ẽ` is not differentiable at `y`).
The complex change of variables (`rescaleRHS_cellScaleC`) then gives the constant
`a · a⁻¹ = 1` on the right-hand side, after the factor `a⁻¹ a² = a` on the left.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- Change of variables `x = √a y` on the moving cell, for a complex-valued integrand. -/
theorem rescaleRHS_cellScaleC (c a : ℝ) (ha : 0 < a) (G : ℝ × ℝ → ℂ) :
    ∫ y in B0579.cell (cellLen c a), G (Real.sqrt a * y.1, Real.sqrt a * y.2) =
      ((a⁻¹ : ℝ) : ℂ) * ∫ x in B0579.cell c, G x := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure (ℝ × ℝ))) G
    (B0579.cell (cellLen c a)) hs
  rw [sqrt_smul_cell c a ha] at h
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hfin, Real.sq_sqrt ha.le, Complex.real_smul] at h
  exact h

/-- Chain rule for the dilated and scaled function `Ẽ(y) = k E(s y)`:
`∂_j Ẽ(y) = k s (∂_jE)(s y)` for every `E` (`k ≠ 0`); both sides vanish where `E` is not
differentiable at `s y`. -/
theorem rescaleRHS_pd (E : ℝ × ℝ → ℝ) (s k : ℝ) (hs : 0 < s) (hk : k ≠ 0) (j : Fin 2)
    (y : ℝ × ℝ) :
    B0579.pd j (fun y : ℝ × ℝ => k * E (s * y.1, s * y.2)) y =
      k * (s * B0579.pd j E (s * y.1, s * y.2)) := by
  have hpt : ∀ z : ℝ × ℝ, s • z = (s * z.1, s * z.2) := fun z => by ext <;> simp
  have hfun : (fun y : ℝ × ℝ => k * E (s * y.1, s * y.2)) = fun z : ℝ × ℝ => k * E (s • z) := by
    funext z
    rw [hpt z]
  by_cases hE : DifferentiableAt ℝ E (s • y)
  · have hg : HasFDerivAt (fun z : ℝ × ℝ => s • z) (s • ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
      (hasFDerivAt_id y).const_smul s
    have hc' : HasFDerivAt (fun z : ℝ × ℝ => k * E (s • z))
        (k • ((fderiv ℝ E (s • y)).comp (s • ContinuousLinearMap.id ℝ (ℝ × ℝ)))) y :=
      (hE.hasFDerivAt.comp y hg).const_mul k
    unfold B0579.pd
    rw [hfun, hc'.fderiv, hpt y]
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      map_smul, smul_eq_mul]
  · have hE' : ¬ DifferentiableAt ℝ E (s * y.1, s * y.2) := by
      rw [← hpt y]
      exact hE
    have h0 : fderiv ℝ E (s * y.1, s * y.2) = 0 := fderiv_zero_of_not_differentiableAt hE'
    have hnd : ¬ DifferentiableAt ℝ (fun y : ℝ × ℝ => k * E (s * y.1, s * y.2)) y := by
      intro hd
      apply hE
      have hd2 : DifferentiableAt ℝ (fun y : ℝ × ℝ => k * E (s * y.1, s * y.2))
          ((s⁻¹ : ℝ) • (s • y)) := by
        rw [inv_smul_smul₀ hs.ne' y]
        exact hd
      have hEeq : E = fun p : ℝ × ℝ =>
          k⁻¹ * (fun y : ℝ × ℝ => k * E (s * y.1, s * y.2)) ((s⁻¹ : ℝ) • p) := by
        funext p
        have e1 : s * (s⁻¹ * p.1) = p.1 := by field_simp
        have e2 : s * (s⁻¹ * p.2) = p.2 := by field_simp
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, e1, e2, Prod.mk.eta]
        rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]
      rw [hEeq]
      exact (hd2.comp (s • y) (differentiableAt_id.const_smul (s⁻¹ : ℝ))).const_mul k⁻¹
    have h1 : fderiv ℝ (fun y : ℝ × ℝ => k * E (s * y.1, s * y.2)) y = 0 :=
      fderiv_zero_of_not_differentiableAt hnd
    unfold B0579.pd
    rw [h1, h0]
    simp

/-- **`RescaleRHS`** (SP 3052-3058): with `Ẽ(y) = a²E(√a y)` and `Φ̃(y) = a⁻¹Φ(√a y)`, the
left integral over `C_{c/√a}` equals the right integral over `C_c`. -/
theorem rescaleRHS : UnforcedLeray.Short.IIIa.E0.RescaleRHS := by
  intro c a hc ha E Φ u
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsne : Real.sqrt a ≠ 0 := hs.ne'
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hk : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
  -- change of variables on the right-hand integrand
  have hC := rescaleRHS_cellScaleC c a ha
    (fun x => Φ x * ((Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 0 *
        B0579.pd 0 E x + Real.sqrt a * u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 1 *
        B0579.pd 1 E x : ℝ) : ℂ))
  simp only [mul_div_cancel_left₀ _ hsne, Prod.mk.eta] at hC
  -- the chain rule for the rescaled `E`
  simp only [rescaleRHS_pd E (Real.sqrt a) (a ^ 2) hs hk]
  -- pointwise: the left integrand is `a` times the transported right integrand
  have key : ∀ y : ℝ × ℝ,
      ((a⁻¹ : ℝ) : ℂ) * Φ (Real.sqrt a * y.1, Real.sqrt a * y.2) *
          ((u y 0 * (a ^ 2 * (Real.sqrt a * B0579.pd 0 E (Real.sqrt a * y.1, Real.sqrt a * y.2))) +
            u y 1 * (a ^ 2 * (Real.sqrt a * B0579.pd 1 E (Real.sqrt a * y.1, Real.sqrt a * y.2))) :
              ℝ) : ℂ) =
        (a : ℂ) * (Φ (Real.sqrt a * y.1, Real.sqrt a * y.2) *
          ((Real.sqrt a * u y 0 * B0579.pd 0 E (Real.sqrt a * y.1, Real.sqrt a * y.2) +
            Real.sqrt a * u y 1 * B0579.pd 1 E (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) := by
    intro y
    push_cast
    field_simp
  simp only [key]
  have hinv : (a : ℂ) * ((a⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    exact mul_inv_cancel₀ hac
  rw [integral_const_mul, hC, ← mul_assoc, hinv, one_mul]

end UnforcedLeray.Short.IIIa.E0
