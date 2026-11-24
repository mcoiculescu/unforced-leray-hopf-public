import UnforcedLeray.Short.PartIIIa.T08_ScalingJaInvDual
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint

/-!
# `PartIII-a:T21/2/2/3/2/4/3`: scaling of the kernel Biot-Savart relation

For `R > 0`, `ψ' = ψ(R⁻¹·)` and `u' = R·u(R⁻¹·)` on the cell `C_c` when `(ψ, u)` solve the
kernel Biot-Savart relation on `C_{c/R}`. The three clauses of `IsKernelBiotSavart` are:

* the horizontal mean: `Γ' = ∫_{C_c} ψ' = R² Γ`, and `meanShear c (R²Γ) x = R meanShear (c/R) Γ (R⁻¹x)`;
* the `L²` clause, by the change of variables `x = R y` on the cell (`MemLp` of the composition with
  a dilation, through the indicator of the cell);
* the divergence and curl clauses, by the change of variables `x = R y` and the dilated tests
  `y ↦ φ(R y)` (`T08.isCylTest_dilate`, `T08.pd_dilate`).

Note: the statement uses `IsKernelBiotSavart` (namespace `UnforcedLeray.Short.IIIa`, defined in
`Clock/WeakSmoothing/Adjoint.lean`); there is no `B0579.IsKernelBiotSavart` declaration.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- Real version of the change of variables `x = R y` on a cell (from `T08.integral_cell_scale`). -/
theorem integral_cell_scale_real {d R : ℝ} (hR : 0 < R) (F : ℝ × ℝ → ℝ) :
    ∫ x in B0579.cell (d * R), F x = R ^ 2 * ∫ y in B0579.cell d, F (R • y) := by
  have h := T08.integral_cell_scale (d := d) hR (fun x => (F x : ℂ))
  simp only [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The mean of the rescaled field: `∫_{C_c} ψ(R⁻¹x) dx = R² ∫_{C_{c/R}} ψ`. -/
theorem cell_integral_comp_inv_real {c R : ℝ} (hR : 0 < R) (ψ : ℝ × ℝ → ℝ) :
    ∫ x in B0579.cell c, ψ (R⁻¹ • x) = R ^ 2 * ∫ y in B0579.cell (c / R), ψ y := by
  have h := integral_cell_scale_real (d := c / R) (R := R) hR (fun x => ψ (R⁻¹ • x))
  rw [div_mul_cancel₀ c hR.ne'] at h
  simpa [inv_smul_smul₀ hR.ne'] using h

/-- The mean shear is carried by the dilation: `meanShear c (R²Γ) x = R meanShear (c/R) Γ (R⁻¹x)`. -/
theorem meanShear_rescale_aux {c R Γ : ℝ} (hR : 0 < R) (x : ℝ × ℝ) (j : Fin 2) :
    meanShear c (R ^ 2 * Γ) x j = R * meanShear (c / R) Γ (R⁻¹ • x) j := by
  by_cases hj : j = 0
  · subst hj
    have hs : Real.sign (R⁻¹ • x).2 = Real.sign x.2 := by
      simp only [Prod.smul_snd, smul_eq_mul]
      rcases lt_trichotomy x.2 0 with h | h | h
      · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg (inv_pos.2 hR) h)]
      · rw [h, mul_zero]
      · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos (inv_pos.2 hR) h)]
    unfold meanShear
    rw [hs]
    rcases eq_or_ne c 0 with hc | hc
    · subst hc
      simp
    · simp only [ite_true]
      field_simp
  · unfold meanShear
    simp [hj]

/-- Dilation of an `L²` function on a cell, with the indicator of the cell. -/
theorem memLp_cell_comp {c R : ℝ} (hR : 0 < R) {g : ℝ × ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell (c / R)))) :
    MemLp (fun x => g (R⁻¹ • x)) 2 (volume.restrict (B0579.cell c)) := by
  have hmem : ∀ x : ℝ × ℝ, R⁻¹ • x ∈ B0579.cell (c / R) ↔ x ∈ B0579.cell c := by
    intro x
    have h := T08.smul_mem_cell_iff_div (d := c / R) (R := R⁻¹) (inv_pos.2 hR) x
    have e : c / R / R⁻¹ = c := by field_simp
    rw [e] at h
    exact h
  set G : ℝ × ℝ → ℝ := (B0579.cell (c / R)).indicator g with hGdef
  have hG : MemLp G 2 volume := (memLp_indicator_iff_restrict (B0579.measurableSet_cell _)).2 hg
  have hG2 : Integrable (fun x => ‖G x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hG.1).1 hG
  have hI : Integrable (fun x => ‖G (R⁻¹ • x)‖ ^ 2) volume :=
    hG2.comp_smul (inv_ne_zero hR.ne')
  have hA : AEStronglyMeasurable (fun x => G (R⁻¹ • x)) volume :=
    hG.1.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul (μ := volume) (inv_ne_zero hR.ne'))
  have hGs : MemLp (fun x => G (R⁻¹ • x)) 2 volume := (memLp_two_iff_integrable_sq_norm hA).2 hI
  have hEq : (B0579.cell c).indicator (fun x => g (R⁻¹ • x)) = fun x => G (R⁻¹ • x) := by
    funext x
    by_cases hx : x ∈ B0579.cell c
    · rw [Set.indicator_of_mem hx, hGdef, Set.indicator_of_mem ((hmem x).2 hx)]
    · rw [Set.indicator_of_notMem hx, hGdef, Set.indicator_of_notMem (fun h => hx ((hmem x).1 h))]
  rw [← memLp_indicator_iff_restrict (B0579.measurableSet_cell c), hEq]
  exact hGs

/-- Scaling of the kernel Biot-Savart relation (`IsKernelBiotSavart` of `ψ(R⁻¹·)` and `R u(R⁻¹·)`
on the cell `C_c` from the one of `ψ, u` on `C_{c/R}`). -/
theorem isKernelBiotSavart_rescale {c R : ℝ} (hR : 0 < R) {ψ : ℝ × ℝ → ℝ}
    {uψ : ℝ × ℝ → Fin 2 → ℝ} (h : IsKernelBiotSavart (c / R) ψ uψ) :
    IsKernelBiotSavart c (fun x => ψ (R⁻¹ • x)) (fun x j => R * uψ (R⁻¹ • x) j) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hΓ := cell_integral_comp_inv_real (c := c) hR ψ
  refine ⟨fun j => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · show MemLp (fun x => R * uψ (R⁻¹ • x) j -
        meanShear c (∫ y in B0579.cell c, ψ (R⁻¹ • y)) x j) 2 (volume.restrict (B0579.cell c))
    have key : (fun x => R * uψ (R⁻¹ • x) j -
        meanShear c (∫ y in B0579.cell c, ψ (R⁻¹ • y)) x j) =
        fun x => R * (uψ (R⁻¹ • x) j -
          meanShear (c / R) (∫ y in B0579.cell (c / R), ψ y) (R⁻¹ • x) j) := by
      funext x
      rw [hΓ, meanShear_rescale_aux hR]
      ring
    rw [key]
    exact (memLp_cell_comp hR (h1 j)).const_mul R
  · show ∫ x in B0579.cell c, ((R * uψ (R⁻¹ • x) 0) * B0579.pd 0 φ x +
        (R * uψ (R⁻¹ • x) 1) * B0579.pd 1 φ x) = 0
    have hφ' : B0579.IsCylTest (c / R * R) φ := by
      rw [div_mul_cancel₀ c hR.ne']
      exact hφ
    have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have hcyl := T08.isCylTest_dilate hR hφ'
    have key := h2 (fun z => φ (R • z)) hcyl
    have hT := integral_cell_scale_real (d := c / R) (R := R) hR
      (fun x => (R * uψ (R⁻¹ • x) 0) * B0579.pd 0 φ x + (R * uψ (R⁻¹ • x) 1) * B0579.pd 1 φ x)
    rw [div_mul_cancel₀ c hR.ne'] at hT
    rw [hT]
    have hpt : ∀ y : ℝ × ℝ,
        (R * uψ (R⁻¹ • (R • y)) 0) * B0579.pd 0 φ (R • y) +
          (R * uψ (R⁻¹ • (R • y)) 1) * B0579.pd 1 φ (R • y) =
        uψ y 0 * B0579.pd 0 (fun z => φ (R • z)) y +
          uψ y 1 * B0579.pd 1 (fun z => φ (R • z)) y := by
      intro y
      rw [T08.pd_dilate 0 hφd, T08.pd_dilate 1 hφd, inv_smul_smul₀ hR.ne']
      ring
    have hint : ∫ y in B0579.cell (c / R),
        ((R * uψ (R⁻¹ • (R • y)) 0) * B0579.pd 0 φ (R • y) +
          (R * uψ (R⁻¹ • (R • y)) 1) * B0579.pd 1 φ (R • y)) =
        ∫ y in B0579.cell (c / R), (uψ y 0 * B0579.pd 0 (fun z => φ (R • z)) y +
          uψ y 1 * B0579.pd 1 (fun z => φ (R • z)) y) := by
      congr 1
      funext y
      exact hpt y
    rw [hint, key, mul_zero]
  · show ∫ x in B0579.cell c, ψ (R⁻¹ • x) * φ x =
        ∫ x in B0579.cell c, ((R * uψ (R⁻¹ • x) 0) * B0579.pd 1 φ x -
          (R * uψ (R⁻¹ • x) 1) * B0579.pd 0 φ x)
    have hφ' : B0579.IsCylTest (c / R * R) φ := by
      rw [div_mul_cancel₀ c hR.ne']
      exact hφ
    have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have hcyl := T08.isCylTest_dilate hR hφ'
    have key := h3 (fun z => φ (R • z)) hcyl
    have hF := integral_cell_scale_real (d := c / R) (R := R) hR (fun x => ψ (R⁻¹ • x) * φ x)
    have hH := integral_cell_scale_real (d := c / R) (R := R) hR
      (fun x => (R * uψ (R⁻¹ • x) 0) * B0579.pd 1 φ x -
        (R * uψ (R⁻¹ • x) 1) * B0579.pd 0 φ x)
    rw [div_mul_cancel₀ c hR.ne'] at hF hH
    rw [hF, hH]
    have e1 : ∫ y in B0579.cell (c / R), ψ (R⁻¹ • (R • y)) * φ (R • y) =
        ∫ y in B0579.cell (c / R), ψ y * φ (R • y) := by
      simp only [inv_smul_smul₀ hR.ne']
    have e2 : ∫ y in B0579.cell (c / R),
        ((R * uψ (R⁻¹ • (R • y)) 0) * B0579.pd 1 φ (R • y) -
          (R * uψ (R⁻¹ • (R • y)) 1) * B0579.pd 0 φ (R • y)) =
        ∫ y in B0579.cell (c / R), (uψ y 0 * B0579.pd 1 (fun z => φ (R • z)) y -
          uψ y 1 * B0579.pd 0 (fun z => φ (R • z)) y) := by
      congr 1
      funext y
      rw [T08.pd_dilate 0 hφd, T08.pd_dilate 1 hφd, inv_smul_smul₀ hR.ne']
      ring
    rw [e1, e2, key]

end UnforcedLeray.Short.IIIa.AdjE1
