import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont.Age

/-!
# Scaling helpers for the moving adjoint regularity leaves (SP 3036-3047, 3060)

Helpers for `MovAdjHigherReg` and `MovAdjBasicReg`: the chain rule for the moving adjoint
`movingPhi ν φ r y = a⁻¹ φ r (√a y)` (`a = clockA ν r`), and the transfer of the weighted integrability
`∫_{C_d} p_d⁻¹ |g(√a ·)|²` (`d = c/√a`) to `∫_{C_c} ⟨x⟩^{-2m}|g|²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open Real

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem contDiff_pdCx (k : Fin 2) {Ψ : ℝ × ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (pdCx k Ψ) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ Ψ) := (contDiff_infty_iff_fderiv.1 hΨ).2
  exact h1.clm_apply contDiff_const

theorem differentiable_pdCx (k : Fin 2) {Ψ : ℝ × ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) :
    Differentiable ℝ (pdCx k Ψ) :=
  (contDiff_pdCx k hΨ).differentiable (by simp)

theorem contDiff_adjSpatial (w : List (Fin 2)) {Ψ : ℝ × ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (adjSpatial w Ψ) := by
  induction w with
  | nil => exact hΨ
  | cons k w ih => exact contDiff_pdCx k ih

/-- Derivative of a composition with a positive dilation, with a constant factor. -/
theorem pdCx_const_mul_comp_smul (k : Fin 2) {Ψ : ℝ × ℝ → ℂ} (hΨ : Differentiable ℝ Ψ)
    (C : ℂ) (R : ℝ) (y : ℝ × ℝ) :
    pdCx k (fun z => C * Ψ (R • z)) y = C * (R : ℂ) * pdCx k Ψ (R • y) := by
  have hs : Differentiable ℝ (fun z : ℝ × ℝ => R • z) := differentiable_id.const_smul R
  have hd : Differentiable ℝ (fun z : ℝ × ℝ => Ψ (R • z)) := hΨ.comp hs
  unfold pdCx
  rw [fderiv_const_mul (hd y) C, fderiv_comp_smul]
  simp [Complex.real_smul, smul_eq_mul]
  ring

/-- Derivative of a composition with a positive dilation. -/
theorem pdCx_comp_smul (k : Fin 2) {Ψ : ℝ × ℝ → ℂ} (hΨ : Differentiable ℝ Ψ) (R : ℝ)
    (y : ℝ × ℝ) :
    pdCx k (fun z => Ψ (R • z)) y = (R : ℂ) * pdCx k Ψ (R • y) := by
  have hs : Differentiable ℝ (fun z : ℝ × ℝ => R • z) := differentiable_id.const_smul R
  have hd : Differentiable ℝ (fun z : ℝ × ℝ => Ψ (R • z)) := hΨ.comp hs
  unfold pdCx
  rw [fderiv_comp_smul]
  simp [Complex.real_smul, smul_eq_mul]

theorem movingPhi_eq_comp (ν : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) :
    movingPhi ν φ r = fun z => (((clockA ν r)⁻¹ : ℝ) : ℂ) * φ r (Real.sqrt (clockA ν r) • z) :=
  rfl

/-- First derivative of the moving adjoint. -/
theorem pdCx_movingPhi (ν : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) (hφ : ContDiff ℝ ∞ (φ r))
    (k : Fin 2) (y : ℝ × ℝ) :
    pdCx k (movingPhi ν φ r) y =
      (((clockA ν r)⁻¹ : ℝ) : ℂ) * ((Real.sqrt (clockA ν r) : ℝ) : ℂ) *
        pdCx k (φ r) (Real.sqrt (clockA ν r) • y) := by
  rw [movingPhi_eq_comp, pdCx_const_mul_comp_smul k (hφ.differentiable (by simp))]

theorem sqrt_mul_sqrt_inv_mul (a : ℝ) (ha : 0 < a) :
    (((a⁻¹ : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ)) * ((Real.sqrt a : ℝ) : ℂ) = 1 := by
  have hs : ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) = (a : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ha.le]
  have hinv : ((a⁻¹ : ℝ) : ℂ) * (a : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ ha.ne', Complex.ofReal_one]
  rw [mul_assoc, hs, hinv]

/-- Second derivative of the moving adjoint: the scalings cancel. -/
theorem pdCx_movingPhi_two (ν : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) (hφ : ContDiff ℝ ∞ (φ r))
    (ha : 0 < clockA ν r) (k l : Fin 2) :
    pdCx k (pdCx l (movingPhi ν φ r)) = fun y => pdCx k (pdCx l (φ r)) (Real.sqrt (clockA ν r) • y) := by
  have h1 : pdCx l (movingPhi ν φ r) = fun z =>
      (((clockA ν r)⁻¹ : ℝ) : ℂ) * ((Real.sqrt (clockA ν r) : ℝ) : ℂ) *
        pdCx l (φ r) (Real.sqrt (clockA ν r) • z) :=
    funext fun z => pdCx_movingPhi ν φ r hφ l z
  rw [h1]
  funext y
  rw [pdCx_const_mul_comp_smul k (differentiable_pdCx l hφ), sqrt_mul_sqrt_inv_mul _ ha, one_mul]

/-- Third derivative of the moving adjoint: one factor `√a` survives. -/
theorem pdCx_movingPhi_three (ν : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) (hφ : ContDiff ℝ ∞ (φ r))
    (ha : 0 < clockA ν r) (j k l : Fin 2) :
    pdCx j (pdCx k (pdCx l (movingPhi ν φ r))) =
      fun y => ((Real.sqrt (clockA ν r) : ℝ) : ℂ) *
        pdCx j (pdCx k (pdCx l (φ r))) (Real.sqrt (clockA ν r) • y) := by
  rw [pdCx_movingPhi_two ν φ r hφ ha k l]
  funext y
  rw [pdCx_comp_smul j (differentiable_pdCx k (contDiff_pdCx l hφ))]

/-- `‖c X‖² = c² ‖X‖²` for a real scalar `c`. -/
theorem norm_sq_real_const_mul (c : ℝ) (X : ℂ) : ‖((c : ℝ) : ℂ) * X‖ ^ 2 = c ^ 2 * ‖X‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The dilation maps the cell of length `c/R` onto the cell of length `c`. -/
theorem smul_mem_cell_iff (c R : ℝ) (hR : 0 < R) (y : ℝ × ℝ) :
    R • y ∈ B0579.cell c ↔ y ∈ B0579.cell (c / R) := by
  simp only [B0579.cell, Set.mem_prod, Set.mem_univ, and_true, Set.mem_Ico, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  have e : c / 2 = (c / R / 2) * R := by field_simp
  rw [e]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

/-- A sine lower bound on the cell: `(4/π²) y₁² ≤ (d/π)² sin²(π y₁/d)` for `|y₁| ≤ d/2`. -/
theorem sin_sq_lower (y1 d : ℝ) (hd : 0 < d) (h : |y1| ≤ d / 2) :
    (4 / π ^ 2) * y1 ^ 2 ≤ (d / π) ^ 2 * Real.sin (π * y1 / d) ^ 2 := by
  have hθ : |π * y1 / d| ≤ π / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hd, div_le_iff₀ hd]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left h Real.pi_pos.le]
  have hs : 2 / π * |π * y1 / d| ≤ Real.sin |π * y1 / d| :=
    Real.mul_le_sin (abs_nonneg _) hθ
  have h1 : (2 / π * |π * y1 / d|) ^ 2 ≤ (Real.sin |π * y1 / d|) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hs 2
  have h3 : (2 / π * |π * y1 / d|) ^ 2 = (2 / π * (π * y1 / d)) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
  have hsin : Real.sin |π * y1 / d| ^ 2 = Real.sin (π * y1 / d) ^ 2 := by
    rcases abs_cases (π * y1 / d) with ⟨h4, _⟩ | ⟨h4, _⟩
    · rw [h4]
    · rw [h4, Real.sin_neg, neg_sq]
  have hsq : (2 / π * (π * y1 / d)) ^ 2 ≤ Real.sin (π * y1 / d) ^ 2 := by
    rw [← h3, ← hsin]; exact h1
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hdne : d ≠ 0 := hd.ne'
  calc (4 / π ^ 2) * y1 ^ 2 = (d / π) ^ 2 * (2 / π * (π * y1 / d)) ^ 2 := by
        field_simp
        ring
    _ ≤ (d / π) ^ 2 * Real.sin (π * y1 / d) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)

/-- The weight comparison on the cell: `p_d⁻¹(y) ≤ μ^{-m} ⟨Ry⟩^{-2m}`-type bound. -/
theorem periodicWeight_le_jb (m c R : ℝ) (hm : 0 ≤ m) (hc : 0 < c) (hR : 0 < R)
    (y : ℝ × ℝ) (hy : y ∈ B0579.cell (c / R)) :
    periodicWeight (-m) (c / R) y ≤
      ((4 / π ^ 2) / (1 + R ^ 2)) ^ (-m) * B0579.jb (R • y) ^ (-m) := by
  have hd : 0 < c / R := div_pos hc hR
  have hy1 : |y.1| ≤ (c / R) / 2 := abs_le.mpr ⟨hy.1.1, hy.1.2.le⟩
  have hsin := sin_sq_lower y.1 (c / R) hd hy1
  have hκ : 0 ≤ 4 / π ^ 2 := by positivity
  have hκ1 : 4 / π ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  set μ : ℝ := (4 / π ^ 2) / (1 + R ^ 2) with hμdef
  have hμ : 0 < μ := by positivity
  have hjbR : B0579.jb (R • y) = 1 + (R * y.1) ^ 2 + (R * y.2) ^ 2 := by
    simp [B0579.jb, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have hjbpos : 0 < B0579.jb (R • y) := B0579.jb_pos _
  have hA : μ * B0579.jb (R • y) ≤ (4 / π ^ 2) * (1 + y.1 ^ 2 + y.2 ^ 2) := by
    rw [hμdef, hjbR, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hκ (sq_nonneg R), mul_nonneg hκ (sq_nonneg y.1),
      mul_nonneg hκ (sq_nonneg y.2)]
  have hB : μ * B0579.jb (R • y) ≤
      1 + y.2 ^ 2 + (c / R / π) ^ 2 * Real.sin (π * y.1 / (c / R)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hκ1) (by positivity : (0 : ℝ) ≤ 1 + y.2 ^ 2)]
  have hpos : 0 < μ * B0579.jb (R • y) := mul_pos hμ hjbpos
  have hw := Real.rpow_le_rpow_of_nonpos hpos hB (by linarith : -m ≤ 0)
  unfold periodicWeight
  rw [Real.mul_rpow hμ.le hjbpos.le] at hw
  exact hw

end UnforcedLeray.Short.IIIa.AdjE1
