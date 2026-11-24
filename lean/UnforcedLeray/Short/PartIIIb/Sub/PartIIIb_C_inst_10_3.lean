import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_3

/-!
# `PartIII-b:C/inst/10/3`: `EAcCellBound` from Gaussian leaves

Source `the November 2 reference manuscript`
lines 4963-4975 (`V_j`, `p_j`), 4971-4972 (`e_A`), 5063-5079 (cell norms).

Same plan as `FAcCellBound` (`Sub/PartIII-b_C_inst_9_3.lean`): the pointwise square bound by the
lattice sum of the same Gaussian majorant `fAcG`, then the cell unfolding (`FAcCellUnfold`) and the
Gaussian integral (`FAcGaussInt`), both of which are already proved for `FAcCellBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `j`-th summand of `eAB`. -/
def eAcTerm (ν s : ℝ) (B C : Mat3) (j : ℤ) (x : ℝ × ℝ) : Vec3 :=
  (2 : ℝ) • mv B (emb (Vj ν s j x))
      + (2 * ν) • hessContr C (Vj ν s j) x
      - mv (fun a b => C a b + C b a) (emb (mgrad (pj ν s j) x))

/-- Leaf E1a (source 4963-4966, 4978): second derivatives of `V_j = a⁻² e^{-|x_j|²/(4a)} J x_j`
(Gaussian times polynomial of degree ≤ 3 in `x_j`), uniform for `ν ≤ 1`, `s ≤ 1.1/ν`. -/
def HessVjUnif : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν →
    ∀ (j : ℤ) (x : ℝ × ℝ) (a b : Fin 2),
    ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei b)) x (ei a)‖ ≤
      K * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))

/-- Leaf E1b (source 4964-4966, 4978): `∇p_j = a⁻⁴ x_j e^{-|x_j|²/(2a)}`, uniform bound. -/
def MgradPjUnif : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν →
    ∀ (j : ℤ) (x : ℝ × ℝ),
    ‖mgrad (pj ν s j) x‖ ≤
      K * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))

/-- Leaf E1 (source 5063-5079): pointwise bound of the meridional part of the `j`-th term. -/
def EAcTermPointwise : Prop :=
  ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ν s : ℝ) (B C : Mat3) (j : ℤ) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s →
    s ≤ (11 / 10) / ν →
    ‖merOf (eAcTerm ν s B C j x)‖ ≤
      C0 * (frob B + frob C) * (1 + sq2 (xj ν j x)) ^ 2 *
        Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))

/-- Leaf E2 (E1 + lattice weight sum + Cauchy-Schwarz over `j`, exactly as `FAcSumPointwise`). -/
def EAcSumPointwise : Prop :=
  ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ (ν s : ℝ) (B C : Mat3) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s →
    s ≤ (11 / 10) / ν →
    ‖merOf (eAB ν s B C x)‖ ^ 2 ≤
      K1 * (frob B + frob C) ^ 2 * ∑' j : ℤ, fAcG (ageA ν s) (xj ν j x)

theorem eAcCellBound_of (h1 : EAcSumPointwise) (h2 : FAcCellUnfold) (h3 : FAcGaussInt) :
    EAcCellBound := by
  obtain ⟨K1, hK1, hP⟩ := h1
  obtain ⟨K2, hK2, hG⟩ := h3
  refine ⟨Real.sqrt (K1 * K2), Real.sqrt_nonneg _, ?_⟩
  intro ν s hν hν1 hs hsT B C
  have hc1 : 1 ≤ cOf ν := by
    unfold cOf
    rw [one_le_inv₀ (by positivity)]
    nlinarith
  have hc0 : 0 < cOf ν := by linarith
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha2 : ageA ν s ≤ 21 / 10 := by
    unfold ageA
    have : ν * s ≤ 11 / 10 := by
      rw [le_div_iff₀ hν] at hsT; linarith
    linarith
  have hfB : (0 : ℝ) ≤ K1 * (frob B + frob C) ^ 2 := by positivity
  have hnn : ∀ y, 0 ≤ fAcG (ageA ν s) y := by
    intro y
    unfold fAcG sq2
    positivity
  have hmeas : Measurable (fAcG (ageA ν s)) := by
    unfold fAcG sq2
    fun_prop
  calc ∫⁻ x, ENNReal.ofReal (‖merOf (eAB ν s B C x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ∫⁻ x, ENNReal.ofReal (K1 * (frob B + frob C) ^ 2) *
          ENNReal.ofReal (∑' j : ℤ, fAcG (ageA ν s) (xj ν j x))
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hfB]
        exact ENNReal.ofReal_le_ofReal (hP ν s B C x hν hν1 hs hsT)
    _ = ENNReal.ofReal (K1 * (frob B + frob C) ^ 2) *
          ∫⁻ x, ENNReal.ofReal (∑' j : ℤ, fAcG (ageA ν s) (xj ν j x))
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K1 * (frob B + frob C) ^ 2) *
          (ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal K2) := by
        gcongr
        calc _ ≤ ENNReal.ofReal (cOf ν)⁻¹ *
              ∫⁻ y, ENNReal.ofReal (fAcG (ageA ν s) y) ∂volume :=
            h2 (cOf ν) (fAcG (ageA ν s)) hc0 hmeas hnn
          _ ≤ _ := by gcongr; exact hG _ ha1 ha2
    _ ≤ ENNReal.ofReal (K1 * (frob B + frob C) ^ 2) * (ENNReal.ofReal 1 * ENNReal.ofReal K2) := by
        gcongr
        exact inv_le_one_of_one_le₀ hc1
    _ = ENNReal.ofReal (Real.sqrt (K1 * K2) ^ 2 * (frob B + frob C) ^ 2) := by
        rw [ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_mul hfB,
          Real.sq_sqrt (mul_nonneg hK1 hK2)]
        congr 1; ring

end UnforcedLeray.Short.PartIIIb.Concrete
