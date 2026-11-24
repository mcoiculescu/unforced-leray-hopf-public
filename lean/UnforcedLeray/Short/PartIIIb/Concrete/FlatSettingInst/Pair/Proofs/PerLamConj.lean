import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Short.PartIIIa.Clock.Frame
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- Inverse of a `2 × 2` complex matrix whose second row is the conjugate of the first, with
conjugate-symmetric diagonal (the Gram matrix of a conjugate pair): the entries of the inverse
satisfy the same conjugation relations. -/
theorem perLamConjInv2_aux (M : Matrix (Fin 2) (Fin 2) ℂ) (h11 : M 1 1 = conj (M 0 0))
    (h10 : M 1 0 = conj (M 0 1)) :
    M⁻¹ 1 1 = conj (M⁻¹ 0 0) ∧ M⁻¹ 1 0 = conj (M⁻¹ 0 1) := by
  have hdet : conj M.det = M.det := by
    rw [Matrix.det_fin_two]
    simp only [h11, h10, map_sub, map_mul, Complex.conj_conj]
    ring
  have e00 : M⁻¹ 0 0 = M.det⁻¹ * M 1 1 := by
    rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
    simp [Matrix.smul_apply]
  have e01 : M⁻¹ 0 1 = -(M.det⁻¹ * M 0 1) := by
    rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
    simp [Matrix.smul_apply, mul_neg]
  have e10 : M⁻¹ 1 0 = -(M.det⁻¹ * M 1 0) := by
    rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
    simp [Matrix.smul_apply, mul_neg]
  have e11 : M⁻¹ 1 1 = M.det⁻¹ * M 0 0 := by
    rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
    simp [Matrix.smul_apply]
  constructor
  · rw [e11, e00, map_mul, map_inv₀, hdet, h11, Complex.conj_conj]
  · rw [e10, e01, map_neg, map_mul, map_inv₀, hdet, h10]

/-- **The Gram-normalized dual rows are conjugate** (source 2894-2896, 4353-4356). -/
theorem perLamConj :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.PerLamConj := by
  intro κ d he hl y
  have hL : ∀ x, UnforcedLeray.Short.IIIa.perLam0 κ d 1 x =
      conj (UnforcedLeray.Short.IIIa.perLam0 κ d 0 x) := by
    intro x
    simp only [UnforcedLeray.Short.IIIa.perLam0, UnforcedLeray.Short.IIIa.perSum, hl]
    exact (Complex.conj_tsum _).symm
  have hE : ∀ x, UnforcedLeray.Short.IIIa.perE κ d 1 x =
      conj (UnforcedLeray.Short.IIIa.perE κ d 0 x) := by
    intro x
    simp only [UnforcedLeray.Short.IIIa.perE, UnforcedLeray.Short.IIIa.perSum, he]
    exact (Complex.conj_tsum _).symm
  have h11 : UnforcedLeray.Short.IIIa.perGram κ d 1 1 =
      conj (UnforcedLeray.Short.IIIa.perGram κ d 0 0) := by
    simp only [UnforcedLeray.Short.IIIa.perGram, hL, hE]
    rw [← integral_conj]
    congr 1
    funext x
    simp [map_mul]
  have h10 : UnforcedLeray.Short.IIIa.perGram κ d 1 0 =
      conj (UnforcedLeray.Short.IIIa.perGram κ d 0 1) := by
    simp only [UnforcedLeray.Short.IIIa.perGram, hL, hE]
    rw [← integral_conj]
    congr 1
    funext x
    simp [map_mul]
  obtain ⟨i11, i10⟩ := perLamConjInv2_aux _ h11 h10
  simp only [UnforcedLeray.Short.IIIa.perLam, Fin.sum_univ_two]
  rw [map_add, map_mul, map_mul, i11, i10, hL y]
  simp only [Complex.conj_conj]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
