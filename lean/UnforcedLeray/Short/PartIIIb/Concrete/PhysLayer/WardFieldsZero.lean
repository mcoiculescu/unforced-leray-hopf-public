import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer

/-!
# `wardFieldsZero`: the Ward fields vanish for zero old source (source 4171)

`X₀` is linear in `χ_oT` (source 4171), so for `g = 0` the Ward field `X = 𝒞_y X₀` is zero,
hence `Y = D_{μ+1}X = 0` and `h = [U, X] = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wardFz_nsSym_zero : NearInst.nsSym (0 : Ten3) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NearInst.nsSym, NearInst.symRZ]

theorem wardFz_cartLift_zero (R c : ℝ) :
    NearInst.cartLift R c (0 : Chart → Ten3) = fun _ _ => (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
  funext τ z
  simp [NearInst.cartLift, wardFz_nsSym_zero]

theorem wardFz_oldPhys_zero (R c : ℝ) :
    oldPhys R c (0 : Chart → Ten3) = fun _ _ => (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
  unfold oldPhys
  exact wardFz_cartLift_zero R c

theorem wardFz_sepW_zero (ν : ℝ) (μ : ℂ) (y : Space) (τ : ℝ) :
    IIIa.sepW ν μ (fun _ _ => (0 : Matrix (Fin 3) (Fin 3) ℝ)) y τ = 0 := by
  funext i
  simp [IIIa.sepW]

theorem wardFz_X0_zero (ν μ R c : ℝ) : wardX0 ν μ R c (0 : Chart → Ten3) = 0 := by
  funext τ y
  ext i
  simp [wardX0, wardFz_oldPhys_zero, wardFz_sepW_zero]

theorem wardFz_streamCut_zero (ν R : ℝ) (χy : ℝ → ℝ) :
    wardStreamCut ν R χy (0 : ℝ → Space → Space) = 0 := by
  funext τ y
  simp [wardStreamCut, outPrim]

theorem wardFz_X_zero (ν μ R c : ℝ) (χy : ℝ → ℝ) :
    wardX ν μ R c χy (0 : Chart → Ten3) = 0 := by
  unfold wardX
  rw [wardFz_X0_zero]
  exact wardFz_streamCut_zero ν R χy

theorem wardFieldsZero (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) :
    WardFieldsZero ν μ R c χy U := by
  have hX := wardFz_X_zero ν μ R c χy
  unfold WardFieldsZero
  constructor
  · unfold wardY
    rw [hX]
    funext τ y
    simp [physDmu, physLap, physPd, physPd2]
  · unfold wardH
    rw [hX]
    funext τ y
    simp

end UnforcedLeray.Short.PartIIIb.Concrete
