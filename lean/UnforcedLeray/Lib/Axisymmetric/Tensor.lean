import UnforcedLeray.Lib.Axisymmetric.Cylindrical

/-!
# AX01 (tensors): the frame lift of meridional tensors and the Frobenius norm


§5 Layer 3, target AX01, item "tensors: `liftTensor` with Frobenius norm preserved; no entry
with exactly one azimuthal index". Blueprint units served: B0417 (`eq:m4-free-spaces`,
tex 7272–7297: `H_T = L²(s^{-1/2} dς; Sym₃)` with the Frobenius norm), B0482
(`eq:free-stress-B1`, tex 7920–7949: "tensor entries with exactly one azimuthal index
vanish"), B0550 (tex 8724–8732).

Frame components are in the manuscript's order `(r, φ, z)` (tex 7920). A tensor `T` in this
frame is lifted to the Cartesian matrix `∑_{a,b} T_{ab} e_a e_bᵀ` with `(e_0, e_1, e_2) =
(e_r, e_φ, e_z)`. For the manuscript's class (`IsMeridTensor`: `T_{rφ} = T_{φr} = T_{φz} =
T_{zφ} = 0`) the Cartesian Frobenius norm equals the frame Frobenius norm off the axis
(`frobenius_liftTensor`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Axi

/-- The cylindrical frame `(e_r, e_φ, e_z)`, in the order `(r, φ, z)`. -/
def frame (y : Space) : Fin 3 → Space := ![eR y, eΦ y, e3]

theorem frame_zero (y : Space) : frame y 0 = eR y := rfl
theorem frame_one (y : Space) : frame y 1 = eΦ y := rfl
theorem frame_two (y : Space) : frame y 2 = e3 := rfl

/-- Frame components with no entry having exactly one azimuthal index (tex 7920–7949). -/
def IsMeridTensor (T : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  T 0 1 = 0 ∧ T 1 0 = 0 ∧ T 1 2 = 0 ∧ T 2 1 = 0

/-- Tensor lift: the Cartesian matrix `∑_{a,b} T_{ab}(ϱ, y₃) (e_a)_i (e_b)_j`. -/
def liftTensor (T : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∑ a : Fin 3, ∑ b : Fin 3, T (mer y) a b * frame y a i * frame y b j

/-- **AX01 tensor lift.** Off the axis, the lift of a tensor without entries with exactly one
azimuthal index preserves the Frobenius norm: `∑ᵢⱼ (lift T)ᵢⱼ² = ∑_{ab} T_{ab}²`. -/
theorem frobenius_liftTensor (T : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) {y : Space}
    (hy : y ∉ axis) (hT : IsMeridTensor (T (mer y))) :
    ∑ i : Fin 3, ∑ j : Fin 3, liftTensor T y i j ^ 2 =
      ∑ a : Fin 3, ∑ b : Fin 3, T (mer y) a b ^ 2 := by
  obtain ⟨h01, h10, h12, h21⟩ := hT
  have hac := eR_sq_sum hy
  simp only [liftTensor, Fin.sum_univ_three, frame_zero, frame_one, frame_two, eR_apply_zero,
    eR_apply_one, eR_apply_two, eΦ_apply_zero, eΦ_apply_one, eΦ_apply_two, e3_apply,
    Fin.isValue, Fin.reduceEq, ite_true, ite_false, ↓reduceIte, h01, h10, h12, h21]
  linear_combination ((T (mer y) 0 0 ^ 2 + T (mer y) 1 1 ^ 2) *
      ((y 0 / ϱ y) ^ 2 + (y 1 / ϱ y) ^ 2 + 1) + T (mer y) 0 2 ^ 2 + T (mer y) 2 0 ^ 2) * hac

end UnforcedLeray.Axi
