import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1_1

/-!
# `PartIII-a:T21/2/2/3/6/1/1/2`: `KerVelDivFree0` from the `d = 1` instance of `KerVelDivFree`

Source: `the November 2 reference manuscript` lines 2875-2896, 3052-3057.
Scaling (`kerVel_scale`, `pd_scale` in `PartIII-a_T21_2_2_3_6_1_1_1`): with `ψ_d(y) = ψ(d y)`,
`K_dψ(d y) = d K_1ψ_d(y)` and `∂_jφ(d y) = d⁻¹ ∂_jφ_d(y)`, so the divergence pairing on `C_d` is
`d²` times the pairing of `K_1ψ_d` with `φ_d` on `C_1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- **`d > 0` weak divergence-freeness from the `d = 1` instance of the `d ≥ 1` statement**. -/
theorem kerVelDivFree0_of (h : KerVelDivFree) : KerVelDivFree0 := by
  intro d hd ψ hψ φ hφ
  have h1 := h 1 le_rfl (fun y => ψ (d • y)) (isCylTest_scale hd hψ)
    (fun y => φ (d • y)) (isCylTest_scale hd hφ)
  rw [integral_cell_scale hd]
  have hpt : ∀ y : ℝ × ℝ,
      kerVel d ψ (d • y) 0 * B0579.pd 0 φ (d • y) + kerVel d ψ (d • y) 1 * B0579.pd 1 φ (d • y) =
      kerVel 1 (fun y => ψ (d • y)) y 0 * B0579.pd 0 (fun y => φ (d • y)) y +
        kerVel 1 (fun y => ψ (d • y)) y 1 * B0579.pd 1 (fun y => φ (d • y)) y := by
    intro y
    have hk : ∀ j, kerVel d ψ (d • y) j = d * kerVel 1 (fun y => ψ (d • y)) y j := by
      intro j
      rw [kerVel_scale hd, smul_smul, inv_mul_cancel₀ hd.ne', one_smul]
    rw [hk 0, hk 1, pd_scale hφ 0, pd_scale hφ 1]
    field_simp
  simp only [hpt]
  rw [h1, mul_zero]

end UnforcedLeray.Short.IIIa.AdjE1

#print axioms UnforcedLeray.Short.IIIa.AdjE1.kerVelDivFree0_of
