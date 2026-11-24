import UnforcedLeray.Short.PartIIIb.NearInst.Chart

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1/4/1`: linear bound for `nsSym`

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 3256-3268, 4284-4286.

`nsSym T` has entries `T₀₀`, `T₁₁`, `T₂₂`, the symmetrised `symRZ T = (T₀₂ + T₂₀)/2`, and zeros.
Each coordinate of a Euclidean tensor is bounded by its norm, so every entry is bounded by `‖T‖`.
-/

set_option autoImplicit false

noncomputable section

theorem nsSym_abs_le_norm : ∃ C : ℝ, ∀ (T : UnforcedLeray.Short.PartIIIb.Concrete.Ten3) (a b : Fin 3), |UnforcedLeray.Short.PartIIIb.NearInst.nsSym T a b| ≤ C * ‖T‖ := by
  refine ⟨1, fun T a b => ?_⟩
  have key : ∀ i : Fin 3 × Fin 3, |T i| ≤ ‖T‖ := fun i => by
    have h := PiLp.norm_apply_le T i
    simpa [Real.norm_eq_abs] using h
  have h02 := abs_le.mp (key (0, 2))
  have h20 := abs_le.mp (key (2, 0))
  have hrz : |UnforcedLeray.Short.PartIIIb.NearInst.symRZ T| ≤ ‖T‖ := by
    unfold UnforcedLeray.Short.PartIIIb.NearInst.symRZ
    exact abs_le.mpr ⟨by linarith [h02.1, h20.1], by linarith [h02.2, h20.2]⟩
  fin_cases a <;> fin_cases b <;>
    simp [UnforcedLeray.Short.PartIIIb.NearInst.nsSym, key, hrz]

end
