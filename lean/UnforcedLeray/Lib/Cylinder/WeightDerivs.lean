import UnforcedLeray.Lib.Cylinder.Weight
import UnforcedLeray.Units.B0656.Weight

/-!
# Derivative bounds for the smooth periodic weight (INF13, target CY02, last part)


§5 CY02 (`norm_iteratedFDeriv_rpow_ρw_le`).

`paper/main.tex` lines 4569-4578 (unit B0271): the smooth periodic weight has "fixed derivative
ratios ... bounded independently of `c`"; lines 13869-13878 (unit B0656).

The weight `ρw` of `Weight.lean` is, by definition, the weight `rho` of the compiled draft

that draft's `norm_iteratedFDeriv_rho_rpow_le`, restated for `ρw`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cyl

theorem ρw_eq_rho (ℓ : ℝ) : ρw ℓ = B0656.rho ℓ := rfl

/-- **Uniform derivative bounds** (CY02; B0271, tex 4569-4578): for every order `n` and real
exponent `s` there is `C`, independent of the period `ℓ ≥ 1` and of the point, with
`‖Dⁿ(ρw ℓ ^ s)(z)‖ ≤ C ρw ℓ (z)^s`. -/
theorem norm_iteratedFDeriv_rpow_ρw_le (n : ℕ) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 1 ≤ ℓ → ∀ z : Plane,
      ‖iteratedFDeriv ℝ n (fun w => ρw ℓ w ^ s) z‖ ≤ C * ρw ℓ z ^ s :=
  B0656.norm_iteratedFDeriv_rho_rpow_le n s

end UnforcedLeray.Cyl
