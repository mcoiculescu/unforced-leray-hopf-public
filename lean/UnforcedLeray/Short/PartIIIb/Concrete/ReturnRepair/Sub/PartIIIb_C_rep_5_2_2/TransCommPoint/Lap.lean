import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Lap.Int

/-!
# `tcLap`: `Ψ_{ΔZ} = ΔΨ_Z - 2Z_z e_z` (`TCLap`)

Source `the November 2 reference manuscript` 4176-4214, 3700-3712, 3603-3647.
With `g = ∂_ρZ_z - ∂_zZ_ρ` on the half plane:
* `ΔΨ_Z = (2Z_z + ϱ g(ϱ)) e_z` (`Lap/Psi.lean`: `∇Ψ = (y₁Z_z, y₂Z_z, -ϱ Z_ρ)`, line identities
  of `Lap/Axi.lean`);
* `Ψ_{ΔZ} = -∫_ϱ^∞ ρ(ΔZ)_z dρ = ϱ g(ϱ) e_z`, since `ρ(ΔZ)_z = (ρ g)'` (`Lap/Ode.lean`, using
  axisymmetry and the divergence-free condition) and `ρ g → 0` (`Lap/Int.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcLap : TCLap := by
  intro σ₁ σ₂ ν μ R P T τ y hctx
  have H := tcb_of_ctx hctx
  have hy := tcb_ann_gt hctx
  have hlap := tcl_lapPsi H τ hy
  have hint := tcl_integral H τ (y 2) hy
  have hpsi : psiFld (fun t y' => physLap (sepX0 ν μ T t) y') τ y =
      (-∫ ρ in Ioi (ϱ y), ρ * physLap (sepX0 ν μ T τ) (!₂[ρ, 0, y 2]) 2) •
        (coordinateVector 2 : Space) := rfl
  rw [hpsi, hint, hlap]
  rw [← sub_smul]
  congr 1
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
