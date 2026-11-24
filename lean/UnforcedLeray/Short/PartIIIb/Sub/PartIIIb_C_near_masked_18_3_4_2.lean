import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.Int

/-!
# Integrability leaf of `SepWRotEquiv` (task `PartIII-b:C/near/masked/18/3/4/2`)

`sepW` is a componentwise Bochner integral over `(l, z) ∈ (0,1) × ℝ³` (source
`the November 2 reference manuscript` 3611-3621,
`sep:resolvent`).  A rotation mixing the components commutes with it when the integrand is
integrable on `(0,1) × Space`; this is the only analytic input of `SepWRotEquiv`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.NearInst (cartLift IsBoxTensor hRad)

/-- **Integrability of the `sepW` integrand for box tensors** (3611-3621, `μ > -1/4`): for the
axisymmetric lift `cartLift R c m` of a bounded band-supported chart tensor (its `z`-support is a
compact solid torus `R/√s₂ ≤ ϱ ≤ R/√s₁`, `|z₃| ≲ L`, away from the axis, bounded by `B`), the
integrand `sepPhi` is integrable on `(0,1) × Space` at EVERY off-axis `y`, including `y` inside the
support (the kernel singularity is integrable: `∫ |∇K_t| ≲ t^{-1/2}`, `t = ν(1-l²)`,
`∫ (1-l)^{-1/2} dl < ∞`, and `l^{2μ+2}` is integrable at `0` since `μ > -3/2`). -/
def SepBoxIntegrable : Prop :=
  ∀ (ν R c μ : ℝ), 0 < ν → 0 < R → 0 < c → -(1 / 4 : ℝ) < μ → ∀ m : Chart → Ten3,
    IsBoxTensor m → ∀ (τ : ℝ) (y : Space), 0 < hRad y →
      SepIntegrableAt ν (μ : ℂ) (cartLift R c m) y τ

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
