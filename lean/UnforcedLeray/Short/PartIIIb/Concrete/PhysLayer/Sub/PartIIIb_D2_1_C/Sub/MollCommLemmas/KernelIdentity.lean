import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs

/-!
# `KernelIdentity`: `adjKer - testKer = ½ kap`

Source `the November 2 reference manuscript` (the adjoint graph at `r = 2`);
the definitions are those of `MollCommDefs`. The difference of the two kernels is
`(3/2) ρ + ½ (v·∇ρ(z)|_{v = x.2} - v·∇ρ(z)|_{v = x.2 - z.2})`, and the `y`-derivative is linear in
the vector, so the two drift terms differ by `½ kerDv ρ z.2 z`, which is `½ (kap ρ z - 3 ρ z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem kernelIdentity : KernelIdentity := by
  intro ν μ ρ x z
  have hv : ((0 : ℝ), x.2) - ((0 : ℝ), x.2 - z.2) = ((0 : ℝ), z.2) := by
    ext <;> simp
  have hD := map_sub (fderiv ℝ (ρ.normed volume) z) ((0 : ℝ), x.2) ((0 : ℝ), x.2 - z.2)
  rw [hv] at hD
  unfold adjKer testKer kap kerDv
  linear_combination (-1 / 2 : ℝ) * hD

end UnforcedLeray.Short.PartIIIb.Concrete
