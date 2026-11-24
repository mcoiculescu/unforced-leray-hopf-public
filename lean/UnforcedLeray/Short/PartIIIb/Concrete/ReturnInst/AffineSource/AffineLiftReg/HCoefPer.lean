import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.HhatAPeriodic

/-!
# `c`-periodicity of the `ĥ_A` coefficient in `q` (source 4963-4975)

The lattice periodicity `ĥ_A(s, q + c, η) = ĥ_A(s, q, η)` is `hhatAPeriodic_proof`
(`PhysLayer/Sub/PartIIIb-D2_4_2/HhatAPeriodic.lean`). The coefficient `hAcoef` is `merOf` of
`s^{-1/2} ĥ_A`, which is `q`-independent in its prefactor.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem affHCoefPer (as : ℝ) (χf : ℝ → ℝ) : AffHCoefPer as χf := by
  intro _ ν ε _ A _ s η _ ξ
  show merOf ((Real.sqrt s)⁻¹ • hhatA ν ε χf A s (ξ + cOf ν, η))
      = merOf ((Real.sqrt s)⁻¹ • hhatA ν ε χf A s (ξ, η))
  have h := hhatAPeriodic_proof ν ε χf A s (ξ, η) 1
  simp only [Int.cast_one, one_mul] at h
  rw [h]

end UnforcedLeray.Short.PartIIIb.Concrete
