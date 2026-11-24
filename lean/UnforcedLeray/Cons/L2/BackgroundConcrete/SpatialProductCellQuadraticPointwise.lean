import UnforcedLeray.Cons.L2.BackgroundConcrete
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators

set_option autoImplicit false

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace

/-- Pointwise bilinear expansion of the quadratic convection pairing for a sum of two fields.
This is an algebraic identity only; spacetime integrability is proved separately at use sites. -/
theorem dotL_advT_sum_pair_expand {Φ A B : ℝ × Space → CVec3} (x : ℝ × Space) :
    dotL (advT (fun z => A z + B z) Φ x) (A x + B x) =
      dotL (advT A Φ x) (A x) + dotL (advT A Φ x) (B x) +
      dotL (advT B Φ x) (A x) + dotL (advT B Φ x) (B x) := by
  simp [advT, dotL_apply, Finset.sum_add_distrib, add_smul, mul_add]
  ring

/-- The pointwise quadratic expansion at the actual scheme state, with its actual affine inlet and
the canonical joint representative of its graph correction. This statement does not claim the
integrability required to integrate its four terms. -/
theorem selectedState_quadraticConvection_pointwise (p : Params) {B : Budget}
    {z : (p.scheme B).Z} {Φ : ℝ × Space → CVec3} (x : ℝ × Space) :
    dotL (advT (p.uOf z) Φ x) (p.uOf z x) =
      dotL (advT (p.eFun (p.coord z)) Φ x) (p.eFun (p.coord z) x) +
      dotL (advT (p.eFun (p.coord z)) Φ x) (rep (p.wOf z) x.1 x.2) +
      dotL (advT (fun y => rep (p.wOf z) y.1 y.2) Φ x)
        (p.eFun (p.coord z) x) +
      dotL (advT (fun y => rep (p.wOf z) y.1 y.2) Φ x)
        (rep (p.wOf z) x.1 x.2) := by
  change dotL (advT (fun y => p.eFun (p.coord z) y +
      rep (p.wOf z) y.1 y.2) Φ x)
      (p.eFun (p.coord z) x + rep (p.wOf z) x.1 x.2) = _
  exact dotL_advT_sum_pair_expand x

#print axioms dotL_advT_sum_pair_expand
#print axioms selectedState_quadraticConvection_pointwise

end UnforcedLeray.Cons.C03.Concrete
