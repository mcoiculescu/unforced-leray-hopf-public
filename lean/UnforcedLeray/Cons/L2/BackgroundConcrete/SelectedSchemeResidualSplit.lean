import UnforcedLeray.Cons.L2.BackgroundConcrete.AggregatePairF
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellSchemeCrossAggregate

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412

/-- The compact-solenoidal fixed-point equation, with its raw/inlet cross convection removed by
actual solenoidality. The remaining convection is grouped into raw self-interaction, state self-
interaction, and the two linear pairings; this is the algebraic bridge to the total background
field equation. -/
theorem selectedState_compactProjectedResidual_split (p : Params) {B : Budget}
    (hRawBound : p.RawResidualBound B) (hLinBound : p.OrdinaryOperatorBounded)
    (hQuadBound : p.QuadraticBound B) (hRaw : p.RawLiftRegular)
    (hInlet : p.InletRegular) {z : (p.scheme B).Z}
    (hsmall : IsSmallSolution (p.scheme B) (B.radius p.ν p.ε) z)
    {Φ : ℝ × Space → CVec3} (hΦ : IsSolTest p.period Φ) :
    (pairF p.period (L0T p.ν Φ) p.Ufun -
      pairF p.period (advT p.Ufun Φ) p.Ufun) +
      (pairF p.period (L0T p.ν Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          pairF p.period (L0T p.ν Φ) (p.Efun i)) -
      (pairF p.period (advT (fun x => rep (p.wOf z) x.1 x.2) Φ) p.Ufun +
        pairF p.period (advT p.Ufun Φ)
          (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          (pairF p.period (advT (p.Efun i) Φ) p.Ufun +
            pairF p.period (advT p.Ufun Φ) (p.Efun i))) -
      pairF p.period (advT (p.uOf z) Φ) (p.uOf z) = 0 := by
  have hagg := compactSolenoidalAggregate_pairF p hRawBound hLinBound hQuadBound hsmall hΦ
  have hcross := selectedState_rawInletCross_pairF_sum_eq_zero p B hRaw hInlet
    (z := z) hΦ.1
  simp_rw [mul_add] at hagg hcross
  simp_rw [Finset.sum_add_distrib] at hagg hcross
  simp_rw [mul_add, Finset.sum_add_distrib]
  linear_combination hagg - hcross

#print axioms selectedState_compactProjectedResidual_split

end UnforcedLeray.Cons.C03.Concrete
