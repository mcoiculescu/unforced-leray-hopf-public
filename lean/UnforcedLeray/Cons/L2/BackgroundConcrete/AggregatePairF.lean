import UnforcedLeray.Cons.L2.BackgroundConcrete.AggregateA0Bridge
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# The explicit period-integral form of the compact aggregate
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0411
open UnforcedLeray.B0412

/-- With the state exposed in its concrete graph space, the aggregate identity uses the explicit
period integral for its linear correction term. -/
theorem compactSolenoidalAggregate_pairF (p : Params) {B : Budget}
    (hRaw : p.RawResidualBound B) (hLin : p.OrdinaryOperatorBounded)
    (hQuad : p.QuadraticBound B) {z : p.Z}
    (hsmall : IsSmallSolution (p.scheme B) (B.radius p.ν p.ε) z)
    {Φ : ℝ × Space → CVec3} (hΦ : IsSolTest p.period Φ) :
    (pairF p.period (L0T p.ν Φ) p.Ufun - pairF p.period (advT p.Ufun Φ) p.Ufun) +
      (pairF p.period (L0T p.ν Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        pairF p.period (convT p.raw Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          (pairF p.period (L0T p.ν Φ) (p.Efun i) +
            pairF p.period (convT p.raw Φ) (p.Efun i))) +
      (-pairF p.period (advT (p.uOf z) Φ) (p.uOf z)) = 0 := by
  have h := compactSolenoidalAggregate_of_small p hRaw hLin hQuad hsmall hΦ
  have hA0 := A0_phasePair_eq_L0T (p := p) (z := z) (Φ := Φ) hΦ.1
  rw [hA0] at h
  rw [phasePair_eq_pairF_rep (isPhaseTest_L0T hΦ.1 p.ν) (p.wOf z)] at h
  exact h

#print axioms compactSolenoidalAggregate_pairF

end UnforcedLeray.Cons.C03.Concrete
