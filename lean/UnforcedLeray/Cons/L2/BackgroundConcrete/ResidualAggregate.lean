import UnforcedLeray.Cons.L2.BackgroundConcrete

/-!
# The compact-solenoidal aggregate of the three projected operator relations

At a small state, the raw, ordinary, and quadratic source relations add to the zero projected
source. This phase-test identity uses precisely the solenoidal tests quantified by the operator
specifications; no extension to non-solenoidal tests is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0411
open UnforcedLeray.B0412

/-- Summing `RawRel`, `OrdRel`, and `QuadRel` at a small state gives the aggregate compact
solenoidal-test identity, and the small-state equation makes that aggregate vanish. -/
theorem compactSolenoidalAggregate_of_small (p : Params) {B : Budget}
    (hRaw : p.RawResidualBound B) (hLin : p.OrdinaryOperatorBounded)
    (hQuad : p.QuadraticBound B) {z : (p.scheme B).Z}
    (hsmall : IsSmallSolution (p.scheme B) (B.radius p.ν p.ε) z)
    {Φ : ℝ × Space → CVec3} (hΦ : IsSolTest p.period Φ) :
    (pairF p.period (L0T p.ν Φ) p.Ufun - pairF p.period (advT p.Ufun Φ) p.Ufun) +
      (phasePair p.period q0E Φ (p.A0 z) +
        pairF p.period (convT p.raw Φ)
          (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          (pairF p.period (L0T p.ν Φ) (p.Efun i) +
            pairF p.period (convT p.raw Φ) (p.Efun i))) +
      (-pairF p.period (advT (p.uOf z) Φ) (p.uOf z)) = 0 := by
  have hraw : p.RawRel (p.rawRes (B.residual p.ν p.ε)) := (p.rawRes_spec hRaw).1
  have hlin : p.OrdRel z (p.lin z) := p.lin_spec hLin z
  have hquad : p.QuadRel z z (p.quad (B.poly p.ν) z z) :=
    (p.quad_spec hQuad).1 z z
  have htotal : p.rawRes (B.residual p.ν p.ε) + p.lin z +
      p.quad (B.poly p.ν) z z = 0 := hsmall.2
  have hpair : phasePair p.period q0E Φ
      (p.rawRes (B.residual p.ν p.ε) + p.lin z + p.quad (B.poly p.ν) z z) = 0 := by
    have h := congrArg (fun g : p.Y => phasePair p.period q0E Φ g) htotal
    simpa using h
  have hsum : phasePair p.period q0E Φ
        (p.rawRes (B.residual p.ν p.ε) + p.lin z + p.quad (B.poly p.ν) z z) =
      (pairF p.period (L0T p.ν Φ) p.Ufun - pairF p.period (advT p.Ufun Φ) p.Ufun) +
        (phasePair p.period q0E Φ (p.A0 z) +
          pairF p.period (convT p.raw Φ)
            (fun x => rep (p.wOf z) x.1 x.2) +
          ∑ i : Fin 2, (p.coord z i : ℂ) *
            (pairF p.period (L0T p.ν Φ) (p.Efun i) +
              pairF p.period (convT p.raw Φ) (p.Efun i))) +
        (-pairF p.period (advT (p.uOf z) Φ) (p.uOf z)) := by
    rw [map_add, map_add, hraw Φ hΦ, hlin Φ hΦ, hquad Φ hΦ]
  rw [hsum] at hpair
  exact hpair

#print axioms compactSolenoidalAggregate_of_small

end UnforcedLeray.Cons.C03.Concrete
