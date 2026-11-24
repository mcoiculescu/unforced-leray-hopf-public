import UnforcedLeray.Cons.L2.BackgroundConcrete.ResidualAggregate
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphA0

/-!
# Explicit period pairing for the aggregate graph identity

The compact-solenoidal aggregate can express its linear correction term directly as the period
integral against `L₀ᵗΦ`, using the actual graph triple of the selected state.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0411
open UnforcedLeray.B0412

/-- At a small solution, the aggregate source identity has its `A₀w` contribution rewritten as
the concrete `L₀ᵗ` pairing with the graph correction. -/
theorem compactSolenoidalAggregate_graphA0 (p : Params) {B : Budget}
    (hRaw : p.RawResidualBound B) (hLin : p.OrdinaryOperatorBounded)
    (hQuad : p.QuadraticBound B) {z : (p.scheme B).Z}
    (hsmall : IsSmallSolution (p.scheme B) (B.radius p.ν p.ε) z)
    {Φ : ℝ × Space → CVec3} (hΦ : IsSolTest p.period Φ) :
    (pairF p.period (L0T p.ν Φ) p.Ufun - pairF p.period (advT p.Ufun Φ) p.Ufun) +
      (phasePair p.period q0E (L0T p.ν Φ) (p.wOf z) +
        pairF p.period (convT p.raw Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          (pairF p.period (L0T p.ν Φ) (p.Efun i) +
            pairF p.period (convT p.raw Φ) (p.Efun i))) +
      (-pairF p.period (advT (p.uOf z) Φ) (p.uOf z)) = 0 := by
  have h := compactSolenoidalAggregate_of_small p hRaw hLin hQuad hsmall hΦ
  have hA0 := A0_phasePair_eq_L0T (p := p) (z := z) (Φ := Φ) hΦ.1
  rw [hA0] at h
  exact h

#print axioms compactSolenoidalAggregate_graphA0

end UnforcedLeray.Cons.C03.Concrete
