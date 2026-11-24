import UnforcedLeray.Cons.L2.BackgroundConcrete
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellConvT
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

/-- At the actual dual exponent `q₀'`, the compact-test transpose identity applies to the
selected state correction and the actual bounded raw background. The correction's solenoidality
comes from membership of the state in the graph space; no correction or pressure hypothesis is
used. -/
theorem selectedState_pairF_convT_convection_identity (p : Params) (B : Budget)
    (hRaw : p.RawLiftRegular) {z : (p.scheme B).Z}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period (convT p.raw Φ)
        (fun x => rep (p.wOf z) x.1 x.2) +
      pairF p.period (advT (fun x => rep (p.wOf z) x.1 x.2) Φ)
        (fun x => realC (p.raw x.1 x.2)) +
      pairF p.period (advT (fun x => realC (p.raw x.1 x.2)) Φ)
        (fun x => rep (p.wOf z) x.1 x.2) = 0 := by
  have hwX : p.wOf z ∈ X p.period p.ν q0E := by
    exact cw_mem_X z
  have hw : IsPhaseSolenoidal (p.wOf z) := (mem_X.mp hwX).1
  have hqtop : conjExp q0E ≠ ⊤ := conjExp_ne_top one_lt_q0E
  exact pairF_convT_convection_identity hw hΦ hRaw.1
    (p := conjExp q0E) hqtop

#print axioms selectedState_pairF_convT_convection_identity

end UnforcedLeray.Cons.C03.Concrete
