import UnforcedLeray.Cons.L2.BackgroundConcrete
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellBoundedConvection

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

/-- The exact compact-test convection identity for an actual scheme inlet column and the actual
raw background. Its only suppliers are the pre-equation raw/inlet regularity clauses. -/
theorem schemeInlet_pairF_convT_convection_identity (p : Params) {B : Budget}
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular) (i : Fin 2)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period (convT p.raw Φ) (p.Efun i) +
      pairF p.period (advT (p.Efun i) Φ) p.Ufun +
      pairF p.period (advT p.Ufun Φ) (p.Efun i) = 0 := by
  change pairF p.period (convT p.raw Φ)
      (fun z => realC (p.inlet i z.1 z.2)) +
    pairF p.period (advT (fun z => realC (p.inlet i z.1 z.2)) Φ)
      (fun z => realC (p.raw z.1 z.2)) +
    pairF p.period (advT (fun z => realC (p.raw z.1 z.2)) Φ)
      (fun z => realC (p.inlet i z.1 z.2)) = 0
  exact pairF_convT_boundedSolenoidal_convection_identity hΦ hRaw.1
    (hInlet i).1 (hInlet i).2

#print axioms schemeInlet_pairF_convT_convection_identity

end UnforcedLeray.Cons.C03.Concrete
