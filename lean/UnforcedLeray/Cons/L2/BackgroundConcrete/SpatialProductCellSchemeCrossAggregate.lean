import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellFixedStateConvection
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellSchemeInletConvection

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

/-- The actual correction and the coordinate-weighted actual inlet columns jointly cancel all
raw-background cross-convection terms on a compact phase test. This is the exact cross-term
aggregate used when expanding the quadratic source at a selected scheme state. -/
theorem selectedState_rawInletCross_pairF_sum_eq_zero (p : Params) (B : Budget)
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular) {z : (p.scheme B).Z}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    (pairF p.period (convT p.raw Φ)
        (fun x => rep (p.wOf z) x.1 x.2) +
      pairF p.period (advT (fun x => rep (p.wOf z) x.1 x.2) Φ) p.Ufun +
      pairF p.period (advT p.Ufun Φ)
        (fun x => rep (p.wOf z) x.1 x.2)) +
    ∑ i : Fin 2, (p.coord z i : ℂ) *
      (pairF p.period (convT p.raw Φ) (p.Efun i) +
       pairF p.period (advT (p.Efun i) Φ) p.Ufun +
       pairF p.period (advT p.Ufun Φ) (p.Efun i)) = 0 := by
  have hw := selectedState_pairF_convT_convection_identity p B hRaw (z := z) hΦ
  have hi (i : Fin 2) := schemeInlet_pairF_convT_convection_identity
    p (B := B) hRaw hInlet i hΦ
  have hsum : ∑ i : Fin 2, (p.coord z i : ℂ) *
      (pairF p.period (convT p.raw Φ) (p.Efun i) +
       pairF p.period (advT (p.Efun i) Φ) p.Ufun +
       pairF p.period (advT p.Ufun Φ) (p.Efun i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi'
    rw [hi i]
    simp
  change (pairF p.period (convT p.raw Φ)
      (fun x => rep (p.wOf z) x.1 x.2) +
    pairF p.period (advT (fun x => rep (p.wOf z) x.1 x.2) Φ)
      (fun x => realC (p.raw x.1 x.2)) +
    pairF p.period (advT (fun x => realC (p.raw x.1 x.2)) Φ)
      (fun x => rep (p.wOf z) x.1 x.2)) +
    ∑ i : Fin 2, (p.coord z i : ℂ) *
      (pairF p.period (convT p.raw Φ) (p.Efun i) +
       pairF p.period (advT (p.Efun i) Φ) p.Ufun +
       pairF p.period (advT p.Ufun Φ) (p.Efun i)) = 0
  rw [hw, hsum]
  simp

#print axioms selectedState_rawInletCross_pairF_sum_eq_zero

end UnforcedLeray.Cons.C03.Concrete
