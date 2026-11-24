import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalConvection
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeResidualSplit

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412

/-- The compact-solenoidal residual identity groups all convection terms into the actual
raw-plus-selected-state convection pairing. The only operator assumptions are the existing
source-characterized raw, linear and quadratic bounds used by the selected fixed-point equation. -/
theorem selectedState_compactResidual_totalConvection {p : Params} {B : Budget}
    (hRawBound : p.RawResidualBound B) (hLinBound : p.OrdinaryOperatorBounded)
    (hQuadBound : p.QuadraticBound B) (hRaw : p.RawLiftRegular)
    (hInlet : p.InletRegular) {z : (p.scheme B).Z}
    (hsmall : IsSmallSolution (p.scheme B) (B.radius p.ν p.ε) z)
    {Φ : SpaceTime → CVec3} (hΦ : IsSolTest p.period Φ) :
    pairF p.period (L0T p.ν Φ) p.Ufun +
      (pairF p.period (L0T p.ν Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          pairF p.period (L0T p.ν Φ) (p.Efun i)) -
      pairF p.period (advT (fun x => p.Ufun x + p.uOf z x) Φ)
        (fun x => p.Ufun x + p.uOf z x) = 0 := by
  let W : SpaceTime → CVec3 := fun x => rep (p.wOf z) x.1 x.2
  let Bcross : ℂ :=
    pairF p.period (advT W Φ) p.Ufun +
      pairF p.period (advT p.Ufun Φ) W +
      ∑ i : Fin 2, (p.coord z i : ℂ) *
        (pairF p.period (advT (p.Efun i) Φ) p.Ufun +
          pairF p.period (advT p.Ufun Φ) (p.Efun i))
  have hsplit := selectedState_compactProjectedResidual_split p
    hRawBound hLinBound hQuadBound hRaw hInlet (z := z) hsmall hΦ
  have hcross0 := selectedState_rawStateCross_pairF_expand hRaw hInlet
    (B := B) (z := z) hΦ.1
  have hcross :
      pairF p.period (advT p.Ufun Φ) (p.uOf z) +
        pairF p.period (advT (p.uOf z) Φ) p.Ufun = Bcross := by
    simpa [Bcross, W, add_comm, add_left_comm, add_assoc] using hcross0
  have hfour := selectedFullBackground_pairF_rawState_fourTerm hRaw hInlet
    (B := B) (z := z) hΦ.1
  have htotal :
      pairF p.period (advT (fun x => p.Ufun x + p.uOf z x) Φ)
        (fun x => p.Ufun x + p.uOf z x) =
      pairF p.period (advT p.Ufun Φ) p.Ufun + Bcross +
        pairF p.period (advT (p.uOf z) Φ) (p.uOf z) := by
    rw [hfour]
    rw [← hcross]
    ac_rfl
  linear_combination hsplit - htotal

#print axioms selectedState_compactResidual_totalConvection

end UnforcedLeray.Cons.C03.Concrete
