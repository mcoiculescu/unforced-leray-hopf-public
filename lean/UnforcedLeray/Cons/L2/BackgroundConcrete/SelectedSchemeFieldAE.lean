import UnforcedLeray.Cons.L2.BackgroundConcrete
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateL4
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedFieldRepAE

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace UnforcedLeray.B0412 UnforcedLeray.RieszLp

/-- The actual concrete scheme field, after complexification, equals the raw-plus-state field
used by the source pairing, almost everywhere on the phase-space product. The only representative
conversion is the proved reality of the selected graph representative. -/
theorem Params.schemeField_eq_rawAddState_ae (p : Params) (B : Budget)
    (z : p.Z) :
    (fun x : ℝ × Space => realC (((p.scheme B).field z x.1) x.2)) =ᵐ[
      (volume : Measure ℝ).prod (volume : Measure Space)]
      fun x => p.Ufun x + p.uOf z x := by
  let w := p.wOf z
  have hgraph : (p.wOf z) ∈ realSub p.period q0E := by
    change cw p.period (z : Amb p.period) ∈ realSub p.period q0E
    have hz : (z : Amb p.period) ∈ graphSpace p.period p.ν := by
      exact z.property
    exact ((mem_graphSpace (P := p.period) (ν := p.ν)).1 hz).2
  have htrace := hasPhaseOp_T0X (p.graphX z)
  have hrep := rep_real_ae_of_realSub_and_drift w (T0X (p.graphX z))
    ENNReal.ofReal_ne_top htrace hgraph
  have hcont := contRep_ae w
  have hrealC_reP (v : CVec3) : realC (reP v) = ofReV (reV v) := by
    ext i
    simp [realC_apply, reP, ofReV_apply, reV_apply]
  have hcont' : (fun x : ℝ × Space => p.corr z x.1 x.2) =ᵐ[
      (volume : Measure ℝ).prod (volume : Measure Space)]
      fun x => reP (rep w x.1 x.2) := by
    rw [← Measure.volume_eq_prod ℝ Space]
    simpa only [Params.corr, w] using hcont
  have hcorr : (fun x : ℝ × Space => realC (p.corr z x.1 x.2)) =ᵐ[
      (volume : Measure ℝ).prod (volume : Measure Space)]
      fun x => rep w x.1 x.2 := by
    filter_upwards [hcont', hrep] with x hc hr
    calc
      realC (p.corr z x.1 x.2) = realC (reP (rep w x.1 x.2)) := by rw [hc]
      _ = ofReV (reV (rep w x.1 x.2)) := hrealC_reP _
      _ = rep w x.1 x.2 := hr.symm
  have hpoint (x : ℝ × Space) :
      realC (((p.scheme B).field z x.1) x.2) =
        p.Ufun x + p.eFun (p.coord z) x + realC (p.corr z x.1 x.2) := by
    ext i
    simp [BackgroundScheme.field, Params.scheme, Params.Ufun, Params.eFun,
      realC_apply, realC, Pi.single_apply]
  filter_upwards [hcorr] with x hx
  rw [hpoint x, hx]
  exact add_assoc _ _ _

#print axioms Params.schemeField_eq_rawAddState_ae

end UnforcedLeray.Cons.C03.Concrete
