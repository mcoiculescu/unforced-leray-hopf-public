import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.RecvConv.Defs


set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace

/-- **(i) The exact multiplier** (source 4147, 2706, 3876-3877): the repair component of `M_Uw` is
`repG w` a.e. for `s^{-1/2}dς`. Exact multiplier pin at `gainHTMeasure`, then the null-set
transfer `ae_gainHTMeasure`, `ae_htRhoMeasure` (as in `repPhasePointwise`). -/
theorem RecvConvOrg.recvExact : RecvConvOrg.RecvExact := by
  intro Pl K L μ hC0 hnear hs w
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hrhoRep : 0 < rhoRep K L := by
    unfold rhoRep
    exact mul_pos (Real.rpow_pos_of_pos hε _) (Real.exp_pos _)
  have hρpos : 0 < L.ρb Pl K := by
    rw [rhoB_eq]
    exact mul_pos (mul_pos hC0 (pow_pos (inv_pos.2 hν) _)) hrhoRep
  -- the exact multiplier
  have hEx : IsExactMultiplier (concreteBase Pl K L μ hnear) L.ε⁻¹ L.V L.rb :=
    concreteBase_isExactMultiplier (h := hnear) NearInst.multPinOfLink hs
  have hEx2 := (hEx w).2
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρpos] at hEx2
  exact hEx2

end UnforcedLeray.Short.PartIIIb.Concrete
