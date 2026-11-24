import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.SolenoidalConj

/-!
# `pepsRealForm` (task `PartIII-b:C/near/pins/3/1`)

Source `the November 2 reference manuscript` 1675-1677, 1339-1362, 4139-4146.

`P_ε` commutes with conjugation (`Body.pepsC_conj`, from `Body.solenoidalConj`), and a real chart
form `f` gives a conjugation-fixed `h'`.  Hence `P_ε h'` is conjugation-fixed a.e., so it is real
a.e., and `wk x := Body.merReL (P_ε h' (cellPtInv x))` is its real chart form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

theorem pepsRealForm : PepsRealForm := by
  intro p f h' hf
  have hc : 0 < p.c := p.c_pos
  -- h' is conjugation fixed
  have hreal : Body.cjLp (measureH p.c) 2 h' = h' := by
    apply Lp.ext
    filter_upwards [Body.coeFn_cjLp (measureH p.c) 2 h', hf] with q h1 h2
    rw [h1, h2, Body.conjV_merC]
  -- P_ε h' is conjugation fixed
  have hreal' : Body.cjLp (measureH p.c) 2 (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c h') =
      UnforcedLeray.Short.PartIIa.PepsC p.ε p.c h' := by
    rw [← Body.pepsC_conj Body.solenoidalConj p.ε p.c h', hreal]
  have hfix := Body.coeFn_cjLp (measureH p.c) 2 (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c h')
  rw [hreal'] at hfix
  refine ⟨fun x => Body.merReL ((UnforcedLeray.Short.PartIIa.PepsC p.ε p.c h' : Profile → MeridC)
      (Masked.cellPtInv p.c x)), ?_⟩
  unfold ChartRep
  filter_upwards [hfix, Body.ae_mem_cell p.c] with q h1 hq
  obtain ⟨-, ⟨h0, hcq⟩, -⟩ := hq
  have hcell : Masked.cellPtInv p.c (cellPt p.c q) = q := Masked.cellPtInv_cellPt h0 hcq
  show (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c h' : Profile → MeridC) q =
    merC (Body.merReL ((UnforcedLeray.Short.PartIIa.PepsC p.ε p.c h' : Profile → MeridC)
      (Masked.cellPtInv p.c (cellPt p.c q))))
  rw [hcell]
  exact (Body.merC_merReL h1.symm).symm

end UnforcedLeray.Short.PartIIIb.NearInst
