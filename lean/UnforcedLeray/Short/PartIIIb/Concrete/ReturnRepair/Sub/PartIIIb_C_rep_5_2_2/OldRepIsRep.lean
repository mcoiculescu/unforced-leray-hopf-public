import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.ChiOStrApply

/-!
# `OldRepIsRep`: representatives of the old repair source

Source `the November 2 reference manuscript` 5153-5157 (the old source
`chi_o T` includes the repair), 4171-4174.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem oldRepIsRep : OldRepIsRep := by
  intro Pl K L w
  unfold IsRep oldRep
  have hX : (repPart (multOp Pl K L w)).fst = 0 := by simp [repPart]
  have hY : (repPart (multOp Pl K L w)).snd = (multOp Pl K L w).snd := by simp [repPart]
  obtain ⟨h1, h2⟩ := chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo
    (repPart (multOp Pl K L w))
  obtain ⟨_, h3⟩ := chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo
    (multOp Pl K L w)
  constructor
  · have hf : ((repPart (multOp Pl K L w)).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ
        (gRate Pl) L.ν] 0 := by
      rw [hX]
      exact Lp.coeFn_zero _ _ _
    filter_upwards [h1, hf] with p hp hp0
    rw [hp]
    simp only [hp0, Pi.zero_apply, smul_zero]
  · have hs : ((repPart (multOp Pl K L w)).snd : Chart → Ten3) =
        ((multOp Pl K L w).snd : Chart → Ten3) := by
      rw [hY]
    filter_upwards [h2, h3] with p hp hp3
    unfold repSrcTen
    rw [hp, hs]
    exact hp3.symm

end UnforcedLeray.Short.PartIIIb.Concrete
