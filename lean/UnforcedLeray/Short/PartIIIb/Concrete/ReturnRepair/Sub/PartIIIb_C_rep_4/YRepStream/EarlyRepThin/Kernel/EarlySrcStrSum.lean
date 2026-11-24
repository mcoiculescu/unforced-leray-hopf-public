import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.Bridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Level
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.ChiOStrApply

/-!
# `earlySrcStrSum` (source 5303-5308, 4163-4166): the early source is `(1-χ_o)T₂`.

`(id - χ_o)(repPart T)` has thin component `0` and repair component `T₂ - χ_oT₂`, which is
the representative `ertTen T` of the early source.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem earlySrcStrSum : EarlySrcStrSum := by
  intro Pl K L hC0 T
  have hρ : 0 < L.ρb Pl K := inv_rhoB_pos hC0
  have hX0 : (repPart T).fst = 0 := by simp [repPart]
  have hXs : (repPart T).snd = T.snd := by simp [repPart]
  have hA := chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν _ K.hχo (repPart T)
  have hB := chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν _ K.hχo T
  have e0 : ((repPart T).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]
      (0 : Chart → Ten3) := by
    rw [hX0]
    exact Lp.coeFn_zero _ _ _
  have fst_ae : ∀ᵐ p ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν),
      ((repPart T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (repPart T)).fst
        : Chart → Ten3) p = 0 := by
    have hsub : (repPart T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
        (repPart T)).fst = (repPart T).fst -
          (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (repPart T)).fst := rfl
    rw [hsub]
    filter_upwards [Lp.coeFn_sub (repPart T).fst
      (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (repPart T)).fst, hA.1, e0]
      with p h1 h2 h3
    rw [h1]
    simp only [Pi.sub_apply]
    rw [h2, h3]
    simp
  have snd_ae : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν),
      ((repPart T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (repPart T)).snd
        : Chart → Ten3) p = ((T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T).snd
        : Chart → Ten3) p := by
    have hsub1 : (repPart T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
        (repPart T)).snd = (repPart T).snd -
          (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (repPart T)).snd := rfl
    have hsub2 : (T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T).snd =
        T.snd - (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T).snd := rfl
    rw [hsub1, hsub2]
    filter_upwards [Lp.coeFn_sub (repPart T).snd
      (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (repPart T)).snd,
      Lp.coeFn_sub T.snd (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T).snd,
      hA.2, hB.2] with p h1 h2 h3 h4
    rw [h1, h2]
    simp only [Pi.sub_apply]
    rw [h3, h4, hXs]
  rw [NearInst.ae_gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν, NearInst.ae_z1Measure (cOf L.ν) K.mZ] at fst_ae
  rw [NearInst.ae_gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν, NearInst.ae_htRhoMeasure hρ] at snd_ae
  simp only [sub_apply, ContinuousLinearMap.id_apply]
  unfold ertTen
  filter_upwards [fst_ae, snd_ae] with p h1 h2
  simp only [strSum]
  rw [h1, h2, zero_add]

end UnforcedLeray.Short.PartIIIb.Concrete
