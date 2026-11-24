import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_14
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvRegular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TranspClass

/-!


Composes `convRegular` (`ConvRegular`) with `transpClass` (`TranspClass`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

theorem pd_per_r (c : ℝ) {g : B0579.Plane → ℝ} (hg : ∀ x : B0579.Plane, g (x.1 + c, x.2) = g x)
    (j : Fin 2) (y : B0579.Plane) :
    B0579.pd j g (y.1 + c, y.2) = B0579.pd j g y := by
  have e : ∀ x : B0579.Plane, x + ((c : ℝ), (0 : ℝ)) = (x.1 + c, x.2) := fun x =>
    Prod.ext (by simp) (by simp)
  have hfun : (fun x : B0579.Plane => g (x + ((c : ℝ), (0 : ℝ)))) = g :=
    funext fun x => by rw [e]; exact hg x
  have h1 : fderiv ℝ g (y + ((c : ℝ), (0 : ℝ))) = fderiv ℝ g y := by
    rw [← fderiv_comp_add_right ((c : ℝ), (0 : ℝ)) (f := g) (x := y), hfun]
  unfold B0579.pd
  rw [← e y, h1]

/-- **`PartII-b:T22/1/14/4`** one Picard step: `ConvRegular` composed with `TranspClass`. -/
theorem picStep_proof : UnforcedLeray.Short.IIb.CylPDE.PicStep := by
  intro c ν s T v hc hν hs hsT hC
  have hCR : UnforcedLeray.Short.IIb.CylPDE.ConvRegular := convRegular
  have hTC : UnforcedLeray.Short.IIb.CylPDE.TranspClass := transpClass
  obtain ⟨K1, hK1, hConv⟩ := hCR ν s T hν hsT
  obtain ⟨K2, hK2, hTr⟩ := hTC c s T v hC hs hsT
  refine ⟨K1, K2, hK1, hK2, ?_⟩
  intro u b hu hb hb0 hbound
  obtain ⟨hFR, hWBt⟩ := hTr u b hu.c2 hu.cont0 hu.cont1 hu.cont2 hbound
  have hPT : ∀ r ∈ Icc s T, ∀ y : B0579.Plane,
      transp v u r (y.1 + c, y.2) = transp v u r y := by
    intro r hr y
    have hr0 : r ∈ Icc 0 T := ⟨hs.trans hr.1, hr.2⟩
    unfold transp
    rw [hC.periodic r hr0 y, pd_per_r c (hu.periodic r hr) 0 y, pd_per_r c (hu.periodic r hr) 1 y]
  obtain ⟨hD, hC0, hC1, hC2, hPer, hW⟩ :=
    hConv (transp v u) hFR (fun r => K2 * b r) (continuousOn_const.mul hb)
      (fun r hr => mul_nonneg hK2 (hb0 r hr))
      (fun r hr => ⟨(hWBt r hr).1, (hWBt r hr).2⟩)
  refine ⟨⟨fun σ hσ => (hD σ hσ).1, fun σ hσ x => hPer c hPT σ hσ x, hC0, hC1, hC2⟩,
    hFR, fun r hr => (hWBt r hr).1, hW⟩

end CylPDE

end UnforcedLeray.Short.IIb

end
