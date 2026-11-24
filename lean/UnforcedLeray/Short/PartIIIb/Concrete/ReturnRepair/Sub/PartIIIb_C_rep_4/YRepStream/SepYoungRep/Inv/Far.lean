import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.FarBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.Defs

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1/inv`: the young-region identity through the far bridge

Source `the November 2 reference manuscript`
3593-3594, 3596-3626, 3902-3912, 4163-4174, 5303-5306.

`S_μ F = S_N F + S_far F`; on the young receiver `ν s ≤ 1` the near part of the old stress
`F = χ_oG` vanishes (the young-old rectangle lies in the far mask, 5303-5306) and the far part of
any stress is the masked kernel response `farOut` wherever the order-zero gap majorant of the lifted
source is finite (`FarBridge.farBridge_ae_of`); where the mask is inactive that is `-W_μ`.
This file proves that assembly once, for an arbitrary stress `F` with chart representative `g`,
from the three facts that carry the content (`hSN`, `habs`, `hid`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The young-region value of `S_μ F` through the far bridge** (3593-3594, 3902-3912, 5303-5306):
`S_μ - S_N = S_far` with the box pin `IsFarMaskG`; the near part of `F` vanishes on the young
receiver (`hSN`); the order-zero gap majorant of the lifted source is finite at a.e. young receiver
(`habs`, absolute convergence of the masked `sep:resolvent` integral); and there the masked kernel
output `farOut` of the measurable representative `f` of `F₁ + F₂` is `-coefOf (wardW …)` (`hid`:
the mask is inactive for an old source, and `sepW` sees only the a.e. class of the source). -/
theorem youngFar_core (hD : FarBridge.FarOutTruncTendsto)
    {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    (hμ : -(1 / 4) < μ) (hδ : 0 < K.δ) (hρ : 0 < L.ρb Pl K)
    {Sf : LStr Pl K L →L[ℝ] LVel Pl L} (hSf : IsFarMaskG L.ε⁻¹ μ K.δ (L.Scut K) Sf)
    (hsplit : Sop Pl K L μ - SNop Pl K L μ = Sf)
    (F : LStr Pl K L) (g f : Chart → Ten3) (hf : Measurable f)
    (hFf : strSum F =ᵐ[ageμ (cOf L.ν) (-1 / 2)] f)
    (hSN : ∀ᵐ p ∂(ageμ (cOf L.ν) (-3 / 2)), L.ν * p.1 ≤ 1 →
      (SNop Pl K L μ F : Chart → Merid) p = 0)
    (habs : ∀ᵐ x ∂(ageμ (cOf L.ν) (-3 / 2)), L.ν * x.1 ≤ 1 →
      UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0
          ((1 - Real.exp (-(K.δ / 2))) * L.ε⁻¹ / Real.sqrt x.1)
          (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift L.ε⁻¹ (cOf L.ν) f))
          (NearInst.chartTau L.ε⁻¹ x) (NearInst.chartY L.ε⁻¹ x) < ⊤)
    (hid : ∀ᵐ x ∂(ageμ (cOf L.ν) (-3 / 2)), L.ν * x.1 ≤ 1 →
      NearInst.Masked.farOut L.ε⁻¹ (cOf L.ν) L.ν μ K.δ (L.Scut K) f x =
        -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) g) x) :
    ∀ᵐ p ∂(bodyMeasure (cOf L.ν) (gRate Pl) L.ν), L.ν * p.1 ≤ 1 →
      (Sop Pl K L μ F : Chart → Merid) p =
        -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) g) p := by
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hb := FarBridge.farBridge_ae_of hD (O := {p : Chart | L.ν * p.1 ≤ 1}) hR hc hρ L.ν_pos hμ
    hδ hSf hf hFf habs
  have hS : Sop Pl K L μ F = SNop Pl K L μ F + Sf F := by
    rw [← hsplit, sub_apply]
    abel
  have hadd := Lp.coeFn_add (SNop Pl K L μ F) (Sf F)
  rw [NearInst.ae_bodyMeasure]
  have hS' : (Sop Pl K L μ F : Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-3 / 2)]
      fun p => (SNop Pl K L μ F : Chart → Merid) p + (Sf F : Chart → Merid) p := by
    rw [← NearInst.ae_bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
    rw [hS]
    exact hadd
  filter_upwards [hS', hSN, hb, hid] with p h1 h2 h3 h4 hp
  rw [h1, h2 hp, zero_add, h3 hp, h4 hp]

end UnforcedLeray.Short.PartIIIb.Concrete
