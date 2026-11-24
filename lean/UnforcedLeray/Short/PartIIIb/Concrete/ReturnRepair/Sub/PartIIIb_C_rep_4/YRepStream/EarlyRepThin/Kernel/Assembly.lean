import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.Bridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecv

/-!
# `PartIII-b:C/rep/4/4/1/org/7/1/org` (c): `EarlyRepThinKernel` from the bridge and the receiver

Source `the November 2 reference manuscript` 5303-5308, 5318-5319, 5323-5339
("the repair-to-thin entry uses the pointwise exponent `79/22`"), 3593-3594, 3902-3920.

`earlyRepThinKernel_of`: the bridge `EarlyFarSepBridge` (`Kernel/Bridge.lean`), applied with the
thin receiver `Φ = (·)₁ ∘ M_U ∘ χ_y`, and the receiver bound `FarThinRecv` (`Kernel/ThinRecv.lean`)
on far-kernel outputs of box tensors give `EarlyRepThinKernel` (`EarlyRepThin/Props.lean`), with
the same S-degree `k₀`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(c) The early-source kernel estimate on the thin receiver from (a) and (b)** (source
5303-5308, 5323-5339, 3593-3594). -/
theorem earlyRepThinKernel_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h1 : EarlyFarSepBridge Pl σ₀ mZ dm dp) (h2 : FarThinRecv Pl σ₀ mZ dm dp) :
    EarlyRepThinKernel Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := h2
  refine ⟨k₀, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨C, k, hC, hev⟩ := hk D hPl hσ hmZ hst
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [h1 D hPl hσ hmZ hst, hev] with n h1n h2n z hz T
  exact h1n z hz (LStr D.Pl D.K (D.level n))
    (thinPart.comp ((multOp D.Pl D.K (D.level n)).comp (youngMul hst.chiY)))
    (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
      (D.level n).ε ^ (79 / 22 : ℝ))
    (fun v f hf hv => h2n z hz v f hf.measurable hv) T

end UnforcedLeray.Short.PartIIIb.Concrete
