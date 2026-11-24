import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.FarKernel.Bridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.FarKernel.Recv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Reduce

/-!
# `PartIII-b:C/rep/4/4/1/org/5/1/org` (c): `FarRepThinUng` from the bridge and the receiver

Source `the November 2 reference manuscript` 5303-5306 (far mask `s < S`,
`t > e^δs`, `S = ε^{-b}`), 3902-3920 and 3621 (`S_far = 1_{s<S,t>e^δs}S_μ`, `sep:resolvent`),
3593-3594 (completion from smooth tensors), 5323-5338 ("the repair-to-thin entry uses the pointwise
exponent `79/22`"), 5345-5355 (pointwise velocity, normalized lift, thin multiplication, the age
integral up to `S` polynomial in `S`), 2713-2721, 3631-3647.

`farRepThinUng_of`: the ungained bridge `RepFarSepBridgeUng` (`FarKernel/Bridge.lean`) applied to
the receiver bound `FarThinRecvUng` (`FarKernel/Recv.lean`) on far-kernel outputs of box tensors
gives the leaf `FarRepThinUng` of `LateRepThinOrg/Props.lean`, with the same S-degree `k₀ = 2`.

`farRepThinUng_of_leaves`: the same from the remaining leaves, all shared with
`PartIII-b:C/rep/4/4/1/org/7/1/org` (`EarlyRepThin/Kernel/Bridge.lean`, `…/ThinRecv.lean`) or with
task `PartIII-b:C/rep/5/1/1/1`:

* `StrBoxTrunc` (box truncation of a stress; 3593-3594),
* `SopSubIsFarSeq` (`S_μ - S_N = S_far` with the kernel realization; 3902-3920, 5785),
* `FarOutChartQ` (Tonelli, `L^∞_q × L²_q`, one cell one phase period; 2666-2689, 2713-2721),
* `FarOutPointwise` (`sep:young` pointwise on the masked source; 3631-3647, 3905-3912),
* `EtaQSupSeq` (the coefficient bound of `stress-short:coefficients`, 2717),
* `FarRecvIntegral` (`∫_0^S s^{23/11}ds ≤ S^{34/11}`; 5352-5353).

Since `FarRepThinUng` also gives `EarlyRepThinKernel` (`earlyRepThinKernel_of_farRepThinUng`,
`LateRepThinOrg/EarlyThinBridge.lean`), one proof closes both thin-receiver repair entries.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(c) The ungained far-kernel leaf from the bridge and the receiver** (source 5303-5306,
3902-3920, 3593-3594, 5323-5338). -/
theorem farRepThinUng_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h1 : RepFarSepBridgeUng Pl σ₀ mZ dm dp) (h2 : FarThinRecvUng Pl σ₀ mZ dm dp) :
    FarRepThinUng Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := h2
  refine ⟨k₀, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨C, k, hC, hev⟩ := hk D hPl hσ hmZ hst
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [h1 D hPl hσ hmZ hst, hev] with n h1n h2n z hz T
  exact h1n z hz _ (fun v f hf hv => h2n z hz v f hf.measurable hv) T

/-- **`FarRepThinUng` from the shared leaves** (source 3593-3594, 3902-3920, 5303-5306, 5323-5338,
5345-5355, 2713-2721, 3631-3647). -/
theorem farRepThinUng_of_leaves (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (h1 : StrBoxTrunc)
    (h2 : SopSubIsFarSeq Pl σ₀ mZ dm dp) (hQ : FarOutChartQ) (hP : FarOutPointwise)
    (hE : EtaQSupSeq dm dp) (hI : FarRecvIntegral) : FarRepThinUng Pl σ₀ mZ dm dp :=
  farRepThinUng_of Pl σ₀ mZ dm dp (repFarSepBridgeUng_of Pl σ₀ mZ dm dp h1 h2)
    (farThinRecvUng_of Pl σ₀ mZ dm dp hQ hP hE hI)

/-- **Both thin-receiver repair entries** from the shared leaves (source 5303-5308, 5318-5319,
5323-5338): the late-output entry `LateRepThin` and the early-source kernel `EarlyRepThinKernel`. -/
theorem lateRepThin_earlyRepThinKernel_of_leaves (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h1 : StrBoxTrunc) (h2 : SopSubIsFarSeq Pl σ₀ mZ dm dp) (hQ : FarOutChartQ)
    (hP : FarOutPointwise) (hE : EtaQSupSeq dm dp) (hI : FarRecvIntegral) :
    LateRepThin Pl σ₀ mZ dm dp ∧ EarlyRepThinKernel Pl σ₀ mZ dm dp :=
  ⟨lateRepThin_of_farRepThinUng Pl σ₀ mZ dm dp
      (farRepThinUng_of_leaves Pl σ₀ mZ dm dp h1 h2 hQ hP hE hI),
    earlyRepThinKernel_of_farRepThinUng Pl σ₀ mZ dm dp
      (farRepThinUng_of_leaves Pl σ₀ mZ dm dp h1 h2 hQ hP hE hI)⟩

end UnforcedLeray.Short.PartIIIb.Concrete
