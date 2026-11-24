import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.PairInt
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.BSExists
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.AdjChi

/-!
# `PartIII-a:T21/2/7/1/7/4`: pointwise localized kernel adjoint (`locAdjPointwise_of`)

Source: `the November 2 reference manuscript` lines 3052-3058, 2875-2896.

Assembles `LocAdjPointwise m` from the linear-operator construction `locAdjPointwise_of_chi`
(`Sub/PartIII-a_T21_2_7_1_7_4.lean`) with the pairing integrability `locPairInt`, the cylinder
fundamental lemma is supplied through `hU`, the kernel Biot-Savart existence `locBSExists`, and
the kernel adjoint `locAdjChi`. The hypotheses `hK` and `hF` are not needed for this assembly:
`locAdjChi` derives its own field bound from `locFieldBound`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem locAdjPointwise_of (m : ℝ) (hm : 8 < m) (hK : KernelAdjointBound m) (hU : LocCylUniq)
    (hF : LocFieldBound m) : LocAdjPointwise m :=
  locAdjPointwise_of_chi m (locPairInt m hm) hU locBSExists (locAdjChi m hm)

end UnforcedLeray.Short.IIIa
