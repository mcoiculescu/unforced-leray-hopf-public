import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.AdjFubini
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarField
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelDivFree
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelCurl

/-!
# `PartIII-a:T21/2/7/1/7/4/1`: existence of the kernel Biot-Savart velocity (`locBSExists`)

Source: `the November 2 reference manuscript` lines 2875-2896, 3052-3057.

For `c ≥ 1` and a cylinder test `ψ`, the velocity `u = kerVel c ψ` satisfies
`IsKernelBiotSavart c ψ u`. The three clauses are the far-field (`KerVelFarField`), divergence
free (`KerVelDivFree`) and curl (`KerVelCurl`) leaves, assembled from the near/far split
`KerNearFar` as in `KernelAdjointBound` (`KernelAdjoint.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem locBSExists : LocBSExists := by
  intro c hc ψ hψ
  have hNF : KerNearFar := kerNearFar
  have hFub : KerAdjFubini := kerAdjFubini_of hNF
  have hFar : KerVelFarField := kerVelFarField_of hNF
  have hD : KerVelDivFree := kerVelDivFree_of hFub (kerDivPointwise_of hNF)
  have hC : KerVelCurl := kerVelCurl_of hFub (kerCurlPointwise_of hNF)
  refine ⟨kerVel c ψ, ?_⟩
  exact ⟨hFar c hc ψ hψ, hD c hc ψ hψ, hC c hc ψ hψ⟩

end UnforcedLeray.Short.IIIa
