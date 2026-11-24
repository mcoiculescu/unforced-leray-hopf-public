import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.AdjFubini
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarField
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelDivFree
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelCurl
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwise

/-!
# `PartIII-a:T21/2/7/2/1/1/6/6`: the kernel velocity of a test is its Biot-Savart velocity (`KerVelIsBS`)

Source: `the November 2 reference manuscript` lines 3052-3057 (the near/far split of
the periodic Biot-Savart kernel, the horizontal mean, and the kernel velocity `K_dψ` of a test `ψ`).
The three clauses of `IsKernelBiotSavart` are the far-field, divergence-free and curl leaves, each
accepted in `Sub/T21_2_1/Kernel/`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

/-- **(6) The kernel velocity of a test is its kernel Biot-Savart velocity** (SP 3052-3057). -/
theorem kerVelIsBS : KerVelIsBS := by
  unfold KerVelIsBS
  intro d hd ψ hψ
  unfold IsKernelBiotSavart
  exact ⟨fun j => kerVelFarField_of kerNearFar d hd ψ hψ j,
    fun φ hφ => kerVelDivFree_of (kerAdjFubini_of kerNearFar) (kerDivPointwise_of kerNearFar)
      d hd ψ hψ φ hφ,
    fun φ hφ => kerVelCurl_of (kerAdjFubini_of kerNearFar) (kerCurlPointwise_of kerNearFar)
      d hd ψ hψ φ hφ⟩

end UnforcedLeray.Short.IIIa
