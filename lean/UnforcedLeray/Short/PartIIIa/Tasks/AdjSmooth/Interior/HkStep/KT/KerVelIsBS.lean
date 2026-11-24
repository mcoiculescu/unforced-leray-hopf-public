import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.AdjFubini
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarField
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelDivFree
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelCurl

/-!
# `KerVelIsBS`: the kernel velocity of a test is its kernel Biot-Savart velocity

Source: `the November 2 reference manuscript` (SP) lines 3052-3058.
The three clauses of `IsKernelBiotSavart` at `u = kerVel d ψ` are the far field, the divergence
free property and the curl identity, each proved in its own leaf file.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem kerVelIsBS : UnforcedLeray.Short.IIIa.KerVelIsBS := by
  intro d hd ψ hψ
  exact ⟨fun j => kerVelFarField_of kerNearFar d hd ψ hψ j,
    fun φ hφ => kerVelDivFree_of (kerAdjFubini_of kerNearFar) (kerDivPointwise_of kerNearFar)
      d hd ψ hψ φ hφ,
    fun φ hφ => kerVelCurl_of (kerAdjFubini_of kerNearFar) (kerCurlPointwise_of kerNearFar)
      d hd ψ hψ φ hφ⟩

end UnforcedLeray.Short.IIIa
