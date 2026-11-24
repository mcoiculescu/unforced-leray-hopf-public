import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.Unique
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

/-!
# `PartIII-a:T21/2/2/3/6/1/1`: `KernelBSExists` from the kernel velocity of the periodic kernel

Source: `the November 2 reference manuscript` lines 2875-2896 (periodic kernel
`K_d`, paired images, horizontal mean), 3052-3057.  The kernel velocity `kerVel d ψ = K_d ψ`
(`∫_{C_d} ψ(y) K_d(x-y) dy`) is the Biot-Savart velocity: far field, divergence, curl.
The three clauses of `IsKernelBiotSavart` are the leaves below, stated for every `d > 0`
(the `d ≥ 1` versions in `T21_2_1/KernelDefs.lean` carry a uniformity restriction not needed
here; the proofs there adapt, since for fixed `d` all constants may depend on `d`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- Leaf (SP 3056-3057): `K_dψ - meanShear ∈ L²(C_d)` for every `d > 0`. -/
def KerVelFarField0 : Prop :=
  ∀ d : ℝ, 0 < d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → ∀ j : Fin 2,
    MemLp (fun x => kerVel d ψ x j - meanShear d (∫ y in B0579.cell d, ψ y) x j) 2
      (volume.restrict (B0579.cell d))

/-- Leaf: `K_dψ` is weakly divergence free, for every `d > 0`. -/
def KerVelDivFree0 : Prop :=
  ∀ d : ℝ, 0 < d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ →
    ∀ φ, B0579.IsCylTest d φ →
      ∫ x in B0579.cell d, (kerVel d ψ x 0 * B0579.pd 0 φ x + kerVel d ψ x 1 * B0579.pd 1 φ x) = 0

/-- Leaf: `K_dψ` has curl `ψ` weakly, for every `d > 0`. -/
def KerVelCurl0 : Prop :=
  ∀ d : ℝ, 0 < d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ →
    ∀ φ, B0579.IsCylTest d φ → ∫ x in B0579.cell d, ψ x * φ x =
      ∫ x in B0579.cell d, (kerVel d ψ x 0 * B0579.pd 1 φ x - kerVel d ψ x 1 * B0579.pd 0 φ x)

theorem kernelBSExists_of (h1 : KerVelFarField0) (h2 : KerVelDivFree0) (h3 : KerVelCurl0) :
    KernelBSExists := by
  intro d ψ hd hψ
  exact ⟨fun x j => kerVel d ψ x j, fun j => h1 d hd ψ hψ j, fun φ hφ => h2 d hd ψ hψ φ hφ,
    fun φ hφ => h3 d hd ψ hψ φ hφ⟩

end UnforcedLeray.Short.IIIa.AdjE1

#print axioms UnforcedLeray.Short.IIIa.AdjE1.kernelBSExists_of
