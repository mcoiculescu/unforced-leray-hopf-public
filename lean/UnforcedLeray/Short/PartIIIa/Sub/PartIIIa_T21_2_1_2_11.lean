import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.Unique

/-!


Source: `the November 2 reference manuscript`, lines 3056-3057 ("the uniform
order-zero multiplier bound for its derivative, including the horizontal mean"), 2254-2259.
Route: `kerVel d (∂_kψ)` is a kernel Biot-Savart velocity of the mean-zero test `∂_kψ`; by
`KernelBiotSavartUnique` it equals the Leray-projected field `P₀ (vec 0 ψ)` (`k = 0`) or
`P₀ (vec (-ψ) 0)` (`k = 1`), whose components have `L²` norm `≤ ‖ψ‖_{L²}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The derivative of a test has zero cell integral (`k = 0`: periodic FTC per `η`-slice and
Fubini; `k = 1`: `∂_η ψ` integrates to zero in `η` since `ψ` has bounded `η`-support). -/
def KerVelDerivMeanZero : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → ∀ k : Fin 2,
    ∫ y in B0579.cell d, B0579.pd k ψ y = 0

/-- The Leray field: for the test `ψ` and `k`, there is a kernel Biot-Savart field `u` of `∂_kψ`
whose components are `L²` with norm `≤ ‖ψ‖_{L²}` (take `u = P₀ f`, `f = vec 0 ψ` for `k = 0`,
`f = vec (-ψ) 0` for `k = 1`: `div u = 0` by `mem_divFree`, `curl u = curl f = ∂_kψ` by
`curl_P0` and one integration by parts, `‖P₀‖ ≤ 1`; `Lib/CylinderB/Leray.lean`). -/
def KerVelDerivLeray : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → ∀ k : Fin 2,
    ∃ u : ℝ × ℝ → Fin 2 → ℝ, IsKernelBiotSavart d (B0579.pd k ψ) u ∧ ∀ j : Fin 2,
      MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ∧
      eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ≤
        eLpNorm ψ 2 (volume.restrict (B0579.cell d))

theorem kerVelDerivBound_of_parts (hFar : KerVelFarField) (hD : KerVelDivFree) (hC : KerVelCurl)
    (hU : KernelBiotSavartUnique) (hL : KerVelDerivLeray) :
    KerVelDerivBound := by
  intro d hd ψ hψ k j
  obtain ⟨u, hu, hj⟩ := hL d hd ψ hψ k
  have hpd := hψ.pd k
  have hv : IsKernelBiotSavart d (B0579.pd k ψ) (fun x i => kerVel d (B0579.pd k ψ) x i) :=
    ⟨fun i => hFar d hd _ hpd i, fun φ hφ => hD d hd _ hpd φ hφ,
      fun φ hφ => hC d hd _ hpd φ hφ⟩
  have hae := hU d (by linarith) _ u _ hu hv
  have hcongr : (fun x => kerVel d (B0579.pd k ψ) x j) =ᵐ[volume.restrict (B0579.cell d)]
      (fun x => u x j) := by
    filter_upwards [hae] with x hx
    exact (congrFun hx j).symm
  refine ⟨(hj j).1.ae_eq hcongr.symm, ?_⟩
  rw [eLpNorm_congr_ae hcongr]
  exact (hj j).2
