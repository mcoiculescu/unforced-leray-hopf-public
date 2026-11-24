import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1
import UnforcedLeray.Lib.CylinderB.BiotSavart

/-!
# Part III-a, `PartIII-a:T21/2/1/2`: the periodic Biot-Savart kernel `K_d` and its adjoint

Source of record: `the November 2 reference manuscript` (SP).

* SP 3052-3057: "The adjoint localized interaction maps `X_{-m,d}` to `H^1_{-m,d}` uniformly: its
  localized source has uniformly bounded `L¹` and `L²` norms [...]; split the Biot-Savart kernel
  into its integrable near part and bounded far part, and use the uniform order-zero multiplier
  bound for its derivative, including the horizontal mean."
* SP 2876-2881, 3142-3147: `K_d` is the paired-image (symmetrically summed) periodization of the
  planar kernel; SP 2117-2121: it is uniformly bounded away from its common local `1/|x-y|`
  singularity; SP 2084, 3121: `K_d` is the cylindrical Biot-Savart operator and includes the
  horizontal mean mode; SP 2254-2259: order-zero multipliers on the nonzero modes, the mean mode
  by a primitive.

## The objects

* `kerD d z`: the periodic Biot-Savart kernel of the cylinder `C_d = (ℝ/dℤ) × ℝ`, the components
  of `UnforcedLeray.Cyl.bsKernel d z = (Re K, -Im K)` with
  `K(z) = (2πi)⁻¹ (π/d) cot(πz/d) = (2πi)⁻¹ (1/z + Σ_{n≥1} [1/(z-nd) + 1/(z+nd)])`
  (`Kernels.cylinderBS_eq_paired`: the paired-image sum of the planar kernel
  `(-η, q)/(2π|z|²) = ∇^⊥ (2π)⁻¹ log|z|`). Its far field is the horizontal mean shear
  `-(1/(2d)) sign(η) e_q` (`meanShear`, `Clock/WeakSmoothing/Adjoint.lean`).
* `kerVel d ψ x = ∫_{C_d} ψ(y) K_d(x - y) dy`: the kernel velocity `K_dψ` of a test.
* `kerAdj d F y = ∫_{C_d} F(x) · K_d(x - y) dx`: the adjoint `χ = K_d^T F`, so that
  `∫ χ ψ = ∫ F · K_dψ` (Fubini).

## The leaf statements (each a task of `PartIII-a:T21/2/1/2`)

* `KerNearFar` (SP 2117-2121, 2876-2881): measurable, `d`-periodic, odd; uniformly in `d ≥ 1`,
  integrable on the unit ball of the cell and bounded off it.
* `KerAdjSplit` (SP 3054-3056): `K_d^T F = a + b` with `‖a‖_{L²} ≤ C‖F‖_{L²}` (near part,
  Young) and `|b| ≤ C‖F‖_{L¹}` (far part, including the horizontal mean).
* `XNormSplitLe m` (`m > 1`): `‖a + b‖_{X_{-m,d}} ≤ ‖a‖_{L²} + C sup|b|`, since
  `∫_{ℝ²} ⟨y⟩^{-2m} < ∞` and `⟨y⟩^{-2m} ≤ 1`.
* `KerAdjFubini`: `∫ (K_d^T F) ψ = ∫ F · K_dψ` with absolute convergence (`F ∈ L¹`).
* `KerDivPointwise`, `KerCurlPointwise`: `∫ K_d(x-y)·∇φ(x) dx = 0` and
  `∫ (K_d(x-y)_q ∂_ηφ - K_d(x-y)_η ∂_qφ)(x) dx = φ(y)` (`K_d = ∇^⊥G_d`, `ΔG_d = Σ_n δ_{nd e_q}`).
* `KerVelFarField`, `KerVelDivFree`, `KerVelCurl`: the three clauses of
  `IsKernelBiotSavart d ψ (kerVel d ψ)` (existence half; uniqueness is `KernelBiotSavartUnique`,
  the Liouville argument of `Short/PartIII-a/T20_2_BiotSavartUnique.lean`).
* `KerVelDerivBound` (SP 3056-3057, 2254-2259): the order-zero multiplier bound
  `‖(K_d ∂_kψ)_j‖_{L²} ≤ ‖ψ‖_{L²}` for tests, including the horizontal mean.
* `WeakDerivOfBoundedPairing`: a field whose pairing with `∂_kψ` is bounded by `M‖ψ‖_{L²}` has a
  weak derivative `∂_k` in `L²` of norm `≤ 2M` (Riesz representation, real and imaginary parts).

The assembly `kernelAdjointBound_of` is in `KernelAdjointOf.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The kernel, the kernel velocity and the adjoint -/

/-- **The periodic Biot-Savart kernel** `K_d` of the cylinder `C_d` (SP 2876-2881, 3121,
3142-3147), component `j` (`0`: `e_q`, `1`: `e_η`): `UnforcedLeray.Cyl.bsKernel d z`, the
paired-image sum of the planar kernel `(-η, q)/(2π|z|²)`, i.e. `(Re K, -Im K)` for
`K(z) = (2πi)⁻¹ (π/d) cot(πz/d)`. At the lattice points `dℤ × {0}` (a null set) it is `0`. -/
def kerD (d : ℝ) (z : ℝ × ℝ) (j : Fin 2) : ℝ := UnforcedLeray.Cyl.bsKernel d z j

/-- **The kernel velocity** `K_dψ(x) = ∫_{C_d} ψ(y) K_d(x - y) dy` of a real field `ψ` on the
cylinder (SP 2081-2084, 3052-3057: `K_d` includes the horizontal mean mode). -/
def kerVel (d : ℝ) (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) (j : Fin 2) : ℝ :=
  ∫ y in B0579.cell d, ψ y * kerD d (x - y) j

/-- **The adjoint** `χ = K_d^T F`, `χ(y) = ∫_{C_d} F(x) · K_d(x - y) dx`, of a complex vector
field `F` on the cell (SP 3052-3057: the adjoint localized interaction applied to
`F = Φ∇E_mov`). -/
def kerAdj (d : ℝ) (F : Fin 2 → ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  ∫ x in B0579.cell d, ∑ j, F j x * ((kerD d (x - y) j : ℝ) : ℂ)

/-! ## The kernel bounds -/

/-- **Near/far bounds of the periodic kernel** (SP 2117-2121: "uniformly bounded away from its
common local `1/|x-y|` singularity"; SP 2876-2881, 3054-3055: integrable near part, bounded far
part, the far part containing the horizontal mean `∓1/(2d)`). Uniformly in `d ≥ 1`: `K_d` is
measurable, `d`-periodic in `q`, odd, `∫_{C_d ∩ {‖z‖_∞ < 1}} |K_d| ≤ C`, and `|K_d| ≤ C` on the
rest of the cell. -/
def KerNearFar : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 1 ≤ d →
    (∀ j : Fin 2, Measurable fun z => kerD d z j) ∧
    (∀ (z : ℝ × ℝ) (j : Fin 2), kerD d (z.1 + d, z.2) j = kerD d z j) ∧
    (∀ (z : ℝ × ℝ) (j : Fin 2), kerD d (-z) j = -kerD d z j) ∧
    (∫⁻ z in B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ j, ‖kerD d z j‖ₑ) ≤
      ENNReal.ofReal C ∧
    (∀ z ∈ B0579.cell d, z ∉ Metric.ball (0 : ℝ × ℝ) 1 → ∀ j, |kerD d z j| ≤ C)

/-- **Near/far split of the adjoint** (SP 3054-3056): uniformly in `d ≥ 1`, for `F ∈ L¹ ∩ L²(C_d)`
the adjoint `K_d^T F` is a.e. on the cell the sum of a near part `a` with
`‖a‖_{L²} ≤ C Σ_j ‖F_j‖_{L²}` (Young with the integrable near kernel) and a far part `b` with
`|b| ≤ C Σ_j ‖F_j‖_{L¹}` everywhere (bounded far kernel, including the horizontal mean). -/
def KerAdjSplit : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 1 ≤ d → ∀ F : Fin 2 → ℝ × ℝ → ℂ,
    (∀ j, IntegrableOn (F j) (B0579.cell d) ∧ MemLp (F j) 2 (volume.restrict (B0579.cell d))) →
    ∃ a b : ℝ × ℝ → ℂ,
      kerAdj d F =ᵐ[volume.restrict (B0579.cell d)] a + b ∧
      MemLp a 2 (volume.restrict (B0579.cell d)) ∧
      eLpNorm a 2 (volume.restrict (B0579.cell d)) ≤
        ENNReal.ofReal C * ∑ j, eLpNorm (F j) 2 (volume.restrict (B0579.cell d)) ∧
      AEStronglyMeasurable b (volume.restrict (B0579.cell d)) ∧
      ∀ y, ‖b y‖ₑ ≤ ENNReal.ofReal C * ∑ j, eLpNorm (F j) 1 (volume.restrict (B0579.cell d))

/-- **The weighted norm of an `L² + L^∞` field** (SP 3053-3056, weighted Cauchy-Schwarz): for
`m > 1` there is `C` (`C² = ∫_{ℝ²} ⟨y⟩^{-2m}`) such that on every cell, if `f = a + b` a.e. with
`|b| ≤ B`, then `‖f‖_{X_{-m,d}} ≤ ‖a‖_{L²(C_d)} + C B` (`⟨y⟩^{-2m} ≤ 1`). -/
def XNormSplitLe (m : ℝ) : Prop :=
  1 < m → ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → ∀ (f a b : ℝ × ℝ → ℂ) (B : ℝ≥0∞),
    f =ᵐ[volume.restrict (B0579.cell d)] a + b →
    AEStronglyMeasurable a (volume.restrict (B0579.cell d)) →
    AEStronglyMeasurable b (volume.restrict (B0579.cell d)) →
    (∀ y, ‖b y‖ₑ ≤ B) →
    xNorm d (-m) f ≤ eLpNorm a 2 (volume.restrict (B0579.cell d)) + ENNReal.ofReal C * B

/-! ## Duality and the Biot-Savart property of the kernel velocity -/

/-- **The duality (Fubini) identity** (SP 3052-3057, the definition of the adjoint): for
`F ∈ L¹(C_d)` and a test `ψ`, `(K_d^T F) ψ` is integrable on the cell and
`∫ (K_d^T F) ψ = ∫ F · K_dψ` (absolute convergence: near kernel integrable, far kernel bounded,
`ψ` bounded with bounded support in the cell). -/
def KerAdjFubini : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ F : Fin 2 → ℝ × ℝ → ℂ, (∀ j, IntegrableOn (F j) (B0579.cell d)) →
    ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ →
      IntegrableOn (fun y => kerAdj d F y * (ψ y : ℂ)) (B0579.cell d) ∧
      ∫ y in B0579.cell d, kerAdj d F y * (ψ y : ℂ) =
        ∫ x in B0579.cell d, ∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ)

/-- **The kernel is divergence free** (`K_d = ∇^⊥G_d`, `G_d = (4π)⁻¹ log(cosh(2πη/d) -
cos(2πq/d))`; SP 2081-2084, 3121): for every test `φ` and every `y`,
`∫_{C_d} K_d(x - y) · ∇φ(x) dx = 0`. -/
def KerDivPointwise : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest d φ → ∀ y : ℝ × ℝ,
    ∫ x in B0579.cell d,
      (kerD d (x - y) 0 * B0579.pd 0 φ x + kerD d (x - y) 1 * B0579.pd 1 φ x) = 0

/-- **The kernel has curl `δ`** (`K_d = ∇^⊥G_d` with `ΔG_d = Σ_n δ_{(nd, 0)}`, the periodic
fundamental solution; SP 2081-2084, 3121): for every test `φ` and every `y`,
`∫_{C_d} (K_d(x-y)_q ∂_ηφ(x) - K_d(x-y)_η ∂_qφ(x)) dx = φ(y)`. -/
def KerCurlPointwise : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest d φ → ∀ y : ℝ × ℝ,
    ∫ x in B0579.cell d,
      (kerD d (x - y) 0 * B0579.pd 1 φ x - kerD d (x - y) 1 * B0579.pd 0 φ x) = φ y

/-- **Far field of the kernel velocity** (first clause of `IsKernelBiotSavart`; SP 3056-3057,
the horizontal mean): for a test `ψ` of circulation `Γ = ∫_{C_d} ψ`, `K_dψ` minus the mean shear
`-(Γ/(2d)) sign(η) e_q` is in `L²(C_d)`. -/
def KerVelFarField : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → ∀ j : Fin 2,
    MemLp (fun x => kerVel d ψ x j - meanShear d (∫ y in B0579.cell d, ψ y) x j) 2
      (volume.restrict (B0579.cell d))

/-- **The kernel velocity is divergence free** (second clause of `IsKernelBiotSavart`). -/
def KerVelDivFree : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ →
    ∀ φ, B0579.IsCylTest d φ →
      ∫ x in B0579.cell d, (kerVel d ψ x 0 * B0579.pd 0 φ x + kerVel d ψ x 1 * B0579.pd 1 φ x) = 0

/-- **The kernel velocity has curl `ψ`** (third clause of `IsKernelBiotSavart`). -/
def KerVelCurl : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ →
    ∀ φ, B0579.IsCylTest d φ → ∫ x in B0579.cell d, ψ x * φ x =
      ∫ x in B0579.cell d, (kerVel d ψ x 0 * B0579.pd 1 φ x - kerVel d ψ x 1 * B0579.pd 0 φ x)

/-- **Uniqueness of the kernel Biot-Savart velocity** (Liouville on the cylinder, as in
`Short/PartIII-a/T20_2_BiotSavartUnique.lean`): two fields with `IsKernelBiotSavart d ψ` differ by
an `L²` field with zero divergence and zero curl, hence agree a.e. on the cell. -/
def KernelBiotSavartUnique : Prop :=
  ∀ d : ℝ, 0 < d → ∀ (ψ : ℝ × ℝ → ℝ) (u v : ℝ × ℝ → Fin 2 → ℝ),
    IsKernelBiotSavart d ψ u → IsKernelBiotSavart d ψ v →
      ∀ᵐ x ∂(volume.restrict (B0579.cell d)), u x = v x

/-! ## The order-zero multiplier and the weak derivative -/

/-- **The uniform order-zero multiplier bound** (SP 3056-3057 "the uniform order-zero multiplier
bound for its derivative, including the horizontal mean"; SP 2254-2259): for every test `ψ`,
`K_d(∂_kψ) = ∂_k(K_dψ)` has every component in `L²(C_d)` with norm `≤ ‖ψ‖_{L²(C_d)}`
(nonzero modes: symbol `|ξ_k ξ^⊥_j|/|ξ|² ≤ 1`; mean mode: `(K_d ∂_η ψ̄)_q = -ψ̄`), uniformly
in `d ≥ 1`. -/
def KerVelDerivBound : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → ∀ k j : Fin 2,
    MemLp (fun x => kerVel d (B0579.pd k ψ) x j) 2 (volume.restrict (B0579.cell d)) ∧
    eLpNorm (fun x => kerVel d (B0579.pd k ψ) x j) 2 (volume.restrict (B0579.cell d)) ≤
      eLpNorm ψ 2 (volume.restrict (B0579.cell d))

/-- **Weak derivative from a bounded pairing** (Riesz representation on `L²(C_d)`, applied to the
real and imaginary parts; this turns the multiplier bound into `∇χ ∈ L²`): if
`ψ ↦ ∫_{C_d} χ ∂_kψ` converges absolutely and is bounded by `M ‖ψ‖_{L²(C_d)}` on tests, then `χ`
has a weak derivative `∂_kχ = g ∈ L²(C_d)` with `‖g‖_{L²} ≤ 2M`. -/
def WeakDerivOfBoundedPairing : Prop :=
  ∀ d : ℝ, 0 < d → ∀ (χ : ℝ × ℝ → ℂ) (k : Fin 2) (M : ℝ≥0∞), M ≠ ⊤ →
    (∀ ψ, B0579.IsCylTest d ψ →
      IntegrableOn (fun x => χ x * (B0579.pd k ψ x : ℂ)) (B0579.cell d) ∧
      ‖∫ x in B0579.cell d, χ x * (B0579.pd k ψ x : ℂ)‖ₑ ≤
        M * eLpNorm ψ 2 (volume.restrict (B0579.cell d))) →
    ∃ g : ℝ × ℝ → ℂ, HasWeakCellDerivC d k χ g ∧
      MemLp g 2 (volume.restrict (B0579.cell d)) ∧
      eLpNorm g 2 (volume.restrict (B0579.cell d)) ≤ 2 * M

end UnforcedLeray.Short.IIIa
