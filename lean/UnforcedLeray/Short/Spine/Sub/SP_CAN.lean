import UnforcedLeray.Short.PartI.StatementsCanonical
import UnforcedLeray.Cons.L2.CanonicalBranch

/-!
# Spine: `Cons.C01.CanonicalBranchHyp` from Part I's canonical branch (task `Spine:SP-CAN`)

Source of record: `the November 2 reference manuscript`, `prop:short-canonical`
(lines 1075-1150), with `lem:short-compact-duhamel` (978-1000) and `lem:short-diffusion-complement`
(1005-1070).

The Part I area proves the canonical branch for a seed triple `IsSeedXG lam q ℓ` as an `X_G`-valued
curve (`Short.PartI.CanonicalBranch`, tasks `PartI:C06`-`C11`). The Spine needs it in the form
`Cons.C01.CanonicalBranchHyp` (whole-line mode `(c, F)`, classical profiles `Profile`). This file
reduces the second to the first by an adapter with four precise bridge Props, each a true source
fact:

* `WholeLineModeIsSeed` (lines 593-609, 602): the whole-line mode `q = qMode hF`, with `ℓ = ⟨q†, ·⟩`
  and `λ = -2ic`, is a Part I seed triple (simplicity of the sole growing eigenvalue,
  `Short.PartI.SeedXGSpectrum`);
* `WholeLineModeKappa` (lines 970-975): the Part I constant `κ = ℓ(Dq)` is the profile-level
  `kapMode c F = gaussianPairing (oscillatorD (modeVort c F)) (adjointMode c F)`;
* `StrongCanonicalIsMild` (lines 1094-1150; old manuscript lines 1809-1840): an `X_G`-valued
  strong solution of `-V' = (L₀ + θ⁻¹D)V` on `(0, ∞)` is the mild solution through the concrete
  backward evolution `S` (`Cons.G3b.S`);
* `Cons.G3b.ClassicalRegularityHyp` (old manuscript lines 1879-1888, B0124; already stated in
  `Cons/L2/CanonicalBranch.lean`): a mild solution has a jointly smooth classical representative.

`canonicalBranchHyp_of` is the conditional theorem; the unconditional `canonicalBranchHyp` is the
task `Spine:SP-CAN` (`Short/Spine/Proofs/CanonicalBranch.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Bridge 1** (lines 593-609, 602): for a whole-line Gaussian Rayleigh mode `(c, F)` of O8, the
triple `(λ, q, ℓ) = (-2ic, qMode hF, ⟨qdagMode hF, ·⟩)` is a seed triple of Part I: `Re λ > 0`,
`q ≠ 0`, `L₀ q = λ q`, `ℓ q = 1`, and `qℓ` is the Riesz projection of the simple isolated
eigenvalue `λ` of `L₀` on `X_G`. Proof: `λ` is in the right half plane and an eigenvalue, so by
`Short.PartI.SeedXGSpectrum` it is the sole growing eigenvalue of the Part I seed, simple, hence
`q` is a multiple of the seed eigenvector, and `ℓ` (a left eigenfunctional,
`Cons.G3b.inner_qdagMode_L0`) is the corresponding multiple of the seed functional
(`Short.PartI.adjoint_eigenvector_unique`, task `PartI:S08`), normalized by `ℓ q = 1`. -/
def WholeLineModeIsSeed : Prop :=
  ∀ (c : ℂ) (F : ℝ → ℂ) (hF : WholeLineData c F),
    PartI.IsSeedXG (lamMode c) (qMode hF) (innerSL ℂ (qdagMode hF))

/-- **Bridge 2** (lines 970-975): the Part I constant `κ = ℓ(Dq)` of the whole-line mode is the
profile-level `κ = ⟨Dq, q†⟩` of `Cons.C01.CanonicalBranchHyp`. Proof: the oscillator `D` acts on
the Gaussian-class representative `modeVort c F` by `oscillatorD` (`PlanarSpectral.modeVort_mem_Ddomain`),
and `gaussianPairing_eq_inner` converts the pairing. -/
def WholeLineModeKappa : Prop :=
  ∀ (c : ℂ) (F : ℝ → ℂ) (hF : WholeLineData c F),
    PartI.seedKappa (innerSL ℂ (qdagMode hF)) (qMode hF) (qMode_mem_Ddomain hF) = kapMode c F

/-- **Bridge 3** (lines 1094-1150; old manuscript lines 1809-1840): an `X_G`-valued strong solution
of `-V' = (L₀ + θ⁻¹D)V` on `(0, ∞)` (`PartI.IsCanonicalSolution`) satisfies `V(θ) = S(θ, θ')V(θ')`
for `0 < θ ≤ θ'`, with `S` the Dyson backward evolution of `Cons/L2/CanonicalBranch/Evolution.lean`.
Proof: apply the free semigroup `e^{log(θ'/u)D}` to the equation, differentiate `u ↦ E(θ,u)V(u)`
on `[θ, θ']` (`V(u) ∈ 𝒟(D)`), obtain the Duhamel identity for `V`, and conclude by uniqueness of
the Duhamel (Dyson) equation with bounded `L₀` (Gronwall, `Cons.G3b.S_mild`, `norm_S_le`). -/
def StrongCanonicalIsMild : Prop :=
  ∀ V : ℝ → B0010.XG, PartI.IsCanonicalSolution V →
    ∀ θ θ' : ℝ, 0 < θ → θ ≤ θ' → V θ = S θ θ' (V θ')

/-- **`Cons.C01.CanonicalBranchHyp` from Part I's `CanonicalBranch`** and the four bridges. -/
theorem canonicalBranchHyp_of (hCan : PartI.CanonicalBranch) (hSeed : WholeLineModeIsSeed)
    (hKap : WholeLineModeKappa) (hMild : StrongCanonicalIsMild)
    (hReg : ClassicalRegularityHyp) : CanonicalBranchHyp := by
  intro c F hF
  obtain ⟨V, hVsol, hVasy, ⟨Cb, hCb⟩, -, -⟩ :=
    hCan (lamMode c) (qMode hF) (innerSL ℂ (qdagMode hF)) (hSeed c F hF) (qMode_mem_Ddomain hF)
  rw [hKap c F hF] at hVasy
  have hXG : IsXGCanonicalBranch (lamMode c) (kapMode c F) (qMode hF) V := by
    refine ⟨hMild V hVsol, hVsol.smooth.continuousOn, ⟨Cb, hCb⟩, ?_⟩
    obtain ⟨C, b, hb, hA⟩ := hVasy
    refine ⟨C, b, hb, fun θ hθ => ?_⟩
    have h := hA θ hθ
    have e : Cons.G3b.gauge (lamMode c) (kapMode c F) θ • V θ =
        Complex.exp (lamMode c * θ) • (θ : ℂ) ^ (kapMode c F) • V θ := by
      unfold Cons.G3b.gauge
      rw [mul_smul]
    rw [e]
    exact h
  obtain ⟨W, hWV, hWs, hWe⟩ := hReg V hXG.mild
  obtain ⟨hB, hX⟩ := isCanonicalBranch_of_rep (coeFn_qMode hF) hXG hWV hWs hWe
  exact ⟨W, hB, continuousOn_quadCurve hB.memXG hX⟩

end UnforcedLeray.Short.Spine
