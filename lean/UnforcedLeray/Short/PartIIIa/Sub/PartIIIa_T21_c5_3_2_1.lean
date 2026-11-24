import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.GaussCore
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound.SubBound.PlanarDualMain

/-!
# Part III-a, task `PartIII-a:T21/c5/3/2/1`: the planar seed duality `L₀^* λ_k = λ_k λ_k`

Source of record: `the November 2 reference manuscript` (SP), lines 593-610
(`eq:short-seed-functional`) and 2891-2918.

For the Part I seed kernels, `v₀·∇λ_k - K_∞^T(λ_k ∇ω₀) = λ_k λ_k` on the plane, with
`λ₀ = lam`, `λ₁ = conj lam` (`EulerSubCore.PlanarSeedEulerDual`).

Proof: unpack `IsSeedKernels κ` into the seed triple `(lam, h, hh, ℓ)` with its three
identifications and apply `PlanarDualSub.seedPlanarDualEigen` (helper of the accepted task
`PartIII-a:T21/c5/2/2/2`, `DirectError/EulerSubBound/SubBound/PlanarDualMain.lean`), which proves
the identity for the realizing seed triple: `λ₀ = c G(|y|) e^{-2iϑ}` with
`G = greenN 2 h/(Ω - i lam/2)` (`CutFTCGradPerSum.seedDualExplicit`), `v₀·∇λ₀ = -2iΩλ₀`, the
eigen relation `k G = h`, `K_∞^T(λ₀∇ω₀)(y) = -c y·(K q̃)(y)` with `q̃ = h(|y|) e^{-2iϑ}`, the
sector identity `y·(K q̃) = 2i greenN 2 h(|y|) e^{-2iϑ}`, and conjugation for `λ₁ = conj λ₀`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **Planar seed duality** (`PartIII-a:T21/c5/3/2/1`, SP 593-610, 2891-2918):
`v₀·∇λ_k - K_∞^T(λ_k ∇ω₀) = λ_k λ_k` for the Part I seed kernels. -/
theorem planarSeedEulerDual (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.EulerSubCore.PlanarSeedEulerDual κ := by
  intro hκ
  obtain ⟨lam, h, hh, ℓ, hIS, he0, he1, hpair⟩ := id hκ
  exact ⟨lam, PlanarDualSub.seedPlanarDualEigen κ hκ lam h hh ℓ hIS he0 he1 hpair⟩

end UnforcedLeray.Short.IIIa
