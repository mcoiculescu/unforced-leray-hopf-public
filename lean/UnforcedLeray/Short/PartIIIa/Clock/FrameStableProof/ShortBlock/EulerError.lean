import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_3
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError.Residual

/-!
# Part III-a, task `PartIII-a:T21/c3/3/3`: linearised Euler eigenmode error (`ComplModeForceEulerError`, SP 2866-2888, 2991-2995)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2888
and 2991-2995.

`complModeForceEulerError_of` (`Sub/PartIII-a_T21_c3_3_3.lean`) reduces the statement to the
Gaussian-cylinder eigenmode residual `MovEulerGaussSubBound κ`, after the rescaled BUC train
comparison `O(ν³/θ) = O(d⁻²)`. The residual bound is proved for the Part I seed kernels in
`EulerError/Residual.lean` (`EulerErrorTail.movEulerGaussSubBound_seed`), from

* the classical planar eigen equation `L₀ e_j = λ_j e_j` of the seed modes
  (`EulerError/Eigen.lean`, `EulerErrorEig.seedPlanarPointwiseEigen`),
* the Gaussian periodization tails of `e_j`, `∇e_j`, `v₀` and `∇ω₀` on the cell
  (`EulerError/Tail.lean`, `tail_gauss`),
* the cylinder versus planar velocity comparison `K_d - K_∞ = O(d⁻²|x - y|)` near the core and
  the Gaussian smallness of the source and of `∇ω₀` away from it
  (`EulerError/Velocity.lean`, `vel_compare`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **`ComplModeForceEulerError`** (`PartIII-a:T21/c3/3/3`, SP 2866-2888, 2991-2995): the
periodized linearised Euler eigenmode defect `L_{ν,c}(r) E_j - λ_j E_j` is a.e. strongly
measurable and `≤ C₂ ν³ / θ(r)` in `X_{m,d(r)}`. -/
theorem complModeForceEulerError (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplModeForceEulerError κ := by
  intro hκ
  exact complModeForceEulerError_of κ (EulerErrorTail.movEulerGaussSubBound_seed κ hκ) hκ

end UnforcedLeray.Short.IIIa
