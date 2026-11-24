import UnforcedLeray.Cons.Data
import UnforcedLeray.Short.Spine.PartI

/-!
# Parameter choices made before the final spectral scan

Source: `the November 2 reference manuscript`, subsection "Phase selection and
the scalar crossing" (lines 5922-5985) and the paragraph at lines 217-222.

The reference `(planar data, σ₀)` is the draft record `Cons.Data.Reference`. Its base
`ConstructionData` (`Reference.base`) carries exactly the explicit formulas of the shorter proof:
* `ν_n ↓ 0` with `ω/ν_n - Im κ log ν_n + arg 𝒞(σ₀) = 2πn sign ω` (`phaseLockedNu`, proved
  to exist by `ConstructionData.stepPhaseLocked_of_C1`);
* `ε_n³ = e^{-γ/ν_n} ν_n^{Re κ - 5 - 2σ₀}/(2|𝒞(σ₀)|)` (`ConstructionData.amplitude`),
  `c_n = ν_n^{-2}` (`spacing`), `P_n = 2ε_nc_n` (`period`);
* `-ν_n log ε_n → d₀ = γ/3` (line 5970: "equivalently").
The shorter proof chooses `σ₀ ∈ (0,1/4)` with `𝒞(σ₀) ≠ 0`; any `σ₀ ∈ (1/16,1/8)` of the draft
`IsReferenceChoice` is such a choice (the identity theorem for the holomorphic `𝒥`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.Data

/-- The viscosities `ν_n` of the phase-locked sequence (lines 5945-5952). -/
def nuSeq (R : Reference) (n : ℕ) : ℝ := R.base.ν n

/-- The amplitudes `ε_n` (lines 5955-5958). -/
def epsSeq (R : Reference) (n : ℕ) : ℝ := R.base.amplitude n

/-- The loss exponent `d_n = -ν_n log ε_n` (line 5970), which tends to `d₀ = γ/3`. -/
def lossExponent (R : Reference) (n : ℕ) : ℝ := -(nuSeq R n) * Real.log (epsSeq R n)

/-- `σ₀ ∈ (0,1/4)` with `𝒞(σ₀) ≠ 0` exists for every Part I planar reference, in the form of the
draft `Reference.IsReferenceChoice`: from `𝒥` holomorphic and not identically zero on
`Re μ > -3/2` (lines 1155-1180), `ℓ_+(H₀) ≠ 0`, `Γ(σ+5/2) ≠ 0`, `λ ≠ 0` (lines 5925-5930, 5940). -/
def ReferenceFromInstability : Prop :=
  ∀ P : PlanarData, GaussianInstability P →
    ∃ R : Reference, R.planar = P ∧ R.IsReferenceChoice

/-- The explicit parameters have the properties used in the scan (lines 5945-5985): `ν_n > 0`,
`ν_n → 0`, `ε_n > 0`, and `d_n = -ν_n log ε_n → γ/3`, `γ = Re λ`. -/
def ParameterAsymptotics : Prop :=
  ∀ R : Reference, R.IsReferenceChoice →
    (∀ n, 0 < nuSeq R n) ∧ Tendsto (nuSeq R) atTop (𝓝 0) ∧ (∀ n, 0 < epsSeq R n) ∧
      Tendsto (lossExponent R) atTop (𝓝 (R.planar.eigenvalue.re / 3))

end UnforcedLeray.Short.Spine
