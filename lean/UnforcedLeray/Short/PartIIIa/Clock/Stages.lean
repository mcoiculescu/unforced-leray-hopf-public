import UnforcedLeray.Short.PartIIIa.FullClock
import UnforcedLeray.Short.PartIIIa.Clock.Restart

/-!
# Part III-a full clock: stage statements (SP 2818-3105, `prop:short-full-clock`)

`FullClock.lean` is already stated over the concrete objects: the actual train `tr`, and weak
solutions `IsLinearisedFlow` of the linearised vorticity equation around it. The moving-coordinate
objects of the source (`G(z)`, `F-bar`, `E(z)`, `Λ(z)`, `𝓑`) enter only inside the proof; each
stage below is stated as an estimate on `IsLinearisedFlow` solutions, so no free predicate
stands in for a source object. Stages follow SP 3030-3094:

* `ShortWeakSmoothing` (C6): SP 3040-3084, the weak-to-strong cost on gaps `0 < s - t ≤ 1`.
* `ZeroCirculationPreserved` (C7, last line SP 3092-3094): zero mass is preserved.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Zero circulation is preserved by every weak linearised flow in `X_{m,c}`, `m > 1`
(SP 3092-3094).  No train property beyond `B0140.IsTrain` is used (no BUC hypothesis): the
velocity `u s` of the flow is an `L²(C_c)` Biot-Savart field (`IsLinearisedFlow.biotSavart`), which
forces `∫_{C_c} w s = 0` (`Clock/Sub/ZeroCircLeaves.lean`). -/
def ZeroCirculationPreserved : Prop :=
  ∀ ν c m : ℝ, 0 < c → 1 < m → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, ∀ t : ℝ,
    ∀ f w u, IsLinearisedFlow ν c m tr t f w u → HasZeroCirculation c f →
      ∀ s, t ≤ s → HasZeroCirculation c (w s)

/-- **Short weak smoothing** (SP 3040-3084): on gaps `0 < s - t ≤ 1` inside the core
`s ≤ H = coreEnd ν b`, for the weak linearised flow from `f ∈ X_{m,c}`,
`(g(t)/g(s)) ‖w(s)‖_{X_{m,c}} ≤ C_b ν^{-(m+2)/2} (s-t)^{-1/2} ‖f‖_{(H^1_{-m,c})^*}`
(physical form of the moving bound `C_b(β_min Δz)^{-1/2}` with the scalings
`eq:short-causal-scales` and the clock identities of SP 3077-3082).  The train is in the BUC
class `PartI.IsBUCTrain` (SP 270-288): the proof uses that "the rescaled train and its first two
derivatives are uniformly bounded for `θ ≥ b`" (SP 3050-3051), which `B0140.IsTrain` does not
give (`Short/PartI/TrainClass.lean`). -/
def ShortWeakSmoothing : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
    ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ t s : ℝ, 0 < t → t < s → s - t ≤ 1 → s ≤ coreEnd ν b →
          ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
            ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
              ENNReal.ofReal (gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s) *
                  xNorm (ν ^ (-2 : ℝ)) m (w s) ≤
                ENNReal.ofReal (C * ν ^ (-((m + 2) / 2)) * (s - t) ^ (-1 / 2 : ℝ)) *
                  negNorm (ν ^ (-2 : ℝ)) m f

end UnforcedLeray.Short.IIIa
