import UnforcedLeray.Short.Spine.PartI
import UnforcedLeray.Short.Spine.Background

/-!
# Part II output: the exact unforced DSS background

Source: `the November 2 reference manuscript`, Part II (lines 1181-2645):
`sct:lift` (ring lift, lines 1205-1230), the free comparisons (lines 1338-2025) and
Section `short-bg:section` (lines 2026-2645), parameters `p = 11/4`, `c = ν^{-2}`, `R = ε⁻¹`,
`ε = e^{-d/ν}`, `P = 2εc`, `0 < dLo ≤ d ≤ dHi` (lines 2031-2035), loss exponent `m`
(`short-bg:result`, `short-bg:strong`, lines 2505-2560).

`PartIIOutput` states, for every planar reference `P` (Part I), a threshold `m₀` depending only on
the window (the contraction condition `2m < 3d₋/11`, lines 2510-2512), and for every loss exponent
`m ≤ m₀`: a slow terminal age `Σ` of the fixed inlet ("Choosing `Σ` large", lines 2337-2342; "the
fixed inlet stream with an age cutoff", lines 2316-2318), and a polynomial `P_ν = C ν^{-N}`
(constants may depend on `d_±`, `m` and the fixed inlet, not on `ν, ε`; lines 2033-2040), such that
at every `ε` with `d = -ν log ε ∈ [dLo, dHi]` and on every BUC train at `c = ν^{-2}` (Part I) the
exact background of `IsShortBackground` (`Short/Spine/Background.lean`) exists with the parameter
record `levelParams P ν ε Σ T` of that train: the contraction-ball state of `short-bg:result`
(lines 2505-2524) and its regularity and bounds (`short-bg:strong`, lines 2525-2562), datum, heat
remainder and pressure (lines 2563-2645). "The background construction realizes this `m₀`; all its
internal choices are then fixed" (lines 5856-5857).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar

/-- **Part II output** (`short-bg:result`, `short-bg:strong`, lines 2505-2562, with the datum,
heat remainder and pressure of lines 2563-2645), at the fixed inlet of slow age `Σ`. -/
def PartIIOutput : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ dLo dHi : ℝ, 0 < dLo → dLo ≤ dHi →
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ m : ℝ, 0 < m → m ≤ m₀ →
      ∃ (Sig : ℝ) (hSig : 0 < Sig) (ν₀ C : ℝ) (N : ℕ), 0 < ν₀ ∧ 0 < C ∧
        ∀ (ν : ℝ) (hν : ν ∈ Ioc 0 ν₀) (ε : ℝ) (hε : 0 < ε), -ν * Real.log ε ∈ Icc dLo dHi →
          ∀ T : B0140.TrainSol ν (Train.per ν), PartI.IsBUCTrain T →
            ∃ B : ShortBackground, B.par = levelParams P hν.1 hε hSig T ∧
              IsShortBackground P ν ε m C N Sig B

end UnforcedLeray.Short.Spine
