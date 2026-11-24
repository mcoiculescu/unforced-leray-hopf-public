import UnforcedLeray.Short.PartIIa.Sub.F02
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation.FreeTestGenAll

/-!
# Part II-a, task `PartII-a:F02`: the body resolvent solves `(μ + L₀)R_μ f = f` (unconditional)

Source of record: `the November 2 reference manuscript`, lines 1363-1370.

The conditional statement `bodyResolvent_solves_of_sub` (in `Sub/F02.lean`) takes the generator
identity `FreeTestGenAll` as hypothesis. Here that hypothesis is discharged by `freeTestGenAll`
(`Tasks/F02BodyResolventEquation/FreeTestGenAll.lean`, task `PartII-a:F02/11`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **`PartII-a:F02`**: the Laplace integral `Rm f = ∫₀^∞ e^{-μt} 𝒯(t) f dt` solves
`(μ + L₀)Rm f = f` in distributions. -/
theorem bodyResolvent_solves (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h3 : r < 3) (P : ℝ)
    [Fact (0 < P)] (nu : ℝ) (hnu : 0 < nu) (mu : ℂ) (hmu : 0 < mu.re + gammaR r)
    (Rm : Yq P r →L[ℂ] Yq P r)
    (hRm : ∀ f, Rm f = ∫ t in Set.Ioi (0:ℝ),
      Complex.exp (-(mu * t)) • B0421.phaseT (ne_top_of_lt h3) nu t f)
    (f : Yq P r) :
    HasPhaseOp (fun Phi => mu • Phi + B0411.L0T nu Phi) (Rm f) f :=
  bodyResolvent_solves_of_sub freeTestGenAll r h1 h3 P nu hnu mu hmu Rm hRm f

end UnforcedLeray.Short.PartIIa
