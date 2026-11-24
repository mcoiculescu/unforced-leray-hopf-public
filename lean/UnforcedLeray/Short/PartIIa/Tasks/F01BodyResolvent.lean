import UnforcedLeray.Short.PartIIa.Sub.F01
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent.NormLift
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent.HeatPositivity

/-!
# Part II-a, task `PartII-a:F01`: the body resolvent `R_μ` (unconditional)

Source of record: `the November 2 reference manuscript`, lines 1363-1368.

The conditional statement `bodyResolvent_exists_of` (in `Sub/F01.lean`) takes the sharp decay
`FreeCSharpDecay` as hypothesis. Here that hypothesis is discharged by `freeCSharpDecay_of`,
applied to the two leaf results `normLiftExists_proof` (`Tasks/F01BodyResolvent/NormLift.lean`)
and `freeCPointwiseLe_proof` (`Tasks/F01BodyResolvent/HeatPositivity.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **`PartII-a:F01`**: existence of the body resolvent `R_μ : Y_r → Y_r` with
`‖R_μ‖ ≤ (Re μ + γ_r)⁻¹`, given by the Laplace integral of the free semigroup `𝒯_ν`. -/
theorem bodyResolvent_exists (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h3 : r < 3) (P : ℝ)
    [Fact (0 < P)] (nu : ℝ) (hnu : 0 < nu) (mu : ℂ) (hmu : 0 < mu.re + gammaR r) :
    ∃ Rm : Yq P r →L[ℂ] Yq P r, ‖Rm‖ ≤ (mu.re + gammaR r)⁻¹ ∧
      ∀ f, Rm f = ∫ t in Set.Ioi (0:ℝ),
        Complex.exp (-(mu * t)) • B0421.phaseT (ne_top_of_lt h3) nu t f := by
  exact bodyResolvent_exists_of (freeCSharpDecay_of normLiftExists_proof freeCPointwiseLe_proof)
    r h1 h3 P nu hnu mu hmu

end UnforcedLeray.Short.PartIIa
