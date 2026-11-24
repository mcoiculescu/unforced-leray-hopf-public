import UnforcedLeray.Units.B0421.Phase
import UnforcedLeray.Short.PartIIa.StatementsFree

/-!
# Part II-a, task `PartII-a:F02`, helper: the phase semigroup as an `ExpSemigroup`

Helper for `Tasks/F02BodyResolventEquation.lean`. It packages the phase-translated free semigroup
`𝒯(t) = phaseT t` as an exponentially bounded semigroup with growth rate `-γ_r` (constant `2`,
`B0421.norm_freeC_le`), and reduces the body-resolvent equation to a Laplace-transform statement
for that semigroup, taken as a hypothesis `hlap`. This file does not use `Units/B0421/Equation.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- The phase semigroup `𝒯` at exponent `r` (with `1 < r < 3`, `ν ≥ 0`) as an
exponentially bounded semigroup on `Y_r`. -/
def bodySemigroup (r : ℝ≥0∞) [Fact (1 ≤ r)] (h3 : r < 3) (P : ℝ) [Fact (0 < P)] (nu : ℝ)
    (hnu : 0 ≤ nu) : Infra.ExpSemigroup (Yq P r) :=
  B0421.phaseSemigroup (P := P) (ne_top_of_lt h3) hnu 2 zero_le_two
    (fun s _ => B0421.norm_freeC_le (ne_top_of_lt h3) nu s)

theorem bodySemigroup_T (r : ℝ≥0∞) [Fact (1 ≤ r)] (h3 : r < 3) (P : ℝ) [Fact (0 < P)]
    (nu : ℝ) (hnu : 0 ≤ nu) (t : ℝ) :
    (bodySemigroup r h3 P nu hnu).T t = B0421.phaseT (ne_top_of_lt h3) nu t :=
  rfl

theorem bodySemigroup_omega (r : ℝ≥0∞) [Fact (1 ≤ r)] (h3 : r < 3) (P : ℝ) [Fact (0 < P)]
    (nu : ℝ) (hnu : 0 ≤ nu) :
    (bodySemigroup r h3 P nu hnu).ω = -B0418.gammaExp r :=
  rfl

/-- **Reduction of `PartII-a:F02` to the Laplace equation for `𝒯`.** Given the Laplace-transform
identity `hlap` for the phase semigroup (`(μ + L₀)(R_μ h) = h` in distributions for every
`μ` with `ω < Re μ`), the Laplace integral `Rm f = ∫₀^∞ e^{-μt} 𝒯(t) f dt` solves the body
equation. The growth condition `0 < Re μ + γ_r` gives `ω < Re μ`. -/
theorem bodyResolvent_solves_of_laplace (r : ℝ≥0∞) [Fact (1 ≤ r)] (h3 : r < 3)
    (P : ℝ) [Fact (0 < P)] (nu : ℝ) (hnu : 0 < nu) (mu : ℂ) (hmu : 0 < mu.re + gammaR r)
    (hlap : ∀ μ : ℂ, (bodySemigroup r h3 P nu hnu.le).ω < μ.re → ∀ h : Yq P r,
      HasPhaseOp (fun Φ => μ • Φ + B0411.L0T nu Φ)
        ((bodySemigroup r h3 P nu hnu.le).laplace μ h) h)
    (Rm : Yq P r →L[ℂ] Yq P r)
    (hRm : ∀ f, Rm f = ∫ t in Set.Ioi (0:ℝ),
      Complex.exp (-(mu * t)) • B0421.phaseT (ne_top_of_lt h3) nu t f)
    (f : Yq P r) :
    HasPhaseOp (fun Φ => mu • Φ + B0411.L0T nu Φ) (Rm f) f := by
  set S : Infra.ExpSemigroup (Yq P r) := bodySemigroup r h3 P nu hnu.le with hSdef
  have hg : gammaR r = B0418.gammaExp r := rfl
  have hω : S.ω < mu.re := by
    rw [hSdef, bodySemigroup_omega]
    linarith [hg]
  have heq : Rm f = S.laplace mu f := by
    rw [hRm f, S.laplace_apply hω]
    rfl
  rw [heq]
  exact hlap mu hω f

end UnforcedLeray.Short.PartIIa
