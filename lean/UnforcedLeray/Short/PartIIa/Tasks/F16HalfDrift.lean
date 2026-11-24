import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F16
import UnforcedLeray.Short.PartIIa.Tasks.F16aBodyInverseBounded
import UnforcedLeray.Short.PartIIa.Tasks.F16bBodyDirectGraph
import UnforcedLeray.Short.PartIIa.Tasks.F16cBodyAdjointGraph
import UnforcedLeray.Short.PartIIa.Tasks.F16dTensorDivRiesz
import UnforcedLeray.Short.PartIIa.Tasks.F12TensorDensity
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Short.PartIIa.Tasks.F07Surjective

/-!
# Part II-a, task `PartII-a:F16`: the half-drift bound `WeakStressHalfDrift`

Source of record: `the November 2 reference manuscript`,
lines 1585-1598. Assembles the four leaves (`F16/a`-`F16/d`), smooth tensor density (`F12`),
and common body bijectivity (`F06`, `F07`) into `weakStressHalfDrift_of` (`Sub/PartII-a_F16.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

private theorem bodyOp_injective_F16 (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (h1 : 1 < r) (h3 : r < 3) (P : ℝ) [Fact (0 < P)] (hP1 : P ≤ 1) (ν : ℝ) (hν : 0 < ν)
    (μ : ℂ) (hμ : 0 < μ.re + gammaR r) : Function.Injective (bodyOp P ν r μ) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨C, _, hC⟩ := commonBodyGraphBound r h1 h3
  obtain ⟨g, -, hg⟩ := hC P hP1 ν hν μ hμ w
  rw [hw, norm_zero, mul_zero] at hg
  have h0 : 0 ≤ Real.sqrt ν * ∑ j, ‖g j‖ := by positivity
  have hw0 : graphNormD w ≤ 0 := by linarith
  have hn : ‖(w : Yq P r)‖ ≤ 0 := by
    have h2 := norm_nonneg (nuLapD w)
    have h3' := norm_nonneg (T0D w)
    unfold graphNormD at hw0
    linarith
  exact Subtype.ext (norm_le_zero_iff.1 hn)

private theorem commonBodyBijective_F16 : CommonBodyBijective := by
  intro r _ h1 h3 P _ hP1 ν hν μ hμ
  exact ⟨bodyOp_injective_F16 r h1 h3 P hP1 ν hν μ hμ,
    commonBodySurjective r h1 h3 P hP1 ν hν μ hμ⟩

/-- **`PartII-a:F16`**: the half-drift bound `WeakStressHalfDrift` (source lines 1585-1598). -/
theorem weakStressHalfDrift : WeakStressHalfDrift :=
  weakStressHalfDrift_of commonBodyBijective_F16 smoothTensorsDense
    bodyInverseBounded bodyDirectGraph bodyAdjointGraph tensorDivRiesz

end UnforcedLeray.Short.PartIIa
