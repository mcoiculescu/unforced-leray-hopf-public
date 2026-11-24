import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Short.PartIIa.Tasks.F05HomogeneousUniqueness

/-!
# Part II-a, task `PartII-a:F15`: distributional uniqueness of the weak stress (reduction)

Source of record: `the November 2 reference manuscript`,
lines 1548-1549 ("subtracting two solutions and applying the homogeneous uniqueness argument").

`weakStressUnique_of` proves `WeakStressUnique` from three step Props:
* `WSUSolenoidal` (S_μ T is solenoidal),
* `WSUWeakEq` (S_μ T satisfies the weak equation against solenoidal phase tests),
* `WSUPressure` (a solenoidal distribution annihilated by the equation tested on solenoidal tests
  is annihilated on all tests: gradient parts drop out, 𝐏 commutes with the phase operator),
and the homogeneous uniqueness `bodyOp_uniqueness` at `r = 2` (F05).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- (F15/1, lines 1537, 1548) For a weak stress inverse `S_μ`, the field `S_μ T` is solenoidal.
Smooth `T`: `S_μ T ∈ D_2` solves `(μ+L)w = 𝐏 div G` with solenoidal right side, and 𝐏 commutes
with the body resolvent (F08), so `w` is solenoidal; rough `T` by density
(`SmoothTensorsDense`) and closedness (`isClosed_isPhaseSolenoidal`) with continuity of `S`. -/
def WSUSolenoidal : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ S : symY2 P →L[ℂ] Yq P 2, IsWeakStressInverse P ν μ S → ∀ T : symY2 P,
      IsPhaseSolenoidal (S T)

/-- (F15/2, lines 1537, 1548) `S_μ T` satisfies the weak equation
`⟨(μ+L^t)Φ, S_μ T⟩ = -⟨∇Φ, T⟩` for solenoidal phase tests `Φ`: for smooth `T` by the definition of
`D_2` (adjoint pairing) and `⟨Φ, 𝐏 div G⟩ = ⟨Φ, div G⟩ = -⟨∇Φ, G⟩`; for rough `T` by density and
continuity of both sides in `T`. -/
def WSUWeakEq : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ S : symY2 P →L[ℂ] Yq P 2, IsWeakStressInverse P ν μ S → ∀ T : symY2 P,
      ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ → (∀ p, ∑ j, dy j Φ p j = 0) →
        phasePair P 2 (μ • Φ + L0T ν Φ) (S T) = -tensorGradPair P Φ (T : Y2Sym P)

/-- (F15/3, lines 1498-1500, 1548) Pressure extension: a solenoidal `v ∈ Y_2` with
`⟨(μ+L^t)Φ, v⟩ = 0` for all solenoidal phase tests `Φ` has `⟨(μ+L^t)Φ, v⟩ = 0` for all phase
tests (write `Φ = 𝐏Φ + ∇ψ`; `𝐏` commutes with `μ+L^t`, `(μ+L^t)∇ψ` is a gradient, and `v` is
solenoidal). -/
def WSUPressure : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ μ : ℂ, ∀ v : Yq P 2, IsPhaseSolenoidal v →
    (∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ → (∀ p, ∑ j, dy j Φ p j = 0) →
      phasePair P 2 (μ • Φ + L0T ν Φ) v = 0) →
    HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) v (0 : Yq P 2)

/-- Reduction of `WeakStressUnique` to the three step Props and F05. -/
theorem weakStressUnique_of (h1 : WSUSolenoidal) (h2 : WSUWeakEq) (h3 : WSUPressure) :
    WeakStressUnique := by
  intro P _ _ ν hν μ hμ S hS T w hws hweq
  have hsol : IsPhaseSolenoidal (w - S T) := by
    intro φ hφ
    rw [map_sub, hws φ hφ, h1 P ν hν μ hμ S hS T φ hφ, sub_zero]
  have hzero : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) (w - S T) (0 : Yq P 2) := by
    refine h3 P ν hν μ _ hsol ?_
    intro Φ hΦ hdiv
    rw [map_sub, hweq Φ hΦ hdiv, h2 P ν hν μ hμ S hS T Φ hΦ hdiv, sub_self]
  have hg : gammaR 2 = 1 / 4 := by
    unfold gammaR
    norm_num
  have := bodyOp_uniqueness 2 (by norm_num) (by norm_num) P ν hν μ (by rw [hg]; exact hμ)
    (w - S T) hzero
  exact sub_eq_zero.mp this

end UnforcedLeray.Short.PartIIa
