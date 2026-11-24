import UnforcedLeray.Lib.HeatR3.Continuity
import UnforcedLeray.Lib.HeatR3.Comm
import UnforcedLeray.Statement

/-!
# B0223 helper: the space of `τ`-periodic fields on `ℝ³`

Blueprint unit B0223 (label `eq:st18-t00116`), `paper/main.tex` lines 3341–3368.

The outer semigroup `S_ε(t)` (tex lines 3348–3352) acts on fields `F(x, τ)`, `x ∈ ℝ³`, that
are `τ`-periodic of period `P = 2εc` (tex line 3289), with the norm of `L²(dx dτ)` over one
period (tex lines 3294–3301). We realize this space as `L²(ℝ³ × (ℝ/Pℤ); E)` with the product
of Lebesgue measure and the Haar measure of total mass `P` on the circle `AddCircle P`
(`PSpace P`, `X E P`). The coefficient space `E` is any complex Banach space (`ℂ` for scalar
fields, `ℂ³` for vector fields in Cartesian components): the resolvent parameter `μ` is
complex, so the resolvent acts on complex-valued fields.

This file checks the instances the heat package (`Lib/HeatR3`, INF04 T3, bypass BP1) needs on
this group: second countability, translation invariance (`IsAddRightInvariant`), regularity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UnforcedLeray.B0223

/-- Space times the phase circle: `ℝ³ × (ℝ/Pℤ)`, the domain of a `τ`-periodic field of period
`P` (tex lines 3289, 3348–3352). -/
abbrev PSpace (P : ℝ) := Space × AddCircle P

/-- The periodic `L²` space `L²(dx dτ; E)` over one period `P` (tex lines 3294–3301): Lebesgue
measure on `ℝ³` times the Haar measure of total mass `P` on `ℝ/Pℤ`. -/
abbrev X (E : Type*) [NormedAddCommGroup E] (P : ℝ) [Fact (0 < P)] :=
  Lp E 2 (volume : Measure (PSpace P))

variable (P : ℝ) [Fact (0 < P)]

instance : (volume : Measure (PSpace P)).IsAddRightInvariant := by
  change ((volume : Measure Space).prod (volume : Measure (AddCircle P))).IsAddRightInvariant
  infer_instance

example : SecondCountableTopology (PSpace P) := inferInstance
example : BorelSpace (PSpace P) := inferInstance
example : IsTopologicalAddGroup (PSpace P) := inferInstance
example : SigmaFinite (volume : Measure (PSpace P)) := inferInstance
example : (volume : Measure (PSpace P)).InnerRegularCompactLTTop := inferInstance
example : IsLocallyFiniteMeasure (volume : Measure (PSpace P)) := inferInstance
example : R1Space (PSpace P) := inferInstance
example : (volume : Measure (PSpace P)).Regular := inferInstance
example : NormalSpace (PSpace P) := inferInstance
example : WeaklyLocallyCompactSpace (PSpace P) := inferInstance

theorem volume_pspace : (volume : Measure (PSpace P)) =
    (volume : Measure Space).prod (volume : Measure (AddCircle P)) := rfl

end UnforcedLeray.B0223
