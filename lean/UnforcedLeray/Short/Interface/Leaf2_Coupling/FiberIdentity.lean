import UnforcedLeray.Short.Interface.Sub.I09

/-!
# Interface:I09 sub-lemma: the Leray fiber identity

Proves `LerayFiberIdentity` (Sub/I09.lean) with no hypothesis. Source of record:
`the November 2 reference manuscript`, lines 173-180 (the term
`𝔓 div(U_* ⊗ b_* + b_* ⊗ U_*)` of `loc:eq:mode`, where `𝔓` is the orthogonal Leray projection
of `L²(ℝ³; ℝ³)`).

The proof is the self-adjointness of `𝔓` on `L²`: for `c ∈ L²` and a representative `pc` of
`𝔓c`,
`∫⟨c, 𝔓∂ⱼφ⟩ = ⟨𝔓c, ∂ⱼφ⟩_{L²} = ∫⟨pc, ∂ⱼφ⟩`.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-- **Sub-lemma I09/2** (self-adjointness of the Leray projection `𝔓`): the fiber identity
`LerayFiberIdentity` holds, with no extra hypothesis. -/
theorem lerayFiberIdentity : LerayFiberIdentity := by
  intro c pc φ j hc hφ hpc
  have hB : MemLp (testPartial φ j) 2 volume :=
    UnforcedLeray.Blueprint.L13.testPartial_memLp hφ j
  calc (∫ y, inner ℝ (c y) (projectedPartial φ j y))
      = inner ℝ (toL2 c) (Leray.projection (toL2 (testPartial φ j))) := by
        rw [MeasureTheory.L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_toL2 hc] with y hy
        simp only [projectedPartial, hy]
    _ = inner ℝ (Leray.projection (toL2 c)) (toL2 (testPartial φ j)) :=
        (Leray.projection_selfadjoint (toL2 c) (toL2 (testPartial φ j))).symm
    _ = ∫ y, inner ℝ (pc y) (testPartial φ j y) := by
        rw [MeasureTheory.L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [hpc, coeFn_toL2 hB] with y h1 h2
        rw [h1, h2]

end UnforcedLeray.Short.Interface
