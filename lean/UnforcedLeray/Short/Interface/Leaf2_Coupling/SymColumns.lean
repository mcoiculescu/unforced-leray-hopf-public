import UnforcedLeray.Short.Interface.Sub.I09

/-!
# Interface:I09/1, the columns of the coupling stress are in `𝒴₂`

Sub-lemma `SymColumnsIsY2` (defined in `Short/Interface/Sub/I09.lean`). Source of record:
`the November 2 reference manuscript`, lines 167-180 (`b_* ∈ 𝒴_{2,div}`,
`U_*` bounded, and the mode equation `loc:eq:mode` with `div(U_* ⊗ b_* + b_* ⊗ U_*)`).

For a bounded jointly measurable background `V` and `b ∈ 𝒴₂`, each column `j` of
`V ⊗ b + b ⊗ V` is periodic, jointly measurable and square integrable on the period slab.
The proof reuses `symTensorColumns_eq` (the column as the bilinear map `symCol j`) and
`memLp_bilin_bdd` (an `L²` bound for a bilinear map applied to a bounded factor and an `L²`
factor).
-/

set_option autoImplicit false

open Set MeasureTheory Filter

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

theorem symColumnsIsY2 : SymColumnsIsY2 := by
  unfold SymColumnsIsY2
  intro P V dV b hP hV hb j
  obtain ⟨C, hC⟩ := hV.bounded
  have e : (fun z : SpaceTime => symTensorColumns (V z.1) (b z.1) j z.2)
      = fun z : SpaceTime => symCol j (V z.1 z.2) (b z.1 z.2) := by
    funext z
    simp only [symTensorColumns_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro τ
    show symTensorColumns (V (τ + P)) (b (τ + P)) j = symTensorColumns (V τ) (b τ) j
    rw [hV.periodic τ, hb.periodic τ]
  · show AEStronglyMeasurable (fun z : SpaceTime => symTensorColumns (V z.1) (b z.1) j z.2) volume
    rw [e]
    exact (symCol j).aestronglyMeasurable_comp₂ hV.measurable hb.measurable
  · show MemLp (fun z : SpaceTime => symTensorColumns (V z.1) (b z.1) j z.2) 2
      (volume.restrict (UnforcedLeray.Blueprint.periodSlab P))
    rw [e]
    exact memLp_bilin_bdd (symCol j) (a := fun z : SpaceTime => V z.1 z.2)
      (μ := volume.restrict (UnforcedLeray.Blueprint.periodSlab P))
      hV.measurable.restrict (fun z => hC z.1 z.2) hb.memL2

end UnforcedLeray.Short.Interface
