import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Extension of a bounded linear map from a dense subspace (`PartIII-b:C/near/masked/16`)

Pure functional analysis. `φ` is made into a continuous linear map `φ'` on `D`, which is then
extended along the dense uniform embedding `D.subtypeL` by `ContinuousLinearMap.extend`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem exists_clm_extend_of_dense {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (D : Submodule ℝ E) (hD : Dense (D : Set E)) (φ : D →ₗ[ℝ] F) (C : ℝ)
    (hφ : ∀ x : D, ‖φ x‖ ≤ C * ‖x‖) :
    ∃ L : E →L[ℝ] F, ∀ x : D, L x = φ x := by
  let φ' : D →L[ℝ] F := LinearMap.mkContinuous φ C hφ
  have hden : DenseRange (D.subtypeL) := by
    unfold DenseRange
    have hr : Set.range (⇑D.subtypeL) = (D : Set E) := by
      ext x
      simp
    rw [hr]
    exact hD
  have hind : IsUniformInducing (⇑D.subtypeL) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  refine ⟨φ'.extend D.subtypeL, fun x => ?_⟩
  have h := ContinuousLinearMap.extend_eq φ' hden hind x
  simpa [φ'] using h

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
