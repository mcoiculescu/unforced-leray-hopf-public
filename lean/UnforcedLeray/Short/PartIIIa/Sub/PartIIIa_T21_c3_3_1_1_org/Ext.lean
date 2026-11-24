import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Extension of a bounded linear map from a subspace of a Hilbert space (generic helper)

A bounded `ℂ`-linear map on a submodule `D` of a complete inner product space extends to a bounded
linear map on the whole space with the same bound (extension to the closure, then composition with
the orthogonal projection onto the closure).  Used for leaf (a) of `PartIII-a:T21/c3/3/1/1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.Ext

theorem exists_extend_of_bound {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (D : Submodule ℂ E) (Φ : D →ₗ[ℂ] F) (C : ℝ) (hC : 0 ≤ C) (h : ∀ x : D, ‖Φ x‖ ≤ C * ‖x‖) :
    ∃ T : E →L[ℂ] F, (∀ x : D, T x = Φ x) ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖ := by
  classical
  let Φc : D →L[ℂ] F := Φ.mkContinuous C h
  let K := D.topologicalClosure
  haveI : CompleteSpace K := (D.isClosed_topologicalClosure : IsClosed (D.topologicalClosure : Set E)).completeSpace_coe
  haveI : K.HasOrthogonalProjection := inferInstance
  let e : D →L[ℂ] K := (Submodule.inclusion D.le_topologicalClosure).mkContinuous 1 (by
    intro x; simp)
  have he : ∀ x : D, ((e x : K) : E) = (x : E) := fun x => rfl
  have hdense : DenseRange e := by
    unfold DenseRange
    rw [dense_iff_closure_eq, Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    have himg : Subtype.val '' Set.range e = (D : Set E) := by
      ext y; constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact x.2
      · intro hy; exact ⟨e ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    erw [himg]
    ext k
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact k.2
  have hind : IsUniformInducing e := by
    refine (ContinuousLinearMap.isUniformEmbedding_of_bound (K := 1) e ?_).isUniformInducing
    intro x; simp [he]
  let T0 : K →L[ℂ] F := Φc.extend e
  refine ⟨T0.comp K.orthogonalProjectionOnto, ?_, ?_⟩
  · intro x
    have h1 : K.orthogonalProjectionOnto (x : E) = e x := by
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := K) (e x)
    simp only [ContinuousLinearMap.comp_apply, h1]
    rw [ContinuousLinearMap.extend_eq Φc hdense hind]
    rfl
  · have hbd : ‖T0‖ ≤ C := by
      have := ContinuousLinearMap.opNorm_extend_le (N := 1) Φc hdense (e := e) (by intro x; simp [he])
      have h2 : ‖Φc‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _
      simpa using this.trans (by simpa using h2)
    intro x
    calc ‖T0 (K.orthogonalProjectionOnto x)‖ ≤ ‖T0‖ * ‖K.orthogonalProjectionOnto x‖ :=
          T0.le_opNorm _
      _ ≤ C * ‖x‖ := by
          gcongr
          exact Submodule.norm_orthogonalProjectionOnto_apply_le K x

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.Ext
