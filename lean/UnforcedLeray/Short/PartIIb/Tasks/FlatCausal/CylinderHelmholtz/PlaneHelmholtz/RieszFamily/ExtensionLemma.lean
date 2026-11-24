import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs

/-!
# Extension of a norm-bounded map from a dense subspace of `L²`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula);
Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

A linear map `L` on a dense submodule `M` of `PlaneL2` with `‖L g‖ ≤ ‖g‖` is bounded by `1`,
so it extends by density to a continuous linear map `T` on `PlaneL2` with `‖T‖ ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- Abstract extension lemma (`ExtensionLemma`). -/
theorem extensionLemma : ExtensionLemma := by
  intro M hM L hL
  obtain ⟨f, hf⟩ : ∃ f : M →L[ℝ] PlaneL2, ∀ g, f g = L g :=
    ⟨LinearMap.mkContinuous L 1 (fun g => by rw [one_mul]; exact hL g), fun g => rfl⟩
  have hnorm : ‖f‖ ≤ 1 :=
    f.opNorm_le_bound zero_le_one (fun g => by rw [hf, one_mul]; exact hL g)
  have hd : DenseRange (M.subtypeL) := by
    have hr : Set.range (M.subtypeL : M → PlaneL2) = (M : Set PlaneL2) := by
      ext x
      simp
    show Dense (Set.range (M.subtypeL : M → PlaneL2))
    rw [hr]
    exact hM
  have hi : IsUniformInducing (M.subtypeL : M → PlaneL2) :=
    (M.subtypeₗᵢ).isometry.isUniformInducing
  refine ⟨f.extend M.subtypeL, ?_, ?_⟩
  · calc ‖f.extend M.subtypeL‖ ≤ ((1 : NNReal) : ℝ) * ‖f‖ :=
          ContinuousLinearMap.opNorm_extend_le f hd (fun x => by simp)
      _ ≤ 1 := by simpa using hnorm
  · intro g
    have h := ContinuousLinearMap.extend_eq f hd hi g
    simp only [Submodule.subtypeL_apply, hf] at h
    exact h

end UnforcedLeray.Short.IIb.PlaneRiesz
