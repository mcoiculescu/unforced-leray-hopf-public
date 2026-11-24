import UnforcedLeray.Analysis.SobolevGraph.H1
import UnforcedLeray.Analysis.WeakDerivative

/-!
# Bridging actual weak derivatives to the Sobolev Hilbert graph

The graph construction is invariant under changes on null sets. In particular,
actual vector fields with L² weak derivatives determine elements of the
complete H¹ graph, with exactly the target statement's squared Sobolev norm.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.SobolevGraph

/-- Passing to L² equivalence classes preserves exactly the weak derivative
predicate appearing in the target theorem. -/
theorem mem_derivativeGraph_toL2_iff (i : Fin 3) {f g : SpatialField}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (toL2 f, toL2 g) ∈ derivativeGraph i ↔ HasWeakSpatialDerivative i f g := by
  rw [mem_derivativeGraph_iff]
  constructor
  · intro h
    exact h.congr (coeFn_toL2 hf) (coeFn_toL2 hg)
  · intro h
    exact h.congr (coeFn_toL2 hf).symm (coeFn_toL2 hg).symm

/-- The concrete field and its concrete L² weak derivatives determine an H¹ element. -/
def H1.ofFields (f : SpatialField) (g : Fin 3 → SpatialField)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) : H1 :=
  H1.ofWeakDerivatives (toL2 f) (fun i => toL2 (g i))
    (fun i => (hderiv i).congr (coeFn_toL2 hf).symm (coeFn_toL2 (hg i)).symm)

@[simp] theorem H1.value_ofFields (f : SpatialField) (g : Fin 3 → SpatialField)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) :
    (H1.ofFields f g hf hg hderiv).value = toL2 f := rfl

@[simp] theorem H1.derivative_ofFields (f : SpatialField) (g : Fin 3 → SpatialField)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) (i : Fin 3) :
    (H1.ofFields f g hf hg hderiv).derivative i = toL2 (g i) := rfl

/-- The Hilbert norm is exactly the L² norm plus the three squared derivative norms. -/
theorem H1.norm_sq_ofFields (f : SpatialField) (g : Fin 3 → SpatialField)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hderiv : ∀ i, HasWeakSpatialDerivative i f (g i)) :
    ‖H1.ofFields f g hf hg hderiv‖ ^ 2 = l2Norm f ^ 2 + ∑ i : Fin 3, l2Norm (g i) ^ 2 := by
  rw [H1.norm_sq, H1.value_ofFields, norm_toL2 hf]
  simp_rw [H1.derivative_ofFields, norm_toL2 (hg _)]

/-- This complete Hilbert space has precisely the usual first-order weak
Sobolev membership condition, in terms of actual L² functions on R³. -/
theorem exists_H1_iff (f : SpatialField) :
    (∃ F : H1, (F.value : SpatialField) =ᵐ[volume] f) ↔
      MemLp f 2 volume ∧ ∃ g : Fin 3 → SpatialField,
        (∀ i, MemLp (g i) 2 volume) ∧ (∀ i, HasWeakSpatialDerivative i f (g i)) := by
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨(memLp_congr_ae hF).mp (Lp.memLp F.value), fun i => (F.derivative i : SpatialField),
      fun i => Lp.memLp (F.derivative i), ?_⟩
    intro i
    exact (F.hasWeakDerivative i).congr hF Filter.EventuallyEq.rfl
  · rintro ⟨hf, g, hg, hderiv⟩
    refine ⟨H1.ofFields f g hf hg hderiv, ?_⟩
    exact coeFn_toL2 hf

end UnforcedLeray.SobolevGraph
