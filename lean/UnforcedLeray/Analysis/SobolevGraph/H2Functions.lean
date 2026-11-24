import UnforcedLeray.Analysis.SobolevGraph.H2
import UnforcedLeray.Analysis.SobolevGraph.MixedPartials

/-!
# Actual functions and the second-order Sobolev graph

Concrete R³ vector fields with L² first and ordered-second weak derivatives
determine elements of the complete H² graph. The graph has precisely that
function-level membership condition. Its mixed second derivatives agree as
L² classes, by commutation of smooth test derivatives.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.SobolevGraph

/-- Actual L² fields and their actual weak derivatives determine an H² element. -/
def H2.ofFields (f : SpatialField) (g : Fin 3 → SpatialField)
    (q : Fin 3 → Fin 3 → SpatialField)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hq : ∀ i j, MemLp (q i j) 2 volume)
    (hfirst : ∀ i, HasWeakSpatialDerivative i f (g i))
    (hsecond : ∀ i j, HasWeakSpatialDerivative j (g i) (q i j)) : H2 :=
  H2.ofWeakDerivatives (toL2 f) (fun i => toL2 (g i)) (fun i j => toL2 (q i j))
    (fun i => (hfirst i).congr (coeFn_toL2 hf).symm (coeFn_toL2 (hg i)).symm)
    (fun i j => (hsecond i j).congr (coeFn_toL2 (hg i)).symm (coeFn_toL2 (hq i j)).symm)

@[simp] theorem H2.value_ofFields (f : SpatialField) (g : Fin 3 → SpatialField)
    (q : Fin 3 → Fin 3 → SpatialField)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hq : ∀ i j, MemLp (q i j) 2 volume)
    (hfirst : ∀ i, HasWeakSpatialDerivative i f (g i))
    (hsecond : ∀ i j, HasWeakSpatialDerivative j (g i) (q i j)) :
    (H2.ofFields f g q hf hg hq hfirst hsecond).value = toL2 f := rfl

@[simp] theorem H2.first_ofFields (f : SpatialField) (g : Fin 3 → SpatialField)
    (q : Fin 3 → Fin 3 → SpatialField)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hq : ∀ i j, MemLp (q i j) 2 volume)
    (hfirst : ∀ i, HasWeakSpatialDerivative i f (g i))
    (hsecond : ∀ i j, HasWeakSpatialDerivative j (g i) (q i j)) (i : Fin 3) :
    (H2.ofFields f g q hf hg hq hfirst hsecond).first i = toL2 (g i) := rfl

@[simp] theorem H2.second_ofFields (f : SpatialField) (g : Fin 3 → SpatialField)
    (q : Fin 3 → Fin 3 → SpatialField)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hq : ∀ i j, MemLp (q i j) 2 volume)
    (hfirst : ∀ i, HasWeakSpatialDerivative i f (g i))
    (hsecond : ∀ i j, HasWeakSpatialDerivative j (g i) (q i j)) (i j : Fin 3) :
    (H2.ofFields f g q hf hg hq hfirst hsecond).second i j = toL2 (q i j) := rfl

/-- Exact norm identity, using the same ordered second derivatives as Statement.lean. -/
theorem H2.norm_sq_ofFields (f : SpatialField) (g : Fin 3 → SpatialField)
    (q : Fin 3 → Fin 3 → SpatialField)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hq : ∀ i j, MemLp (q i j) 2 volume)
    (hfirst : ∀ i, HasWeakSpatialDerivative i f (g i))
    (hsecond : ∀ i j, HasWeakSpatialDerivative j (g i) (q i j)) :
    ‖H2.ofFields f g q hf hg hq hfirst hsecond‖ ^ 2 =
      l2Norm f ^ 2 + (∑ i : Fin 3, l2Norm (g i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, l2Norm (q i j) ^ 2 := by
  rw [H2.norm_sq, H2.value_ofFields, norm_toL2 hf]
  simp_rw [H2.first_ofFields, H2.second_ofFields, norm_toL2 (hg _), norm_toL2 (hq _ _)]

/-- The complete Hilbert graph has exactly the concrete weak H² membership
condition on R³ vector fields. No differentiability of representatives is assumed. -/
theorem exists_H2_iff (f : SpatialField) :
    (∃ F : H2, (F.value : SpatialField) =ᵐ[volume] f) ↔
      MemLp f 2 volume ∧ ∃ (g : Fin 3 → SpatialField) (q : Fin 3 → Fin 3 → SpatialField),
        (∀ i, MemLp (g i) 2 volume) ∧ (∀ i j, MemLp (q i j) 2 volume) ∧
        (∀ i, HasWeakSpatialDerivative i f (g i)) ∧
        (∀ i j, HasWeakSpatialDerivative j (g i) (q i j)) := by
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨(memLp_congr_ae hF).mp (Lp.memLp F.value),
      (fun i => (F.first i : SpatialField)), (fun i j => (F.second i j : SpatialField)),
      (fun i => Lp.memLp (F.first i)), (fun i j => Lp.memLp (F.second i j)), ?_, ?_⟩
    · intro i
      exact (F.hasWeakFirst i).congr hF Filter.EventuallyEq.rfl
    · intro i j
      exact F.hasWeakSecond i j
  · rintro ⟨hf, g, q, hg, hq, hfirst, hsecond⟩
    refine ⟨H2.ofFields f g q hf hg hq hfirst hsecond, ?_⟩
    exact coeFn_toL2 hf

/-- The ordered second derivatives are symmetric as actual L² equivalence classes. -/
theorem H2.second_symmetric (F : H2) (i j : Fin 3) : F.second i j = F.second j i := by
  apply Lp.ext
  exact weak_second_symmetry (F.hasWeakFirst i) (F.hasWeakFirst j)
    (F.hasWeakSecond i j) (F.hasWeakSecond j i)
    (Lp.memLp (F.second i j)) (Lp.memLp (F.second j i))

end UnforcedLeray.SobolevGraph
