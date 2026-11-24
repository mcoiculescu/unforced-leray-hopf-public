import UnforcedLeray.Analysis.LerayProjection.TranslationGenerator
import UnforcedLeray.Analysis.SobolevGraph.H2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith

/-!
# Integration by parts for actual L² weak derivatives

The infinitesimal generator of the genuine isometric translation group is
already identified with the concrete weak derivative graph. Differentiating
the invariant L² inner product therefore proves integration by parts, without
an additional density or integration identity assumption. The H² Laplacian
is the sum of the three actual diagonal weak second derivatives.
-/
noncomputable section
open MeasureTheory
namespace UnforcedLeray.SobolevGraph

/-- Integration by parts for two actual square-integrable weak derivative pairs. -/
theorem weakDerivative_inner (F F' G G' : L2Space) (i : Fin 3)
    (hF : HasWeakSpatialDerivative i (F : SpatialField) (F' : SpatialField))
    (hG : HasWeakSpatialDerivative i (G : SpatialField) (G' : SpatialField)) :
    inner ℝ F' G = -inner ℝ F G' := by
  have hF0 := (Leray.weakDerivative_iff_hasDerivAt_translation F F' i).mp hF
  have hG0 := (Leray.weakDerivative_iff_hasDerivAt_translation G G' i).mp hG
  have hi := hF0.inner ℝ hG0
  simp only [zero_smul, Leray.translation_zero, Leray.inner_translation] at hi
  have hz := hi.unique (hasDerivAt_const 0 (inner ℝ F G))
  linarith

namespace H2

/-- The actual L² Laplacian on the weak H² graph, as a bounded graph-to-L² map. -/
def laplaceCLM : H2 →L[ℝ] L2Space := ∑ i : Fin 3, secondCLM i i

/-- The sum of the three actual diagonal second weak derivatives. -/
def laplace (F : H2) : L2Space := laplaceCLM F

@[simp] theorem laplace_eq (F : H2) : laplace F = ∑ i : Fin 3, F.second i i := by
  simp [laplace, laplaceCLM]

/-- The bilinear weak H² energy identity with all first derivatives accounted for. -/
theorem laplace_inner (F G : H2) :
    inner ℝ (laplace F) G.value =
      -(∑ i : Fin 3, inner ℝ (F.first i) (G.first i)) := by
  rw [laplace_eq, sum_inner, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact weakDerivative_inner (F.first i) (F.second i i) G.value (G.first i) i
    (F.hasWeakSecond i i) (G.hasWeakFirst i)

/-- The actual Laplacian dissipates precisely the sum of squared L² first derivatives. -/
theorem laplace_inner_self (F : H2) :
    inner ℝ (laplace F) F.value = -(∑ i : Fin 3, ‖F.first i‖ ^ 2) := by
  rw [laplace_inner]
  simp only [real_inner_self_eq_norm_sq]

/-- The weak H² Laplacian is symmetric on its actual L² values. -/
theorem laplace_inner_symmetric (F G : H2) :
    inner ℝ (laplace F) G.value = inner ℝ F.value (laplace G) := by
  calc
    inner ℝ (laplace F) G.value = -(∑ i : Fin 3, inner ℝ (F.first i) (G.first i)) :=
      laplace_inner F G
    _ = -(∑ i : Fin 3, inner ℝ (G.first i) (F.first i)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact real_inner_comm _ _
    _ = inner ℝ (laplace G) F.value := (laplace_inner G F).symm
    _ = inner ℝ F.value (laplace G) := real_inner_comm _ _

theorem laplace_inner_self_nonpos (F : H2) : inner ℝ (laplace F) F.value ≤ 0 := by
  rw [laplace_inner_self]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end H2
end UnforcedLeray.SobolevGraph
