import UnforcedLeray.Analysis.LerayProjection.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Measure

/-!
# Actual translations of vector-valued L²(R³)

Composition with `x ↦ x + a` is a linear isometry because Lebesgue measure is
translation invariant. These operators form a strongly continuous group. The
representative identity is almost everywhere, as required for L² classes.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Leray

/-- Spatial translation `F(x) ↦ F(x+a)` on the actual L² quotient. -/
def translation (a : Space) : L2Space →ₗᵢ[ℝ] L2Space :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : Space => x + a)
    (measurePreserving_add_right volume a)

/-- A translated L² class is represented by the actual translated field. -/
theorem coeFn_translation (a : Space) (F : L2Space) :
    (translation a F : SpatialField) =ᵐ[volume] fun x => F (x + a) :=
  Lp.coeFn_compMeasurePreserving F (measurePreserving_add_right volume a)

@[simp] theorem norm_translation (a : Space) (F : L2Space) : ‖translation a F‖ = ‖F‖ :=
  (translation a).norm_map F

@[simp] theorem translation_zero (F : L2Space) : translation 0 F = F := by
  apply Lp.ext
  simpa only [add_zero] using coeFn_translation 0 F

/-- Composition agrees with addition of spatial shifts. -/
theorem translation_add (a b : Space) (F : L2Space) :
    translation a (translation b F) = translation (a + b) F := by
  change Lp.compMeasurePreserving (fun x : Space => x + a) _
    (Lp.compMeasurePreserving (fun x : Space => x + b) _ F) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : (fun x : Space => x + b) ∘ (fun x : Space => x + a) =
      (fun x : Space => x + (a + b)) := by
    funext x
    simp only [Function.comp_apply, add_assoc]
  simp only [he]
  rfl

@[simp] theorem translation_neg_cancel (a : Space) (F : L2Space) :
    translation (-a) (translation a F) = F := by
  rw [translation_add, neg_add_cancel, translation_zero]

@[simp] theorem translation_cancel_neg (a : Space) (F : L2Space) :
    translation a (translation (-a) F) = F := by
  rw [translation_add, add_neg_cancel, translation_zero]

/-- Translation is a surjective linear isometry, with inverse translation by `-a`. -/
def translationEquiv (a : Space) : L2Space ≃ₗᵢ[ℝ] L2Space where
  toLinearEquiv :=
    { (translation a).toLinearMap with
      invFun := translation (-a)
      left_inv := translation_neg_cancel a
      right_inv := translation_cancel_neg a }
  norm_map' := norm_translation a

@[simp] theorem translationEquiv_apply (a : Space) (F : L2Space) :
    translationEquiv a F = translation a F := rfl

@[simp] theorem translationEquiv_symm_apply (a : Space) (F : L2Space) :
    (translationEquiv a).symm F = translation (-a) F := rfl

theorem inner_translation (a : Space) (F G : L2Space) :
    inner ℝ (translation a F) (translation a G) = inner ℝ F G :=
  (translation a).inner_map_map F G

/-- Moving translation between the slots reverses its shift. -/
theorem inner_translation_left (a : Space) (F G : L2Space) :
    inner ℝ (translation a F) G = inner ℝ F (translation (-a) G) := by
  conv_lhs => rw [← translation_cancel_neg a G]
  exact inner_translation a F (translation (-a) G)

/-- Joint continuity of the spatial shift and the L² input. -/
theorem continuous_translation : Continuous (fun p : Space × L2Space => translation p.1 p.2) := by
  let shift : Space × L2Space → C(Space, Space) := fun p =>
    ⟨fun x => x + p.1, continuous_id.add continuous_const⟩
  have hs : Continuous shift := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_snd.add (continuous_fst.fst)
  exact continuous_snd.compMeasurePreservingLp hs
    (fun p => measurePreserving_add_right volume p.1) (by norm_num)

/-- In particular translations are strongly continuous at the identity. -/
theorem continuous_translation_orbit (F : L2Space) :
    Continuous (fun a : Space => translation a F) :=
  continuous_translation.comp (continuous_id.prodMk continuous_const)

/-- The L² norm of a translated difference tends to zero as the shift tends to zero. -/
theorem translation_tendsto_zero (F : L2Space) :
    Tendsto (fun a : Space => translation a F) (𝓝 0) (𝓝 F) := by
  simpa only [translation_zero] using (continuous_translation_orbit F).tendsto (0 : Space)

end UnforcedLeray.Leray
