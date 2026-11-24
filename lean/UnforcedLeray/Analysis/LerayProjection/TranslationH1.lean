import UnforcedLeray.Analysis.LerayProjection.TranslationWeakDerivative
import UnforcedLeray.Analysis.LerayProjection.TranslationL2
import UnforcedLeray.Analysis.SobolevGraph.H1

/-!
# Spatial translation on the genuine first-order Sobolev graph

All four L² components of an H¹ element translate together. The translated
components still satisfy the original weak derivative relation, so they define
an actual H¹ element. These translations preserve the Sobolev norm and form a
strongly continuous group of real linear isometries.

No boundedness or derivative-commutation claim about the Leray projection is
made here; this module concerns spatial translation itself.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology
open UnforcedLeray.SobolevGraph

namespace UnforcedLeray.Leray

/-- Translate the actual field and each of its L² weak coordinate derivatives. -/
def h1Translate (a : Space) (F : H1) : H1 :=
  H1.ofWeakDerivatives (translation a F.value)
    (fun i => translation a (F.derivative i))
    (fun i => (weakDerivative_fieldTranslate a (F.hasWeakDerivative i)).congr
      (coeFn_translation a F.value).symm (coeFn_translation a (F.derivative i)).symm)

@[simp] theorem value_h1Translate (a : Space) (F : H1) :
    (h1Translate a F).value = translation a F.value := rfl

@[simp] theorem derivative_h1Translate (a : Space) (F : H1) (i : Fin 3) :
    (h1Translate a F).derivative i = translation a (F.derivative i) := rfl

/-- Preservation of the genuine square-sum H¹ graph norm. -/
@[simp] theorem norm_h1Translate (a : Space) (F : H1) : ‖h1Translate a F‖ = ‖F‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [H1.norm_sq, value_h1Translate, derivative_h1Translate, norm_translation]

/-- Translation as a real linear isometry of the actual H¹ Hilbert graph. -/
def h1Translation (a : Space) : H1 →ₗᵢ[ℝ] H1 where
  toFun := h1Translate a
  map_add' F G := by
    apply H1.ext
    change translation a (H1.valueCLM (F + G)) =
      H1.valueCLM (h1Translate a F + h1Translate a G)
    simp only [map_add, H1.valueCLM_apply, value_h1Translate]
  map_smul' c F := by
    apply H1.ext
    change translation a (H1.valueCLM (c • F)) = H1.valueCLM (c • h1Translate a F)
    simp only [map_smul, H1.valueCLM_apply, value_h1Translate]
  norm_map' := norm_h1Translate a

@[simp] theorem h1Translation_apply (a : Space) (F : H1) :
    h1Translation a F = h1Translate a F := rfl

@[simp] theorem value_h1Translation (a : Space) (F : H1) :
    (h1Translation a F).value = translation a F.value := rfl

@[simp] theorem derivative_h1Translation (a : Space) (F : H1) (i : Fin 3) :
    (h1Translation a F).derivative i = translation a (F.derivative i) := rfl

@[simp] theorem norm_h1Translation (a : Space) (F : H1) :
    ‖h1Translation a F‖ = ‖F‖ := (h1Translation a).norm_map F

@[simp] theorem h1Translation_zero (F : H1) : h1Translation 0 F = F := by
  apply H1.ext
  simp only [value_h1Translation, translation_zero]

theorem h1Translation_add (a b : Space) (F : H1) :
    h1Translation a (h1Translation b F) = h1Translation (a + b) F := by
  apply H1.ext
  simp only [value_h1Translation, translation_add]

@[simp] theorem h1Translation_neg_cancel (a : Space) (F : H1) :
    h1Translation (-a) (h1Translation a F) = F := by
  rw [h1Translation_add, neg_add_cancel, h1Translation_zero]

@[simp] theorem h1Translation_cancel_neg (a : Space) (F : H1) :
    h1Translation a (h1Translation (-a) F) = F := by
  rw [h1Translation_add, add_neg_cancel, h1Translation_zero]

/-- The inverse Sobolev translation is the translation by the opposite vector. -/
def h1TranslationEquiv (a : Space) : H1 ≃ₗᵢ[ℝ] H1 where
  toLinearEquiv :=
    { (h1Translation a).toLinearMap with
      invFun := h1Translation (-a)
      left_inv := h1Translation_neg_cancel a
      right_inv := h1Translation_cancel_neg a }
  norm_map' := norm_h1Translation a

@[simp] theorem h1TranslationEquiv_apply (a : Space) (F : H1) :
    h1TranslationEquiv a F = h1Translation a F := rfl

@[simp] theorem h1TranslationEquiv_symm_apply (a : Space) (F : H1) :
    (h1TranslationEquiv a).symm F = h1Translation (-a) F := rfl

/-- Joint continuity follows from the actual L² field and derivative components. -/
theorem continuous_h1Translation :
    Continuous (fun p : Space × H1 => h1Translation p.1 p.2) := by
  apply continuousOn_univ.mp
  apply (H1.continuousOn_iff_components _ Set.univ).mpr
  constructor
  · simpa only [Function.comp_def, id_eq, H1.valueCLM_apply, value_h1Translation] using
      (continuous_translation.comp
        (continuous_fst.prodMk (H1.valueCLM.continuous.comp continuous_snd))).continuousOn
  · intro i
    simpa only [Function.comp_def, id_eq, H1.derivativeCLM_apply, derivative_h1Translation] using
      (continuous_translation.comp
        (continuous_fst.prodMk
          ((H1.derivativeCLM i).continuous.comp continuous_snd))).continuousOn

/-- Spatial translations are strongly continuous in the genuine H¹ norm. -/
theorem continuous_h1Translation_orbit (F : H1) :
    Continuous (fun a : Space => h1Translation a F) := by
  simpa only [Function.comp_def, id_eq] using
    continuous_h1Translation.comp (continuous_id.prodMk continuous_const)

/-- Translation by a vanishing spatial shift converges in the H¹ graph norm. -/
theorem h1Translation_tendsto_zero (F : H1) :
    Tendsto (fun a : Space => h1Translation a F) (𝓝 0) (𝓝 F) := by
  simpa only [h1Translation_zero] using
    (continuous_h1Translation_orbit F).tendsto (0 : Space)

end UnforcedLeray.Leray
