/-
Adapted from OpenAI's NavierStokesAndEuler Euler/LpTranslation.lean,
commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd, Apache-2.0.
Changes: only elementary translation lemmas extracted; x-a convention;
namespace and imports use this project's concrete R³ L² space.
-/
import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Genuine, strongly continuous, isometric translations in L²(R³;R³). -/
noncomputable section
open MeasureTheory
namespace UnforcedLeray.Heat

def translation (a : Space) : L2Space →ₗᵢ[ℝ] L2Space :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : Space => x-a)
    (measurePreserving_sub_right volume a)

theorem translation_ae (a : Space) (u : L2Space) :
    translation a u =ᵐ[volume] fun x => u (x-a) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_sub_right volume a)

@[simp] theorem translation_zero (u : L2Space) : translation 0 u = u := by
  apply Lp.ext
  filter_upwards [translation_ae 0 u] with x hx
  simpa only [sub_zero] using hx

theorem translation_add (a b : Space) (u : L2Space) :
    translation a (translation b u) = translation (a+b) u := by
  apply Lp.ext
  filter_upwards [translation_ae a (translation b u),
    (measurePreserving_sub_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (translation_ae b u), translation_ae (a+b) u] with x ha hb hab
  rw [ha, hb, hab, sub_sub]

theorem translation_continuous (u : L2Space) : Continuous (fun a : Space => translation a u) := by
  let g : Space → C(Space, Space) := fun a => ⟨fun x => x-a, continuous_id.sub continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun a => measurePreserving_sub_right (volume : Measure Space) a) (by norm_num)

@[simp] theorem norm_translation (a : Space) (u : L2Space) : ‖translation a u‖ = ‖u‖ :=
  (translation a).norm_map u

end UnforcedLeray.Heat
