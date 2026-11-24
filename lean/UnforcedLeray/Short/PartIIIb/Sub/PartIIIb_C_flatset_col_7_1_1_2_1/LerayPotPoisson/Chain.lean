import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs

/-!
# Chain rule helpers for `LerayPotPoisson`

Derivatives of `y ↦ g (p + (0, -y))` (the reflected translate used in the fundamental
solution identity) and the component derivative `ppDv`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The affine map `y ↦ p + (0, -y)` on the `(q, η)` plane. -/
lemma pp_hasFDerivAt_shift (p : Chart) (y : ℝ × ℝ) :
    HasFDerivAt (fun y' : ℝ × ℝ => p + ((0 : ℝ), -y'))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (-ContinuousLinearMap.id ℝ (ℝ × ℝ))) y := by
  have h1 : HasFDerivAt (fun y' : ℝ × ℝ => -y') (-ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
    (hasFDerivAt_id y).neg
  have h2 : HasFDerivAt (fun y' : ℝ × ℝ => ((0 : ℝ), -y'))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (-ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
    (hasFDerivAt_const (0 : ℝ) y).prodMk h1
  exact h2.const_add p

lemma pp_chain1 (g : Chart → ℝ) (hg : ContDiff ℝ ∞ g) (p : Chart) (y v : ℝ × ℝ) :
    fderiv ℝ (fun y' => g (p + ((0 : ℝ), -y'))) y v =
      -fderiv ℝ g (p + ((0 : ℝ), -y)) ((0 : ℝ), v) := by
  have hgd : HasFDerivAt g (fderiv ℝ g (p + ((0 : ℝ), -y))) (p + ((0 : ℝ), -y)) :=
    ((hg.differentiable (by simp)) _).hasFDerivAt
  have hc := hgd.comp y (pp_hasFDerivAt_shift p y)
  rw [show (fun y' => g (p + ((0 : ℝ), -y'))) = g ∘ (fun y' => p + ((0 : ℝ), -y')) from rfl,
    hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
  rw [show ((0 : ℝ), -v) = -((0 : ℝ), v) by simp, map_neg]

lemma pp_chain2 (g : Chart → ℝ) (hg : ContDiff ℝ ∞ g) (p w : Chart) (y v : ℝ × ℝ) :
    fderiv ℝ (fun y' => fderiv ℝ g (p + ((0 : ℝ), -y')) w) y v =
      -fderiv ℝ (fun z => fderiv ℝ g z w) (p + ((0 : ℝ), -y)) ((0 : ℝ), v) := by
  have hD : ContDiff ℝ ∞ (fun z => fderiv ℝ g z w) :=
    (hg.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hDd : HasFDerivAt (fun z => fderiv ℝ g z w)
      (fderiv ℝ (fun z => fderiv ℝ g z w) (p + ((0 : ℝ), -y))) (p + ((0 : ℝ), -y)) :=
    ((hD.differentiable (by simp)) _).hasFDerivAt
  have hc := hDd.comp y (pp_hasFDerivAt_shift p y)
  rw [show (fun y' => fderiv ℝ g (p + ((0 : ℝ), -y')) w) =
      (fun z => fderiv ℝ g z w) ∘ (fun y' => p + ((0 : ℝ), -y')) from rfl, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
  rw [show ((0 : ℝ), -v) = -((0 : ℝ), v) by simp, map_neg]

/-- The `v`-derivative of each component of a field. -/
def ppDv (F : Chart → Fin 2 → ℝ) (v : Chart) : Chart → Fin 2 → ℝ :=
  fun p i => fderiv ℝ (fun p' => F p' i) p v

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
