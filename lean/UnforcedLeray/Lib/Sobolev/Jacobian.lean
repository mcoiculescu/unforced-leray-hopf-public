import UnforcedLeray.Lib.Sobolev.SmoothCoeff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Module.Determinant

/-!
# Smooth diffeomorphisms of `ℝⁿ`: Jacobian and change of variables (helpers for S6)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S6: `W.compDiffeo` for `Φ : Eucl n ≃ₜ Eucl n`
smooth with smooth inverse). Manuscript uses: composition with the area-preserving flow
(tex 1228–1237, B0062), dilations (tex 1569–1580, B0102; tex 2370–2377, B0156), linear
changes of variables (tex 14162–14178, B0912).

For a homeomorphism `Φ` of `ℝⁿ` with `Φ` and `Φ⁻¹` smooth:
* `fderiv_symm_comp`, `fderiv_comp_symm`: `DΦ⁻¹(Φ y) ∘ DΦ(y) = id`, `DΦ(Φ⁻¹ x) ∘ DΦ⁻¹(x) = id`;
* `det_fderiv_ne_zero`, `contDiff_det_fderiv`, `jac Φ y = |det DΦ(y)|`, `contDiff_jac`;
* `integral_comp_diffeo`: `∫ g = ∫ jac Φ · (g ∘ Φ)`, `lintegral_comp_diffeo`;
* `locallyIntegrable_comp_symm`, `ae_comp_symm`: composition with `Φ⁻¹` preserves local
  integrability and null sets.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Sob

section Coordinates

variable {n : ℕ}

/-- Coordinates: `w = ∑ᵢ wᵢ eᵢ`. -/
theorem eucl_eq_sum (w : Eucl n) : w = ∑ i, w i • e i := by
  refine PiLp.ext fun k => ?_
  simp [e, Pi.single_apply, mul_ite]

theorem clm_apply_eq_sum {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : Eucl n →L[ℝ] G) (w : Eucl n) : L w = ∑ i, w i • L (e i) := by
  conv_lhs => rw [eucl_eq_sum w]
  simp only [map_sum, map_smul]

/-- The `i`-th coordinate of `ℝⁿ` is smooth. -/
theorem contDiff_coord (i : Fin n) : ContDiff ℝ ∞ (fun w : Eucl n => w i) := by
  have : (fun w : Eucl n => w i) = ⇑(EuclideanSpace.proj i : Eucl n →L[ℝ] ℝ) := by
    funext w; simp
  rw [this]
  exact ContinuousLinearMap.contDiff _

end Coordinates

section Diffeo

variable {n : ℕ} (Φ : Eucl n ≃ₜ Eucl n) (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm)

include hΦ hΨ in
theorem fderiv_symm_comp (y : Eucl n) :
    (fderiv ℝ Φ.symm (Φ y)).comp (fderiv ℝ Φ y) = ContinuousLinearMap.id ℝ (Eucl n) := by
  have hc := fderiv_comp y ((hΨ.differentiable (by simp)) (Φ y))
    ((hΦ.differentiable (by simp)) y)
  have hid : (Φ.symm ∘ Φ : Eucl n → Eucl n) = id := funext Φ.symm_apply_apply
  rw [hid, fderiv_id] at hc
  exact hc.symm

include hΦ hΨ in
theorem fderiv_comp_symm (x : Eucl n) :
    (fderiv ℝ Φ (Φ.symm x)).comp (fderiv ℝ Φ.symm x) = ContinuousLinearMap.id ℝ (Eucl n) := by
  have hc := fderiv_comp x ((hΦ.differentiable (by simp)) (Φ.symm x))
    ((hΨ.differentiable (by simp)) x)
  have hid : (Φ ∘ Φ.symm : Eucl n → Eucl n) = id := funext Φ.apply_symm_apply
  rw [hid, fderiv_id] at hc
  exact hc.symm

include hΦ hΨ in
theorem det_fderiv_ne_zero (y : Eucl n) : (fderiv ℝ Φ y).det ≠ 0 := by
  have h := congrArg (fun A : Eucl n →L[ℝ] Eucl n => A.det) (fderiv_symm_comp Φ hΦ hΨ y)
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    ContinuousLinearMap.coe_id, LinearMap.det_id] at h
  exact right_ne_zero_of_mul_eq_one h

/-- The determinant of the derivative of a smooth map is smooth. -/
theorem contDiff_det_fderiv {f : Eucl n → Eucl n} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y => (fderiv ℝ f y).det) := by
  have key : ∀ y, (fderiv ℝ f y).det =
      Matrix.det (Matrix.of fun i j : Fin n => fderiv ℝ f y (e j) i) := by
    intro y
    rw [ContinuousLinearMap.det,
      ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
    congr 1
  have hent : ∀ i j : Fin n, ContDiff ℝ ∞ (fun y => fderiv ℝ f y (e j) i) := fun i j =>
    (contDiff_coord i).comp ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  simp_rw [key, Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => hent _ _

/-- The Jacobian `|det DΦ(y)|`. -/
def jac (Φ : Eucl n → Eucl n) (y : Eucl n) : ℝ := |(fderiv ℝ Φ y).det|

theorem jac_nonneg (f : Eucl n → Eucl n) (y : Eucl n) : 0 ≤ jac f y := abs_nonneg _

include hΦ hΨ in
theorem contDiff_jac : ContDiff ℝ ∞ (jac Φ) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  exact ((contDiff_det_fderiv hΦ).contDiffAt).abs (det_fderiv_ne_zero Φ hΦ hΨ y)

include hΦ in
theorem hasFDerivWithinAt_diffeo (s : Set (Eucl n)) :
    ∀ y ∈ s, HasFDerivWithinAt Φ (fderiv ℝ Φ y) s y := fun y _ =>
  ((hΦ.differentiable (by simp)) y).hasFDerivAt.hasFDerivWithinAt

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

include hΦ in
/-- **Change of variables**: `∫ g = ∫ y, jac Φ y • g (Φ y)`. -/
theorem integral_comp_diffeo (g : Eucl n → F) :
    ∫ x, g x = ∫ y, jac Φ y • g (Φ y) := by
  have := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (hasFDerivWithinAt_diffeo Φ hΦ univ) Φ.injective.injOn g
  rwa [Set.image_univ_of_surjective Φ.surjective, Measure.restrict_univ] at this

include hΦ in
theorem integrable_comp_diffeo_iff (g : Eucl n → F) :
    Integrable g ↔ Integrable (fun y => jac Φ y • g (Φ y)) := by
  have := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume MeasurableSet.univ
    (hasFDerivWithinAt_diffeo Φ hΦ univ) Φ.injective.injOn g
  rwa [Set.image_univ_of_surjective Φ.surjective, integrableOn_univ, integrableOn_univ] at this

include hΦ in
theorem lintegral_comp_diffeo (g : Eucl n → ℝ≥0∞) :
    ∫⁻ x, g x = ∫⁻ y, ENNReal.ofReal (jac Φ y) * g (Φ y) := by
  have := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume MeasurableSet.univ
    (hasFDerivWithinAt_diffeo Φ hΦ univ) Φ.injective.injOn g
  rwa [Set.image_univ_of_surjective Φ.surjective, Measure.restrict_univ] at this

include hΦ hΨ in
/-- Composition with `Φ⁻¹` preserves local integrability. -/
theorem locallyIntegrable_comp_symm {u : Eucl n → F} (hu : LocallyIntegrable u volume) :
    LocallyIntegrable (fun x => u (Φ.symm x)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hs : IsCompact (Φ.symm '' K) := hK.image Φ.symm.continuous
  have hKs : K = Φ '' (Φ.symm '' K) := by
    rw [Set.image_image]; simp
  rw [hKs, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs.measurableSet
    (hasFDerivWithinAt_diffeo Φ hΦ _) Φ.injective.injOn]
  simp only [Homeomorph.symm_apply_apply]
  exact (hu.integrableOn_isCompact hs).continuousOn_smul
    (contDiff_jac Φ hΦ hΨ).continuous.continuousOn hs

include hΦ in
/-- Composition with `Φ⁻¹` preserves null sets. -/
theorem ae_comp_symm {P : Eucl n → Prop} (h : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ x ∂volume, P (Φ.symm x) := by
  rw [ae_iff] at h ⊢
  have hnull := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (hΦ.differentiable (by simp)).differentiableOn h
  refine measure_mono_null (fun x hx => ?_) hnull
  exact ⟨Φ.symm x, hx, Φ.apply_symm_apply x⟩

include hΦ in
theorem ae_eq_comp_symm {β : Type*} {f g : Eucl n → β} (h : f =ᵐ[volume] g) :
    (fun x => f (Φ.symm x)) =ᵐ[volume] fun x => g (Φ.symm x) :=
  ae_comp_symm Φ hΦ h

end Diffeo

end UnforcedLeray.Sob
