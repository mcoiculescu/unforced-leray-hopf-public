import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.ParamDmu

/-!
# Measurability of parametric derivatives

Generic: if `p ↦ f p x` is measurable for every `x` and every `f p` is differentiable at `y`, then
`p ↦ fderiv (f p) y` is measurable (difference quotients along a sequence).  Used for the
measurability hypotheses of `ParamDmuCausal` in `pdYRep` (source 3611-3621, 4171-4186).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma yr_meas_fderiv_apply {X E G : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (f : X → E → G) (y v : E)
    (hd : ∀ p, DifferentiableAt ℝ (f p) y) (hm : ∀ x, Measurable fun p => f p x) :
    Measurable fun p => fderiv ℝ (f p) y v := by
  have hq : ∀ n : ℕ, Measurable fun p : X => ((n : ℝ) + 1) • (f p (y + ((n : ℝ) + 1)⁻¹ • v) - f p y) :=
    fun n => ((hm _).sub (hm y)).const_smul _
  refine measurable_of_tendsto_metrizable hq ?_
  refine tendsto_pi_nhds.2 fun p => ?_
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) atTop atTop :=
    h1.congr (fun n => (Real.norm_of_nonneg (by positivity)).symm)
  exact (hd p).hasFDerivAt.lim (c := fun n : ℕ => (n : ℝ) + 1) v hc

lemma yr_clm_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (T : Space →L[ℝ] G) :
    T = ∑ i : Fin 3, (EuclideanSpace.proj i : Space →L[ℝ] ℝ).smulRight (T (coordinateVector i)) := by
  ext w : 1
  have hw : w = ∑ i : Fin 3, w i • coordinateVector i := by
    ext j
    simp [coordinateVector, Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum]

lemma yr_meas_fderiv {X G : Type*} [MeasurableSpace X] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (f : X → Space → G) (y : Space)
    (hd : ∀ p, DifferentiableAt ℝ (f p) y) (hm : ∀ x, Measurable fun p => f p x) :
    Measurable fun p => fderiv ℝ (f p) y := by
  have : (fun p => fderiv ℝ (f p) y) = fun p => ∑ i : Fin 3,
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).smulRight (fderiv ℝ (f p) y (coordinateVector i)) := by
    funext p; exact yr_clm_eq _
  rw [this]
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (ContinuousLinearMap.smulRightL ℝ Space G
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ)).continuous.measurable.comp
    (yr_meas_fderiv_apply f y _ hd hm)

/-- The derivative in the phase variable. -/
lemma yr_meas_deriv {X : Type*} [MeasurableSpace X] (f : X → ℝ → Space) (t : ℝ)
    (hd : ∀ p, DifferentiableAt ℝ (f p) t) (hm : ∀ x, Measurable fun p => f p x) :
    Measurable fun p => deriv (f p) t := by
  have := yr_meas_fderiv_apply f t 1 hd hm
  exact this

/-- `iteratedFDeriv 2` is a continuous image of `fderiv (fderiv ·)`. -/
lemma yr_iter2_eq (f : Space → Space) (y : Space) :
    iteratedFDeriv ℝ 2 f y =
      (continuousMultilinearCurryRightEquiv' ℝ 1 Space Space).symm
        ((continuousMultilinearCurryFin1 ℝ Space (Space →L[ℝ] Space)).symm
          (fderiv ℝ (fderiv ℝ f) y)) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  congr 1
  ext m
  simp

lemma yr_meas_iter2 {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → Space → Space)
    (y : Space) (hd : ∀ p, DifferentiableAt ℝ (fderiv ℝ (f p)) y)
    (hm : ∀ x, Measurable fun p => fderiv ℝ (f p) x) :
    AEStronglyMeasurable (fun p => iteratedFDeriv ℝ 2 (f p) y) ν := by
  have h := yr_meas_fderiv (fun p => fderiv ℝ (f p)) y hd hm
  have : (fun p => iteratedFDeriv ℝ 2 (f p) y) = fun p =>
      (continuousMultilinearCurryRightEquiv' ℝ 1 Space Space).symm
        ((continuousMultilinearCurryFin1 ℝ Space (Space →L[ℝ] Space)).symm
          (fderiv ℝ (fderiv ℝ (f p)) y)) := by
    funext p; exact yr_iter2_eq _ _
  rw [this]
  exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable
    ((LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable h.aestronglyMeasurable)

end UnforcedLeray.Short.PartIIIb.Concrete

end
