import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub2

/-!
# `KF2a` (source 3606-3608, 3613): joint strong measurability of the explicit semigroup integrand

Proof: the integrand `((t, w), y) ↦ G_{θ_t}(y) F(e^{t/2}w.1 - y, w.2 - t)_i` is strongly
measurable (`Lp.stronglyMeasurable` of `F` composed with a measurable map, then a coordinate
projection; `heatG` measurable), so `StronglyMeasurable.integral_prod_right'` gives the
`y`-integral jointly measurable in `(t, w)`; multiply by the continuous `e^{t/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.B0223 UnforcedLeray.Infra

theorem kf2a : KF2a := by
  intro ν ε P _ F i
  -- the argument map of `F`
  have hm : Measurable (fun q : (ℝ × PSpace P) × Space =>
      (Real.exp (q.1.1 / 2) • q.1.2.1 - q.2, q.1.2.2 - (q.1.1 : AddCircle P))) := by
    refine Measurable.prodMk ?_ ?_
    · fun_prop
    · fun_prop
  have hFm : StronglyMeasurable (fun q : (ℝ × PSpace P) × Space =>
      F (Real.exp (q.1.1 / 2) • q.1.2.1 - q.2, q.1.2.2 - (q.1.1 : AddCircle P))) :=
    (Lp.stronglyMeasurable F).comp_measurable hm
  have hFi : StronglyMeasurable (fun q : (ℝ × PSpace P) × Space =>
      F (Real.exp (q.1.1 / 2) • q.1.2.1 - q.2, q.1.2.2 - (q.1.1 : AddCircle P)) i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) i).comp_stronglyMeasurable hFm
  -- the heat kernel factor
  have hH : Measurable (fun q : (ℝ × PSpace P) × Space =>
      ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp q.1.1 - 1)) q.2 : ℝ) : ℂ)) := by
    unfold UnforcedLeray.Short.IIIa.heatG
    fun_prop
  -- the joint integrand
  have hK : StronglyMeasurable (fun q : (ℝ × PSpace P) × Space =>
      ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp q.1.1 - 1)) q.2 : ℝ) : ℂ) *
        (F (Real.exp (q.1.1 / 2) • q.1.2.1 - q.2, q.1.2.2 - (q.1.1 : AddCircle P)) i)) :=
    hH.stronglyMeasurable.mul hFi
  -- integrate out `y`
  have hInt : StronglyMeasurable (fun p : ℝ × PSpace P => ∫ y : Space,
      ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp p.1 - 1)) y : ℝ) : ℂ) *
        (F (Real.exp (p.1 / 2) • p.2.1 - y, p.2.2 - (p.1 : AddCircle P)) i)) :=
    hK.integral_prod_right'
  -- multiply by the continuous factor `e^{t/2}`
  have hc : Continuous (fun p : ℝ × PSpace P => ((Real.exp (p.1 / 2) : ℝ) : ℂ)) := by
    fun_prop
  exact hc.stronglyMeasurable.mul hInt

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
