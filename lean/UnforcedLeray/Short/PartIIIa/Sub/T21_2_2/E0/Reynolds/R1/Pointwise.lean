import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_2_1

/-!
# `PartIII-a:T21/2/2/2/2/1/2`: pointwise facts of the adjoint flow (SP 3060-3073)

For `r ∈ (t, s)`:
* `φ(·, x)` is differentiable at `r` with derivative `adjDt t s φ r x` (the joint smoothness of
  `φ` on the open set `(t, s) × ℝ²` gives a partial derivative in the age, and `derivWithin` on
  the neighbourhood `[t, s)` of `r` is the ordinary derivative);
* `φ(r')` is continuous, hence a.e.-strongly measurable, for `r'` near `r`;
* `wtPhys` is measurable in `x` for every age.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

theorem physE0Pointwise (m : ℝ) : UnforcedLeray.Short.IIIa.E0.PhysE0Pointwise m := by
  intro ν hν tr t s ht hts g φ hφ r hr
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hnhds : Ico t s ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 (r, x) :=
      prod_mem_nhds (Ico_mem_nhds hr.1 hr.2) univ_mem
    have hC : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x) :=
      hφ.jointSmooth.contDiffAt hnhds
    have hF : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
        (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x)) (r, x) :=
      (hC.differentiableAt (by simp)).hasFDerivAt
    have hline : HasDerivAt (fun q : ℝ => (q, x)) ((1 : ℝ), (0 : ℝ × ℝ)) r :=
      (hasDerivAt_id' r).prodMk (hasDerivAt_const r x)
    have hcomp := hF.comp_hasDerivAt r hline
    have hHD : HasDerivAt (fun q => φ q x)
        (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x) ((1 : ℝ), (0 : ℝ × ℝ))) r :=
      hcomp
    have hdw : adjDt t s φ r x = deriv (fun q => φ q x) r := by
      unfold adjDt
      exact derivWithin_of_mem_nhds (Ico_mem_nhds hr.1 hr.2)
    rw [hdw]
    exact hHD.differentiableAt.hasDerivAt
  · filter_upwards [Ico_mem_nhds hr.1 hr.2] with r' hr'
    exact (hφ.smooth r' hr').continuous.aestronglyMeasurable
  · intro r'
    unfold wtPhys periodicWeight
    fun_prop

end UnforcedLeray.Short.IIIa.E0
