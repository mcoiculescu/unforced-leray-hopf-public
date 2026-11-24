import UnforcedLeray.Analysis.Sturm.OneDRegularityH2
import UnforcedLeray.Analysis.Sturm.OneDRegularitySecond
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Continuous second derivatives of genuine weak H² functions

The actual Green reconstruction upgrades a given C¹ representative when the
second weak derivative has a continuous representative. No classical second
derivative or boundary condition is assumed.
-/
noncomputable section
open MeasureTheory Set Filter
namespace UnforcedLeray.Rayleigh.RealSpeed
open Sturm NonUniqueEuler.Sob

/-- A continuous representative of the actual second weak derivative gives
classical C² regularity and the pointwise second derivative identity. -/
theorem c1_contDiff_two_of_continuous_second {u du ddu : ComplexL2}
    (v : C1L2Representative u du)
    (h2 : HasWeakDerivOn univ (derivList 2) (u : ℝ → ℂ) (ddu : ℝ → ℂ))
    {s : ℝ → ℂ} (hs : Continuous s) (hsAE : (ddu : ℝ → ℂ) =ᵐ[volume] s) :
    ContDiff ℝ 2 v.value ∧ deriv (deriv v.value) = s := by
  let f : ComplexL2 := ((2 : ℝ) : ℂ) ^ 2 • u - ddu
  let source : ℝ → ℂ := fun t => (4 : ℂ) * v.value t - s t
  have hsource : Continuous source :=
    (continuous_const.mul v.continuous).sub hs
  have hfAE : (f : ℝ → ℂ) =ᵐ[volume] source := by
    filter_upwards [Lp.coeFn_sub (((2 : ℝ) : ℂ) ^ 2 • u) ddu,
      Lp.coeFn_smul (((2 : ℝ) : ℂ) ^ 2) u, v.value_ae, hsAE] with t hsub hsm hu hd
    change f t = source t
    simpa only [f, source, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hu, hd,
      Complex.ofReal_ofNat, show (2 : ℂ) ^ 2 = 4 by norm_num] using
      hsub.trans (congrArg (fun z : ℂ => z - ddu t) hsm)
  have hf2 : MemLp source 2 volume := (Lp.memLp f).ae_eq hfAE
  have hrec : freeResolventOperator (by norm_num : (0 : ℝ) < 2) f = u :=
    weakH2_eq_freeResolvent (by norm_num) u ddu h2
  have hvR : v.value = freeResolvent 2 (f : ℝ → ℂ) := by
    have ha := coeFn_freeResolventOperator (by norm_num : (0 : ℝ) < 2) f
    rw [hrec] at ha
    exact Measure.eq_of_ae_eq (v.value_ae.symm.trans ha) v.continuous
      (contDiff_one_freeResolvent_of_memLp (by norm_num) (Lp.memLp f)).continuous
  have hvsource : v.value = freeResolvent 2 source :=
    hvR.trans (freeResolvent_congr_ae 2 hfAE)
  constructor
  · rw [hvsource]
    exact contDiff_two_freeResolvent_of_memLp_continuous (by norm_num) hf2 hsource
  · rw [hvsource, deriv_freeResolvent_of_memLp (by norm_num : (0 : ℝ) < 2) hf2,
      deriv_freeResolventDeriv_of_memLp_continuous (by norm_num : (0 : ℝ) < 2)
        hf2 hsource]
    funext t
    rw [← hvsource]
    simp only [source, Complex.ofReal_ofNat]
    ring

end UnforcedLeray.Rayleigh.RealSpeed
