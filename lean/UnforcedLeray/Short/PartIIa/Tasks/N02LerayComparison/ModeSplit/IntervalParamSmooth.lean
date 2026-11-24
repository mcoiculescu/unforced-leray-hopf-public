import UnforcedLeray.Short.PartIIa.Sub.N02_5
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Order.CompletePartialOrder

/-!


Target: `intervalParamSmooth_proof : IntervalParamSmooth`.
Source of record `the November 2 reference manuscript`, lines 1738-1750: the
zero-frequency part `f_0 = c⁻¹ ∫_0^c f dq` of a smooth test is again smooth, by differentiation
under the `q`-integral over the compact interval `[a, b]`.

Proof. The first derivative is obtained by dominated differentiation: the derivative of the
integrand is bounded on a neighbourhood of the base point times `uIcc a b`, by compactness of
`uIcc a b` (tube lemma). Smoothness of any finite order is then proved by induction on the order,
for all complete codomains at once, because the derivative takes values in `P →L[ℝ] V`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

namespace IntervalParamSmoothAux

/-- First derivative under the `q`-integral over `[a, b]`, for a `C¹` integrand. -/
theorem ipsHasFDeriv (P V : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (a b : ℝ)
    (H : P × ℝ → V) (hH : ContDiff ℝ 1 H) (x₀ : P) :
    HasFDerivAt (fun x : P => ∫ q in a..b, H (x, q))
      (∫ q in a..b, (fderiv ℝ H (x₀, q)).comp (ContinuousLinearMap.inl ℝ P ℝ)) x₀ := by
  have hHc : Continuous H := hH.continuous
  have hfd : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by norm_num)
  have hΦc : Continuous (fun z : P × ℝ => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ P ℝ)) :=
    hfd.clm_comp continuous_const
  have hcont₀ : Continuous
      (fun y : ℝ => (fderiv ℝ H (x₀, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)) :=
    hΦc.comp (by fun_prop : Continuous fun y : ℝ => (x₀, y))
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hcont₀.continuousOn
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ uIcc a b,
      ‖(fderiv ℝ H (x, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ < C + 1 := by
    refine isCompact_uIcc.eventually_forall_of_forall_eventually
      (P := fun x y => ‖(fderiv ℝ H (x, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ < C + 1) ?_
    intro y hy
    have hb : ‖(fderiv ℝ H (x₀, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ ≤ C := hC y hy
    have hlt : ‖(fderiv ℝ H (x₀, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ < C + 1 := by
      linarith
    exact (hΦc.norm.continuousAt).eventually_lt continuousAt_const hlt
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume)
    (F := fun x q => H (x, q))
    (F' := fun x q => (fderiv ℝ H (x, q)).comp (ContinuousLinearMap.inl ℝ P ℝ))
    (bound := fun _ => C + 1)
    (s := {x : P | ∀ y ∈ uIcc a b,
      ‖(fderiv ℝ H (x, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ < C + 1})
    hev ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous fun q : ℝ => H (x, q)).aestronglyMeasurable
  · exact (by fun_prop : Continuous fun q : ℝ => H (x₀, q)).intervalIntegrable a b
  · exact hcont₀.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht x hx => ?_
    have h1 : ∀ y ∈ uIcc a b,
        ‖(fderiv ℝ H (x, y)).comp (ContinuousLinearMap.inl ℝ P ℝ)‖ < C + 1 := hx
    exact (h1 t (uIoc_subset_uIcc ht)).le
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t _ x _ => ?_
    have hdiff : DifferentiableAt ℝ H (x, t) := (hH.differentiable one_ne_zero) (x, t)
    have hpair : HasFDerivAt (fun x' : P => (x', t)) (ContinuousLinearMap.inl ℝ P ℝ) x :=
      hasFDerivAt_prodMk_left x t
    exact hdiff.hasFDerivAt.comp x hpair

/-- Smoothness of `x ↦ ∫_a^b H(x, q) dq` in every finite order, for all complete codomains. -/
theorem ipsContDiff (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (a b : ℝ) :
    ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (H : P × ℝ → V), ContDiff ℝ n H → ContDiff ℝ n (fun x : P => ∫ q in a..b, H (x, q)) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ H hH
    rw [Nat.cast_zero, contDiff_zero] at hH ⊢
    have hHu : Continuous (Function.uncurry fun (x : P) (t : ℝ) => H (x, t)) := hH
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hHu a b
  | succ n ih =>
    intro V _ _ _ H hH
    have hH1 : ContDiff ℝ 1 H := hH.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hfd : ContDiff ℝ n (fderiv ℝ H) := hH.fderiv_right (by norm_num)
    have hH' : ContDiff ℝ n (fun z : P × ℝ => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ P ℝ)) :=
      hfd.clm_comp contDiff_const
    refine contDiff_succ_iff_hasFDerivAt.2
      ⟨fun x : P => ∫ q in a..b, (fderiv ℝ H (x, q)).comp (ContinuousLinearMap.inl ℝ P ℝ),
        ih (P →L[ℝ] V) (fun z : P × ℝ => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ P ℝ)) hH',
        fun x => ipsHasFDeriv P V a b H hH1 x⟩

end IntervalParamSmoothAux

/-- Target: `IntervalParamSmooth` (`Sub/N02_5.lean`). Smooth dependence on a parameter of an
integral over a compact interval, with the derivative formula. -/
theorem intervalParamSmooth_proof : IntervalParamSmooth := by
  intro P V _ _ _ _ _ a b H hH
  have hH1 : ContDiff ℝ 1 H := by exact_mod_cast contDiff_infty.1 hH 1
  refine ⟨contDiff_infty.2 fun n =>
    IntervalParamSmoothAux.ipsContDiff P a b n V H (contDiff_infty.1 hH n), fun x v => ?_⟩
  rw [(IntervalParamSmoothAux.ipsHasFDeriv P V a b H hH1 x).fderiv]
  have hcont : Continuous
      (fun q : ℝ => (fderiv ℝ H (x, q)).comp (ContinuousLinearMap.inl ℝ P ℝ)) := by
    have hfd : Continuous (fderiv ℝ H) := hH1.continuous_fderiv one_ne_zero
    have hΦc : Continuous (fun z : P × ℝ => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ P ℝ)) :=
      hfd.clm_comp continuous_const
    exact hΦc.comp (by fun_prop : Continuous fun q : ℝ => (x, q))
  have hint : IntervalIntegrable
      (fun q : ℝ => (fderiv ℝ H (x, q)).comp (ContinuousLinearMap.inl ℝ P ℝ)) volume a b :=
    hcont.intervalIntegrable a b
  rw [ContinuousLinearMap.intervalIntegral_apply hint v]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

end UnforcedLeray.Short.PartIIa
