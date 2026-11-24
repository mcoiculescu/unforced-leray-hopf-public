import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements
import UnforcedLeray.Lib.Kernels.NewtonDerivatives
import UnforcedLeray.Lib.CZL2.NewtonConv
import UnforcedLeray.Lib.Kernels.ParamIntegral
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# `newtonConvFarDeriv`: far-field derivatives of the Newton potential of a test

Target `newtonConvFarDeriv` (`Statements.lean`, item (2a)). Status: partial.

This file proves the estimate half of the target from the differentiation identity
`ncfd_identity` (the derivative of the convolution at a far point is the integral of the kernel
derivative against `f`). The identity is NOT proved here; it is the missing lemma.

Given `ncfd_identity`, on `‖y‖ ≥ 2ρ+1` and `f = 0` for `‖x‖ > ρ`, the bound
`‖D^k(N ∗ f)(y)‖ ≤ |C_k| 2^{k+1} (∫|f|) ‖y‖^{-(k+1)}` follows from `‖y - t‖ ≥ ‖y‖/2` on the support.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.RieszLp

/-- Missing identity: the `k`-th derivative of `N ∗ f` at a far point `y` is the integral of the
`k`-th derivative of the Newton potential against `f` (differentiation under the integral sign,
`hasFDerivAt_integral_of_dominated_of_fderiv_le`, by induction on `k`). -/
def NcfdIdentity : Prop :=
  ∀ (k : ℕ) (f : Space → ℝ) (ρ : ℝ), 0 ≤ ρ → IsSpatialTest f → (∀ x : Space, ρ < ‖x‖ → f x = 0) →
    ∀ y : Space, 2 * ρ + 1 ≤ ‖y‖ →
      iteratedFDeriv ℝ k (newtonConv f) y =
        ∫ t : Space, f t • iteratedFDeriv ℝ k PressureAnalysis.newtonPotential (y - t)

/-- The estimate part of `newtonConvFarDeriv`, given `NcfdIdentity`. -/
theorem ncfd_of_identity (hI : NcfdIdentity) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Space → ℝ) (ρ : ℝ), IsSpatialTest f → 0 ≤ ρ →
      (∀ x : Space, ρ < ‖x‖ → f x = 0) → ∀ y : Space, 2 * ρ + 1 ≤ ‖y‖ →
        ‖iteratedFDeriv ℝ k (newtonConv f) y‖ ≤ C * (∫ x, |f x|) * ‖y‖ ^ (-((k : ℝ) + 1)) := by
  intro k
  obtain ⟨C, hC⟩ := UnforcedLeray.Kernels.norm_iteratedFDeriv_newton_le k
  refine ⟨|C| * (2 : ℝ) ^ (1 + (k : ℝ)), by positivity, ?_⟩
  intro f ρ hf hρ hsupp y hy
  rw [hI k f ρ hρ hf hsupp y hy]
  have hyk : (0 : ℝ) < ‖y‖ := by linarith
  set s : ℝ := ‖y‖ ^ (-((k : ℝ) + 1)) with hs
  set c : ℝ := |C| * (2 : ℝ) ^ (1 + (k : ℝ)) * s with hc
  have hkey : ∀ t : Space, ‖f t • iteratedFDeriv ℝ k PressureAnalysis.newtonPotential (y - t)‖ ≤
      |f t| * c := by
    intro t
    by_cases ht : ‖t‖ ≤ ρ
    · have hyt : ‖y‖ / 2 ≤ ‖y - t‖ := by
        have h1 := norm_sub_norm_le y t
        linarith
      have hpos : 0 < ‖y‖ / 2 := by linarith
      have hne : y - t ≠ 0 := by
        intro h
        rw [h, norm_zero] at hyt
        linarith
      have hD := hC (y - t) hne
      have hexp : (-(1 + (k : ℝ))) ≤ 0 := by
        have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
        linarith
      have hmono : ‖y - t‖ ^ (-(1 + (k : ℝ))) ≤ (‖y‖ / 2) ^ (-(1 + (k : ℝ))) :=
        Real.rpow_le_rpow_of_nonpos hpos hyt hexp
      have hpow : (‖y‖ / 2) ^ (-(1 + (k : ℝ))) = (2 : ℝ) ^ (1 + (k : ℝ)) * s := by
        rw [Real.div_rpow (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2), hs,
          show -((k : ℝ) + 1) = -(1 + (k : ℝ)) by ring,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
        ring
      have hX : 0 ≤ ‖y - t‖ ^ (-(1 + (k : ℝ))) := Real.rpow_nonneg (norm_nonneg _) _
      have hD' : ‖iteratedFDeriv ℝ k PressureAnalysis.newtonPotential (y - t)‖ ≤
          |C| * ((2 : ℝ) ^ (1 + (k : ℝ)) * s) := by
        calc ‖iteratedFDeriv ℝ k PressureAnalysis.newtonPotential (y - t)‖
            ≤ C * ‖y - t‖ ^ (-(1 + (k : ℝ))) := hD
          _ ≤ |C| * ‖y - t‖ ^ (-(1 + (k : ℝ))) :=
              mul_le_mul_of_nonneg_right (le_abs_self C) hX
          _ ≤ |C| * ((‖y‖ / 2) ^ (-(1 + (k : ℝ)))) :=
              mul_le_mul_of_nonneg_left hmono (abs_nonneg C)
          _ = |C| * ((2 : ℝ) ^ (1 + (k : ℝ)) * s) := by rw [hpow]
      rw [norm_smul, Real.norm_eq_abs]
      calc |f t| * ‖iteratedFDeriv ℝ k PressureAnalysis.newtonPotential (y - t)‖
          ≤ |f t| * (|C| * ((2 : ℝ) ^ (1 + (k : ℝ)) * s)) :=
            mul_le_mul_of_nonneg_left hD' (abs_nonneg _)
        _ = |f t| * c := by rw [hc]; ring
    · have hft : f t = 0 := hsupp t (lt_of_not_ge ht)
      simp [hft]
  have hint : Integrable (fun t : Space => |f t| * c) :=
    ((hf.smooth.continuous.integrable_of_hasCompactSupport hf.compact).abs).mul_const c
  calc ‖∫ t : Space, f t • iteratedFDeriv ℝ k PressureAnalysis.newtonPotential (y - t)‖
      ≤ ∫ t : Space, |f t| * c :=
        norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hkey)
    _ = (∫ x, |f x|) * c := integral_mul_const c _
    _ = |C| * (2 : ℝ) ^ (1 + (k : ℝ)) * (∫ x, |f x|) * s := by rw [hc]; ring

/-- A smooth global kernel equal to the Newton potential off the ball of radius `1/2`. -/
def ncfdBump : ContDiffBump (0 : Space) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def smoothNewton : Space → ℝ :=
  fun z => (1 - ncfdBump z) * PressureAnalysis.newtonPotential z

theorem smoothNewton_eq {z : Space} (hz : 1 / 2 < ‖z‖) :
    smoothNewton z = PressureAnalysis.newtonPotential z := by
  have : ncfdBump z = 0 := ncfdBump.zero_of_le_dist (by simp [ncfdBump, dist_zero_right]; norm_num; exact hz.le)
  simp [smoothNewton, this]

theorem smoothNewton_contDiff : ContDiff ℝ ∞ smoothNewton := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have h0 : smoothNewton =ᶠ[𝓝 (0 : Space)] fun _ => 0 := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : Space) (show (0:ℝ) < 1 / 4 by norm_num)]
        with w hw
      have : ncfdBump w = 1 := ncfdBump.one_of_mem_closedBall (by simpa [ncfdBump] using hw)
      simp [smoothNewton, this]
    exact (contDiffAt_const).congr_of_eventuallyEq h0
  · exact (contDiffAt_const.sub ncfdBump.contDiffAt).mul (UnforcedLeray.Kernels.contDiffAt_newton hz)

theorem ncfdIdentity : NcfdIdentity := by
  intro k f ρ hρ hf hsupp y hy
  let F : Space → Space → ℝ := fun t x => f t * smoothNewton (x - t)
  have hK := smoothNewton_contDiff
  have hshift : ∀ t : Space, ContDiff ℝ ∞ (fun x : Space => smoothNewton (x - t)) :=
    fun t => hK.comp (by fun_prop)
  have hsmooth : ∀ᵐ t ∂(volume : Measure Space), ContDiff ℝ ∞ (F t) :=
    Filter.Eventually.of_forall fun t => contDiff_const.mul (hshift t)
  have hiter : ∀ (n : ℕ) (t x : Space), iteratedFDeriv ℝ n (F t) x =
      f t • iteratedFDeriv ℝ n smoothNewton (x - t) := by
    intro n t x
    change iteratedFDeriv ℝ n (fun x : Space => f t • smoothNewton (x - t)) x = _
    rw [iteratedFDeriv_const_smul_apply' ((hshift t).contDiffAt.of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_comp_sub']
  have hcontD : ∀ n : ℕ, Continuous (iteratedFDeriv ℝ n smoothNewton) := fun n =>
    hK.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hmeas : ∀ (n : ℕ) (x : Space),
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ n (F t) x) volume := by
    intro n x
    have hc : Continuous (fun t : Space => f t • iteratedFDeriv ℝ n smoothNewton (x - t)) :=
      hf.continuous.smul ((hcontD n).comp (by fun_prop))
    exact hc.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun t => (hiter n t x).symm)
  have hfint : Integrable f := hf.continuous.integrable_of_hasCompactSupport hf.compact
  have hdom : UnforcedLeray.Kernels.LocDominated volume F univ := by
    intro n x _
    refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Space) (‖x‖ + 1 + ρ)).exists_bound_of_continuousOn
      (hcontD n).continuousOn
    refine ⟨fun t => |f t| * B, hfint.abs.mul_const B, Filter.Eventually.of_forall fun t y hy' => ?_⟩
    rw [hiter, norm_smul, Real.norm_eq_abs]
    by_cases ht : ‖t‖ ≤ ρ
    · refine mul_le_mul_of_nonneg_left (hB _ ?_) (abs_nonneg _)
      have h1 : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using hy'
      have h2 : ‖y - t‖ ≤ ‖y - x‖ + ‖x‖ + ‖t‖ := by
        calc ‖y - t‖ = ‖(y - x) + x - t‖ := by congr 1; abel
          _ ≤ ‖(y - x) + x‖ + ‖t‖ := norm_sub_le _ _
          _ ≤ ‖y - x‖ + ‖x‖ + ‖t‖ := by gcongr; exact norm_add_le _ _
      simp only [Metric.mem_closedBall, dist_zero_right]
      linarith
    · simp [hsupp t (lt_of_not_ge ht)]
  have hmain := UnforcedLeray.Kernels.iteratedFDeriv_integral_eq isOpen_univ hsmooth hmeas hdom k
    (x := y) (mem_univ _)
  -- identify newtonConv with the integral on the open set `‖·‖ > 2ρ + 1/2`
  have hEq : newtonConv f =ᶠ[𝓝 y] fun x => ∫ t, F t x := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
      (show 2 * ρ + 1 / 2 < ‖y‖ by linarith)] with x hx
    unfold newtonConv
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : ‖t‖ ≤ ρ
    · have : 1 / 2 < ‖x - t‖ := by
        have := norm_sub_norm_le x t
        have hx : 2 * ρ + 1 / 2 < ‖x‖ := hx
        linarith
      simp only [F, smoothNewton_eq this, mul_comm]
    · simp [F, hsupp t (lt_of_not_ge ht)]
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hEq k).eq_of_nhds, hmain]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show iteratedFDeriv ℝ k (F t) y = _
  rw [hiter]
  by_cases ht : ‖t‖ ≤ ρ
  · have h12 : 1 / 2 < ‖y - t‖ := by
      have := norm_sub_norm_le y t
      linarith
    have : iteratedFDeriv ℝ k smoothNewton (y - t) =
        iteratedFDeriv ℝ k PressureAnalysis.newtonPotential (y - t) := by
      refine (Filter.EventuallyEq.iteratedFDeriv ℝ ?_ k).eq_of_nhds
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h12] with w hw
      exact smoothNewton_eq hw
    rw [this]
  · simp [hsupp t (lt_of_not_ge ht)]

theorem newtonConvFarDeriv : NewtonConvFarDeriv := ncfd_of_identity ncfdIdentity

#print axioms newtonConvFarDeriv

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
