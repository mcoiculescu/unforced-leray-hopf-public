import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.B.Util

/-!
# `∂_t part2(∫_t^∞G) = -part2 G_t` and `Δ ∫_t^∞ G = -G_t` (source 3598-3610)

Differentiation under the integral is the library `iteratedFDeriv_heatTimePotential`
(`D^n ∫_t^∞ G_a = ∫_t^∞ D^n G_a`, `t > 0`); then FTC in `t`, and FTC on `(t,∞)` with `∂_aG_a = ΔG_a`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma smooth_two {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ 2 g :=
  hg.of_le (by simp)

lemma part2_heatG_eq (a : ℝ) (i j : Fin 3) (x : Space) :
    IIIa.part2 (IIIa.heatG a) i j x = iteratedFDeriv ℝ 2 (Heat.kernel a) x
      ![UnforcedLeray.coordinateVector i, UnforcedLeray.coordinateVector j] := by
  rw [part2_eq_iter (smooth_two (heatG_smooth a)), IIIa.heatG_eq_heatKernel]

lemma integrableOn_iter_apply {t : ℝ} (ht : 0 < t) (y : Space) (m : Fin 2 → Space) :
    IntegrableOn (fun a => iteratedFDeriv ℝ 2 (Heat.kernel a) y m) (Ioi t) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) ℝ m).integrable_comp
    (Kernels.integrableOn_iteratedFDeriv_heatKernel_time 2 ht.le (Or.inr ht))

lemma part2_tail_integral {t : ℝ} (ht : 0 < t) (i j : Fin 3) (x : Space) :
    IIIa.part2 (IIIa.heatTail t) i j x = ∫ a in Ioi t, IIIa.part2 (IIIa.heatG a) i j x := by
  rw [part2_eq_iter (smooth_two (heatTail_smooth ht)), heatTail_eq_potential,
    Kernels.iteratedFDeriv_heatTimePotential 2 ht.le (Or.inr ht),
    ContinuousMultilinearMap.integral_apply
      (Kernels.integrableOn_iteratedFDeriv_heatKernel_time 2 ht.le (Or.inr ht))]
  refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
  rw [part2_heatG_eq]

lemma part2_tail_hasDerivAt {t : ℝ} (ht : 0 < t) (i j : Fin 3) (x : Space) :
    HasDerivAt (fun s => IIIa.part2 (IIIa.heatTail s) i j x)
      (-IIIa.part2 (IIIa.heatG t) i j x) t := by
  set m : Fin 2 → Space := ![UnforcedLeray.coordinateVector i, UnforcedLeray.coordinateVector j]
  have hc : ContinuousOn (fun a => IIIa.part2 (IIIa.heatG a) i j x) (Ioi 0) := by
    have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) ℝ m).continuous.comp_continuousOn
      (Kernels.continuousOn_iteratedFDeriv_heatKernel 2 x)
    refine this.congr fun a _ => ?_
    simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply]
    exact part2_heatG_eq a i j x
  have hi : IntegrableOn (fun a => IIIa.part2 (IIIa.heatG a) i j x) (Ioi (t / 2)) := by
    have h := integrableOn_iter_apply (t := t / 2) (by positivity) x m
    exact h.congr_fun (fun a _ => (part2_heatG_eq a i j x).symm) measurableSet_Ioi
  have hd := hasDerivAt_integral_Ioi ht hc hi
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact part2_tail_integral (show (0 : ℝ) < s from hs) i j x

lemma lap_iter {K : Space → ℝ} (hK : ContDiff ℝ 2 K) (z : Space) :
    Heat.laplacian K z = ∑ l : Fin 3, iteratedFDeriv ℝ 2 K z
      ![UnforcedLeray.coordinateVector l, UnforcedLeray.coordinateVector l] := by
  rw [Heat.laplacian_eq_sum_fderiv_fderiv hK z]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp

lemma heatG_tendsto (y : Space) : Tendsto (fun s => IIIa.heatG s y) atTop (𝓝 0) := by
  have e : (-3 / 2 : ℝ) = -(3 / 2) := by norm_num
  have hb : Tendsto (fun s : ℝ => (4 * Real.pi * s) ^ (-3 / 2 : ℝ)) atTop (𝓝 0) := by
    rw [e]
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp
      (tendsto_id.const_mul_atTop (by positivity))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with s hs
    unfold IIIa.heatG
    positivity
  · filter_upwards [eventually_gt_atTop 0] with s hs
    unfold IIIa.heatG
    have h1 : Real.exp (-‖y‖ ^ 2 / (4 * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ ‖y‖ ^ 2 / (4 * s) := by positivity
      rw [neg_div]; linarith
    have h2 : 0 ≤ (4 * Real.pi * s) ^ (-3 / 2 : ℝ) := by positivity
    nlinarith

theorem lap_tail {t : ℝ} (ht : 0 < t) (y : Space) :
    Heat.laplacian (IIIa.heatTail t) y = -IIIa.heatG t y := by
  set e : Fin 3 → Fin 2 → Space := fun l =>
    ![UnforcedLeray.coordinateVector l, UnforcedLeray.coordinateVector l] with he
  have hint0 : ∀ l ∈ (Finset.univ : Finset (Fin 3)),
      IntegrableOn (fun a => iteratedFDeriv ℝ 2 (Heat.kernel a) y (e l)) (Ioi t) :=
    fun l _ => integrableOn_iter_apply ht y (e l)
  have hsum : IntegrableOn (fun a => ∑ l : Fin 3, iteratedFDeriv ℝ 2 (Heat.kernel a) y (e l)) (Ioi t) :=
    integrable_finset_sum _ hint0
  have hint : IntegrableOn (fun a => Heat.laplacian (Heat.kernel a) y) (Ioi t) := by
    refine hsum.congr_fun (fun a _ => ?_) measurableSet_Ioi
    exact (lap_iter (smooth_two (Kernels.heatKernel_smooth a)) y).symm
  have h1 : Heat.laplacian (IIIa.heatTail t) y = ∫ a in Ioi t, Heat.laplacian (Heat.kernel a) y := by
    rw [lap_iter (smooth_two (heatTail_smooth ht)), heatTail_eq_potential,
      Kernels.iteratedFDeriv_heatTimePotential 2 ht.le (Or.inr ht)]
    have hk : ∀ l : Fin 3, (∫ a in Ioi t, iteratedFDeriv ℝ 2 (Heat.kernel a) y) (e l) =
        ∫ a in Ioi t, iteratedFDeriv ℝ 2 (Heat.kernel a) y (e l) := fun l =>
      ContinuousMultilinearMap.integral_apply
        (Kernels.integrableOn_iteratedFDeriv_heatKernel_time 2 ht.le (Or.inr ht)) (e l)
    simp only [← he] at *
    rw [Finset.sum_congr rfl (fun l _ => hk l), ← integral_finset_sum _ hint0]
    refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
    exact (lap_iter (smooth_two (Kernels.heatKernel_smooth a)) y).symm
  rw [h1]
  have hcont : ContinuousWithinAt (fun s => Heat.kernel s y) (Ici t) t :=
    (Heat.kernel_hasDerivAt_laplacian ht y).continuousAt.continuousWithinAt
  have hder : ∀ a ∈ Ioi t, HasDerivAt (fun s => Heat.kernel s y)
      (Heat.laplacian (Heat.kernel a) y) a :=
    fun a ha => Heat.kernel_hasDerivAt_laplacian (lt_trans ht ha) y
  have hlim : Tendsto (fun s => Heat.kernel s y) atTop (𝓝 0) := by
    have := heatG_tendsto y
    simpa only [IIIa.heatG_eq_heatKernel] using this
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hder hint hlim
  rw [this, IIIa.heatG_eq_heatKernel]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
