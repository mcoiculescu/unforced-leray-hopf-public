import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2.TailIterated
import UnforcedLeray.Lib.Kernels.GaussDeriv

/-!
# `PartIII-b:C/rep/5/1/2/4/1/2/4/2/3`: `TailPartDt` (FTC in the lower limit)

Proves `tailPartDt : TailPartDt` (source 3600-3610: `∂_t ∫_t^∞ G_a da = -G_t`).

Strategy.
* `part2_eq_hess_tp`: `part2 f i j y = D²f(y)(e_i, e_j)` for `C^∞` functions `f`.
* `fderiv_part2_eq_iter_tp`: `∂_k (part2 f i j)(x) = D³f(x)(e_k, e_i, e_j)`.
* `tail_main_tp`: for a continuous linear functional `Λ` on the third-order multilinear maps,
  `∂_t Λ(D³ T_t(x)) = -Λ(D³G_t(x))`, where `D³T_t(x) = ∫_t^∞ D³G_a(x) da` (`tailIterated`), by
  the scalar FTC in the lower limit (`hasDerivAt_tail_integral_tp`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.KPH

open UnforcedLeray.Short.IIIa

/-- The second partial in Hessian form, for a `C^∞` function. -/
private lemma part2_eq_hess_tp {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 3) (y : Space) :
    part2 f i j y = iteratedFDeriv ℝ 2 f y ![coordinateVector i, coordinateVector j] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp)) y
  have hu : DifferentiableAt ℝ (fun _ : Space => coordinateVector j) y := differentiableAt_const _
  have hc : fderiv ℝ (fun z => fderiv ℝ f z (coordinateVector j)) y =
      (fderiv ℝ (fderiv ℝ f) y).flip (coordinateVector j) := by
    have := fderiv_clm_apply (u := fun _ : Space => coordinateVector j) hd hu
    simpa [fderiv_const_apply] using this
  rw [iteratedFDeriv_two_apply]
  unfold part2
  rw [hc]
  simp

/-- The third-order identity: `∂_k (part2 f i j)(x) = D³f(x)(e_k, e_i, e_j)` for `C^∞` `f`. -/
private lemma fderiv_part2_eq_iter_tp {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (i j k : Fin 3)
    (x : Space) :
    fderiv ℝ (fun y => part2 f i j y) x (coordinateVector k) =
      iteratedFDeriv ℝ 3 f x ![coordinateVector k, coordinateVector i, coordinateVector j] := by
  have hA : Differentiable ℝ (iteratedFDeriv ℝ 2 f) :=
    hf.differentiable_iteratedFDeriv (m := 2) (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top 2))
  have hfun : (fun y => part2 f i j y) =
      fun y => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) ℝ
        ![coordinateVector i, coordinateVector j]) (iteratedFDeriv ℝ 2 f y) := by
    funext y
    exact part2_eq_hess_tp hf i j y
  have hD : HasFDerivAt
      (fun y => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) ℝ
        ![coordinateVector i, coordinateVector j]) (iteratedFDeriv ℝ 2 f y))
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) ℝ
        ![coordinateVector i, coordinateVector j]).comp (fderiv ℝ (iteratedFDeriv ℝ 2 f) x)) x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) ℝ
      ![coordinateVector i, coordinateVector j]).hasFDerivAt.comp x (hA x).hasFDerivAt
  have h3 : iteratedFDeriv ℝ 3 f x ![coordinateVector k, coordinateVector i, coordinateVector j] =
      fderiv ℝ (iteratedFDeriv ℝ 2 f) x (coordinateVector k)
        ![coordinateVector i, coordinateVector j] := by
    rw [iteratedFDeriv_succ_apply_left]
    rfl
  rw [hfun, hD.fderiv, h3]
  rfl

/-- FTC in the lower limit for a continuous, locally integrable scalar profile `h` on `(0, ∞)`:
`d/ds ∫_s^∞ h = -h(t)`. -/
private lemma hasDerivAt_tail_integral_tp {h : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hc : ContinuousOn h (Ioi 0))
    (hi : ∀ s : ℝ, 0 < s → IntegrableOn h (Ioi s)) :
    HasDerivAt (fun s => ∫ a in Ioi s, h a) (-h t) t := by
  have hdec : ∀ s : ℝ, 0 < s → s ≤ t + 1 →
      ∫ a in Ioi s, h a = (∫ a in s..(t + 1), h a) + ∫ a in Ioi (t + 1), h a := by
    intro s hs hst
    have hI1 : IntegrableOn h (Ioc s (t + 1)) := (hi s hs).mono_set Ioc_subset_Ioi_self
    have hI2 : IntegrableOn h (Ioi (t + 1)) := hi (t + 1) (by linarith)
    rw [← Set.Ioc_union_Ioi_eq_Ioi hst,
      MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hI1 hI2,
      intervalIntegral.integral_of_le hst]
  have hcI : ContinuousOn h (uIcc t (t + 1)) := by
    apply hc.mono
    intro a ha
    rw [Set.uIcc_of_le (by linarith : t ≤ t + 1)] at ha
    exact lt_of_lt_of_le ht ha.1
  have hint : IntervalIntegrable h volume t (t + 1) := hcI.intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter h (𝓝 t) :=
    hc.stronglyMeasurableAtFilter isOpen_Ioi t ht
  have hcont : ContinuousAt h t := hc.continuousAt (Ioi_mem_nhds ht)
  have hD : HasDerivAt (fun s => ∫ a in s..(t + 1), h a) (-h t) t :=
    intervalIntegral.integral_hasDerivAt_left hint hmeas hcont
  have hD2 := hD.add_const (∫ a in Ioi (t + 1), h a)
  refine hD2.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht (lt_add_one t)] with s hs
  exact hdec s hs.1 hs.2.le

/-- The scalar-functional form: `∂_t Λ(D³T_t(x)) = -Λ(D³G_t(x))`. -/
private lemma tail_main_tp {t : ℝ} (ht : 0 < t) (x : Space)
    (Λ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Space) ℝ →L[ℝ] ℝ) :
    HasDerivAt (fun s => Λ (iteratedFDeriv ℝ 3 (heatTail s) x))
      (-(Λ (iteratedFDeriv ℝ 3 (heatG t) x))) t := by
  have hfin : ∀ s : ℝ, 0 < s → IntegrableOn (fun a => iteratedFDeriv ℝ 3 (heatG a) x) (Ioi s) := by
    intro s hs
    simp only [heatG_eq_heatKernel]
    exact UnforcedLeray.Kernels.integrableOn_iteratedFDeriv_heatKernel_time 3 hs.le (Or.inr hs)
  have hcont : ContinuousOn (fun a => iteratedFDeriv ℝ 3 (heatG a) x) (Ioi 0) := by
    simp only [heatG_eq_heatKernel]
    exact UnforcedLeray.Kernels.continuousOn_iteratedFDeriv_heatKernel 3 x
  have hc : ContinuousOn (fun a => Λ (iteratedFDeriv ℝ 3 (heatG a) x)) (Ioi 0) :=
    Λ.continuous.comp_continuousOn hcont
  have hi : ∀ s : ℝ, 0 < s → IntegrableOn (fun a => Λ (iteratedFDeriv ℝ 3 (heatG a) x)) (Ioi s) :=
    fun s hs => ContinuousLinearMap.integrable_comp Λ (hfin s hs)
  have hF := hasDerivAt_tail_integral_tp ht hc hi
  have hEv : (fun s => Λ (iteratedFDeriv ℝ 3 (heatTail s) x)) =ᶠ[𝓝 t]
      (fun s => ∫ a in Ioi s, Λ (iteratedFDeriv ℝ 3 (heatG a) x)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [(tailIterated s hs).2 3 x]
    exact (ContinuousLinearMap.integral_comp_comm Λ (hfin s hs)).symm
  exact hF.congr_of_eventuallyEq hEv

/-- **`PartIII-b:C/rep/5/1/2/4/1/2/4/2/3`**: `∂_t ∂_k∂_i∂_j ∫_t^∞ G_a da = -∂_k∂_i∂_j G_t`. -/
theorem tailPartDt : UnforcedLeray.Short.PartIIIb.Concrete.KPH.TailPartDt := by
  intro t ht i j k x
  have key := tail_main_tp ht x (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => Space) ℝ
    ![coordinateVector k, coordinateVector i, coordinateVector j])
  have hEv : (fun s => fderiv ℝ (fun y => part2 (heatTail s) i j y) x (coordinateVector k)) =ᶠ[𝓝 t]
      (fun s => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => Space) ℝ
        ![coordinateVector k, coordinateVector i, coordinateVector j])
          (iteratedFDeriv ℝ 3 (heatTail s) x)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [fderiv_part2_eq_iter_tp (tailIterated s hs).1 i j k x]
    rfl
  have hR := fderiv_part2_eq_iter_tp (contDiff_heatG ht) i j k x
  rw [hR]
  exact key.congr_of_eventuallyEq hEv

end UnforcedLeray.Short.PartIIIb.Concrete.KPH
