import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2.TailIterated
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_4_2.GaussHeat
import UnforcedLeray.Lib.Kernels.GaussDeriv

/-!
# `PartIII-b:C/rep/5/1/2/4/1/2/4/2/4`: `TailLapPart` (Laplacian of the tail third derivative)

Proves `tailLapPart : TailLapPart` (source 3600-3610: `Δ ∫_t^∞ G_a da = -G_t`, applied to the
third derivatives `∂_k∂_i∂_j`).

Strategy.
* `fderiv_part2_eq_iter_L`: `∂_k (part2 f i j)(y) = D³f(y)(e_k, e_i, e_j)` for `C^∞` `f`
  (copied from `TailPartDt`, whose copy is private).
* `fderiv_iter_apply_L`: `∂_w (y ↦ D^n f(y) v) = D^{n+1} f(y)(w, v)`.
  Applied twice, the nested Laplacian is `Σ_l D⁵T_t(x)(e_l, e_l, e_k, e_i, e_j)`.
* `tailIterated` turns `D⁵T_t(x)` into `∫_{(t,∞)} D⁵G_a(x)`; the sum over `l` inside the integral
  equals `∂_a D³G_a(x)(v)` by `gaussHeat` (second clause, `n = 3`).
* FTC on `(t, ∞)`: `∫_{(t,∞)} ∂_a h = -h(t)` since `h(a) = D³G_a(x)(v) → 0` as `a → ∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.KPH

open UnforcedLeray.Short.IIIa

/-- The second partial in Hessian form, for a `C^∞` function. -/
private lemma part2_eq_hess_L {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 3) (y : Space) :
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
private lemma fderiv_part2_eq_iter_L {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (i j k : Fin 3)
    (x : Space) :
    fderiv ℝ (fun y => part2 f i j y) x (coordinateVector k) =
      iteratedFDeriv ℝ 3 f x ![coordinateVector k, coordinateVector i, coordinateVector j] := by
  have hA : Differentiable ℝ (iteratedFDeriv ℝ 2 f) :=
    hf.differentiable_iteratedFDeriv (m := 2) (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top 2))
  have hfun : (fun y => part2 f i j y) =
      fun y => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) ℝ
        ![coordinateVector i, coordinateVector j]) (iteratedFDeriv ℝ 2 f y) := by
    funext y
    exact part2_eq_hess_L hf i j y
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


/-- `∂_w (y ↦ D^n f(y)(v)) = D^{n+1} f(y)(w, v)` for a `C^∞` function `f`. -/
private lemma fderiv_iter_apply_L {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (v : Fin n → Space) (x w : Space) :
    fderiv ℝ (fun y => iteratedFDeriv ℝ n f y v) x w =
      iteratedFDeriv ℝ (n + 1) f x (Fin.cons w v) := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
    (hf.differentiable_iteratedFDeriv (m := n) (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top n))) x
  rw [fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left]
  simp

private lemma integrableOn_eval_L {n : ℕ} {S : Set ℝ}
    {M : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℝ}
    (hM : IntegrableOn M S) (w : Fin n → Space) : IntegrableOn (fun a => M a w) S :=
  ContinuousLinearMap.integrable_comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) ℝ w) hM

private lemma integral_eval_L {n : ℕ} {S : Set ℝ}
    {M : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℝ}
    (hM : IntegrableOn M S) (w : Fin n → Space) :
    (∫ a in S, M a) w = ∫ a in S, M a w :=
  (ContinuousLinearMap.integral_comp_comm
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) ℝ w) hM).symm

/-- **`PartIII-b:C/rep/5/1/2/4/1/2/4/2/4`**: `Δ ∂_k∂_i∂_j ∫_t^∞ G_a da = -∂_k∂_i∂_j G_t`. -/
theorem tailLapPart : UnforcedLeray.Short.PartIIIb.Concrete.KPH.TailLapPart := by
  intro t ht i j k x
  have hT : ContDiff ℝ ∞ (heatTail t) := (tailIterated t ht).1
  set v : Fin 3 → Space := ![coordinateVector k, coordinateVector i, coordinateVector j] with hv
  have hinner : (fun y' => fderiv ℝ (fun y'' => part2 (heatTail t) i j y'') y'
      (coordinateVector k)) = fun y' => iteratedFDeriv ℝ 3 (heatTail t) y' v := by
    funext y'
    exact fderiv_part2_eq_iter_L hT i j k y'
  rw [hinner]
  have hsum : ∀ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ
      (fun y' => iteratedFDeriv ℝ 3 (heatTail t) y' v) y (coordinateVector l)) x
        (coordinateVector l) =
      iteratedFDeriv ℝ 5 (heatTail t) x
        (Fin.cons (coordinateVector l) (Fin.cons (coordinateVector l) v)) := by
    intro l
    have h1 : (fun y => fderiv ℝ (fun y' => iteratedFDeriv ℝ 3 (heatTail t) y' v) y
        (coordinateVector l)) =
        fun y => iteratedFDeriv ℝ 4 (heatTail t) y (Fin.cons (coordinateVector l) v) := by
      funext y
      exact fderiv_iter_apply_L hT 3 v y (coordinateVector l)
    rw [h1, fderiv_iter_apply_L hT 4 _ x (coordinateVector l)]
  rw [Finset.sum_congr rfl fun l _ => hsum l]
  rw [fderiv_part2_eq_iter_L (contDiff_heatG ht) i j k x]
  have hM5 : IntegrableOn (fun a => iteratedFDeriv ℝ 5 (heatG a) x) (Ioi t) := by
    simp only [heatG_eq_heatKernel]
    exact UnforcedLeray.Kernels.integrableOn_iteratedFDeriv_heatKernel_time 5 ht.le (Or.inr ht)
  have hT5 : ∀ l : Fin 3,
      iteratedFDeriv ℝ 5 (heatTail t) x (Fin.cons (coordinateVector l) (Fin.cons (coordinateVector l) v))
        = ∫ a in Ioi t, iteratedFDeriv ℝ 5 (heatG a) x
            (Fin.cons (coordinateVector l) (Fin.cons (coordinateVector l) v)) := by
    intro l
    rw [(tailIterated t ht).2 5 x]
    exact integral_eval_L hM5 _
  have hsplit : ∑ l : Fin 3, (∫ a in Ioi t, iteratedFDeriv ℝ 5 (heatG a) x
            (Fin.cons (coordinateVector l) (Fin.cons (coordinateVector l) v)))
      = ∫ a in Ioi t, ∑ l : Fin 3, iteratedFDeriv ℝ 5 (heatG a) x
            (Fin.cons (coordinateVector l) (Fin.cons (coordinateVector l) v)) := by
    rw [integral_finsetSum]
    intro l _
    exact integrableOn_eval_L hM5 _
  have hderiv : ∀ a ∈ Ioi t, HasDerivAt (fun a' => iteratedFDeriv ℝ 3 (heatG a') x v)
      (∑ l : Fin 3, iteratedFDeriv ℝ 5 (heatG a) x
        (Fin.cons (coordinateVector l) (Fin.cons (coordinateVector l) v))) a := by
    intro a ha
    exact gaussHeat.2 3 a (ht.trans ha) x v
  have hint : IntegrableOn (fun a => ∑ l : Fin 3, iteratedFDeriv ℝ 5 (heatG a) x
      (Fin.cons (coordinateVector l) (Fin.cons (coordinateVector l) v))) (Ioi t) :=
    integrable_finsetSum _ (fun l _ => integrableOn_eval_L hM5 _)
  have hcont : ContinuousWithinAt (fun a => iteratedFDeriv ℝ 3 (heatG a) x v) (Ici t) t := by
    have h0 : ContinuousOn (fun a => iteratedFDeriv ℝ 3 (heatG a) x) (Ioi 0) := by
      simp only [heatG_eq_heatKernel]
      exact UnforcedLeray.Kernels.continuousOn_iteratedFDeriv_heatKernel 3 x
    have hc : ContinuousOn (fun a => iteratedFDeriv ℝ 3 (heatG a) x v) (Ioi 0) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => Space) ℝ v).continuous.comp_continuousOn h0
    exact (hc.continuousAt (Ioi_mem_nhds ht)).continuousWithinAt
  have hlim : Tendsto (fun a => iteratedFDeriv ℝ 3 (heatG a) x v) atTop (𝓝 0) := by
    have hK : ∀ a : ℝ, 0 < a →
        ‖iteratedFDeriv ℝ 3 (heatG a) x‖ ≤
          UnforcedLeray.Kernels.heatDerivConst 3 * a ^ (-((3 + ((3:ℕ):ℝ)) / 2)) := by
      intro a ha
      have hb := UnforcedLeray.Kernels.norm_iteratedFDeriv_heatKernel_le 3 ha x
      have he : Real.exp (-‖x‖ ^ 2 / (8 * a)) ≤ 1 := by
        apply Real.exp_le_one_iff.2
        apply div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ‖x‖]) (by positivity)
      have hpos : 0 ≤ UnforcedLeray.Kernels.heatDerivConst 3 * a ^ (-((3 + ((3:ℕ):ℝ)) / 2)) := by
        have := UnforcedLeray.Kernels.heatDerivConst_pos 3
        positivity
      simp only [heatG_eq_heatKernel]
      exact le_trans hb (mul_le_of_le_one_right hpos he)
    have hdecay : Tendsto (fun a : ℝ => UnforcedLeray.Kernels.heatDerivConst 3 * a ^ (-((3 + ((3:ℕ):ℝ)) / 2)))
        atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := (3 + ((3:ℕ):ℝ)) / 2) (by positivity)).const_mul
        (UnforcedLeray.Kernels.heatDerivConst 3)
      rwa [mul_zero] at this
    have hbd : ∀ᶠ a in atTop, ‖iteratedFDeriv ℝ 3 (heatG a) x v‖ ≤
        (UnforcedLeray.Kernels.heatDerivConst 3 * a ^ (-((3 + ((3:ℕ):ℝ)) / 2))) * ∏ i, ‖v i‖ := by
      filter_upwards [eventually_gt_atTop 0] with a ha
      calc ‖iteratedFDeriv ℝ 3 (heatG a) x v‖
          ≤ ‖iteratedFDeriv ℝ 3 (heatG a) x‖ * ∏ i, ‖v i‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (hK a ha) (by positivity)
    have hdec2 : Tendsto (fun a : ℝ => (UnforcedLeray.Kernels.heatDerivConst 3 * a ^ (-((3 + ((3:ℕ):ℝ)) / 2))) *
        ∏ i, ‖v i‖) atTop (𝓝 0) := by
      have := hdecay.mul_const (∏ i, ‖v i‖)
      rwa [zero_mul] at this
    exact squeeze_zero_norm' hbd hdec2
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [Finset.sum_congr rfl fun l _ => hT5 l, hsplit, hFTC, zero_sub]

end UnforcedLeray.Short.PartIIIb.Concrete.KPH
