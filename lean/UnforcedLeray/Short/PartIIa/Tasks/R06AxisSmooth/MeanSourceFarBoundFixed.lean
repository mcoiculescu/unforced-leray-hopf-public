import UnforcedLeray.Short.PartIIa.Sub.PartIIa_R06
import UnforcedLeray.Short.PartI.Sub.PartI_T23_2

/-!
# `PartII-a:R06/2`: Fixed-parameter spatial-derivative bound for `meanSourceFar`

Source of record: `the November 2 reference manuscript`, lines 429–435, 453–455,
535–538. Proves `MeanSourceFarBoundFixed` (`Sub/PartII-a_R06.lean`) by differentiating
`meanSourceFar` under the integral sign in `η` and absorbing the exponential decay on `[s/2, s]`
into any negative power of `s` via `exp_neg_le_rpow_any`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set ContDiff
open scoped Topology ENNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI

namespace MeanSourceFarBoundFixedAux

private theorem contDiff_heatKernel1 (a : ℝ) : ContDiff ℝ ∞ (heatKernel1 a) := by
  unfold heatKernel1
  fun_prop

private theorem contDiff_iteratedDeriv (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ∀ k : ℕ, ContDiff ℝ ∞ (iteratedDeriv k φ)
  | 0 => by rw [iteratedDeriv_zero]; exact hφ
  | k + 1 => by
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp (contDiff_iteratedDeriv φ hφ k)).2

private theorem aestronglyMeasurable_parametric_integral_Ioc {a d : ℝ}
    {H : ℝ → ℝ → ℝ} (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Ioc a d ×ˢ univ)) :
    AEStronglyMeasurable (fun t : ℝ => ∫ w : ℝ, H t w) (volume.restrict (Ioc a d)) := by
  let G : ℝ × ℝ → ℝ := (Ioc a d ×ˢ (univ : Set ℝ)).indicator (fun p => H p.1 p.2)
  have hS_meas : MeasurableSet (Ioc a d ×ˢ (univ : Set ℝ)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hG_aem : AEStronglyMeasurable G (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (aestronglyMeasurable_indicator_iff hS_meas).2 (hH.aestronglyMeasurable hS_meas)
  have h_int_aem : AEStronglyMeasurable (fun t : ℝ => ∫ w : ℝ, G (t, w)) volume :=
    hG_aem.integral_prod_right'
  refine h_int_aem.restrict.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  congr 1
  funext w
  have hmem : ((t, w) : ℝ × ℝ) ∈ Ioc a d ×ˢ (univ : Set ℝ) := ⟨ht, mem_univ w⟩
  simp [G, hmem]

private theorem iteratedDeriv_eq_of_hasDerivAt_le (b : ℕ) (g : ℕ → ℝ → ℝ)
    (hd : ∀ k ≤ b, ∀ y : ℝ, HasDerivAt (g k) (g (k + 1) y) y) :
    (∀ k ≤ b, ∀ y : ℝ, iteratedDeriv k (g 0) y = g k y) ∧
      ContDiff ℝ (b : WithTop ℕ∞) (g 0) := by
  have hiter : ∀ k ≤ b, ∀ y : ℝ, iteratedDeriv k (g 0) y = g k y := by
    intro k hk
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      have heq : iteratedDeriv k (g 0) = g k := funext (ih (by omega))
      rw [iteratedDeriv_succ, heq, (hd k (by omega) y).deriv]
  have hcd : ∀ n k : ℕ, n + k ≤ b → ContDiff ℝ (n : WithTop ℕ∞) (g k) := by
    intro n
    induction n with
    | zero =>
      intro k hk
      exact contDiff_zero.2 (continuous_iff_continuousAt.mpr fun y => (hd k (by omega) y).continuousAt)
    | succ n ih =>
      intro k hk
      push_cast
      rw [contDiff_succ_iff_deriv]
      refine ⟨fun y => (hd k (by omega) y).differentiableAt, by simp, ?_⟩
      have hderiv : deriv (g k) = g (k + 1) := funext fun y => (hd k (by omega) y).deriv
      rw [hderiv]
      exact ih (k + 1) (by omega)
  exact ⟨hiter, hcd b 0 (by omega)⟩

/-- Iterated differentiation in `η` up to order `b` under `∫ t in a..d, ∫ w : ℝ, Φ k t w η` for a
family `Φ : ℕ → ℝ → ℝ → ℝ → ℝ` with uniform integrable majorants `dom k` for `k ≤ b + 1`. -/
private theorem iteratedDeriv_intervalIntegral_integral (b : ℕ) {a d : ℝ} (had : a ≤ d)
    (Φ : ℕ → ℝ → ℝ → ℝ → ℝ) (dom : ℕ → ℝ → ℝ)
    (hdom_int : ∀ k ≤ b + 1, Integrable (dom k) volume)
    (hΦ_cont : ∀ k ≤ b + 1, ∀ η : ℝ,
      ContinuousOn (fun p : ℝ × ℝ => Φ k p.1 p.2 η) (Ioc a d ×ˢ univ))
    (hΦ_deriv : ∀ k ≤ b, ∀ t ∈ Ioc a d, ∀ w η : ℝ,
      HasDerivAt (Φ k t w) (Φ (k + 1) t w η) η)
    (hΦ_bd : ∀ k ≤ b + 1, ∀ t ∈ Ioc a d, ∀ w η : ℝ, |Φ k t w η| ≤ dom k w) :
    (∀ k ≤ b, ∀ η : ℝ,
      iteratedDeriv k (fun η' => ∫ t in a..d, ∫ w : ℝ, Φ 0 t w η') η =
        ∫ t in a..d, ∫ w : ℝ, Φ k t w η) ∧
    ContDiff ℝ (b : WithTop ℕ∞) (fun η' => ∫ t in a..d, ∫ w : ℝ, Φ 0 t w η') ∧
    (∀ k ≤ b + 1, ∀ η₀ : ℝ, IntervalIntegrable (fun t => ∫ w : ℝ, Φ k t w η₀) volume a d) := by
  let g : ℕ → ℝ → ℝ := fun k η => ∫ t in a..d, ∫ w : ℝ, Φ k t w η
  have hI_int_all : ∀ k ≤ b + 1, ∀ η₀ : ℝ,
      IntervalIntegrable (fun t => ∫ w : ℝ, Φ k t w η₀) volume a d := by
    intro k hk1 η₀
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le had]
    have h_const : IntegrableOn (fun _ : ℝ => ∫ w : ℝ, dom k w) (Ioc a d) volume :=
      integrableOn_const measure_Ioc_lt_top.ne
    refine h_const.mono' (aestronglyMeasurable_parametric_integral_Ioc (hΦ_cont k hk1 η₀)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    refine norm_integral_le_of_norm_le (hdom_int k hk1) (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs]
    exact hΦ_bd k hk1 t ht w η₀
  have hI_deriv : ∀ k ≤ b, ∀ t ∈ Ioc a d, ∀ η₀ : ℝ,
      HasDerivAt (fun η => ∫ w : ℝ, Φ k t w η) (∫ w : ℝ, Φ (k + 1) t w η₀) η₀ := by
    intro k hk t ht η₀
    have hk1 : k ≤ b + 1 := by omega
    have hk2 : k + 1 ≤ b + 1 := by omega
    have hF_meas : ∀ η : ℝ, AEStronglyMeasurable (fun w => Φ k t w η) volume := by
      intro η
      have hc : Continuous (fun w : ℝ => Φ k t w η) :=
        (hΦ_cont k hk1 η).comp_continuous (continuous_const.prodMk continuous_id)
          (fun w => ⟨ht, mem_univ w⟩)
      exact hc.aestronglyMeasurable
    have hF_int : Integrable (fun w => Φ k t w η₀) volume := by
      refine (hdom_int k hk1).mono' (hF_meas η₀) (Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs]
      exact hΦ_bd k hk1 t ht w η₀
    have hF'_meas : AEStronglyMeasurable (fun w => Φ (k + 1) t w η₀) volume := by
      have hc : Continuous (fun w : ℝ => Φ (k + 1) t w η₀) :=
        (hΦ_cont (k + 1) hk2 η₀).comp_continuous (continuous_const.prodMk continuous_id)
          (fun w => ⟨ht, mem_univ w⟩)
      exact hc.aestronglyMeasurable
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := univ) (bound := dom (k + 1)) univ_mem
      (Eventually.of_forall hF_meas) hF_int hF'_meas
      (Eventually.of_forall fun w => fun η _ => ?_)
      (hdom_int (k + 1) hk2)
      (Eventually.of_forall fun w => fun η _ => hΦ_deriv k hk t ht w η)).2
    rw [Real.norm_eq_abs]
    exact hΦ_bd (k + 1) hk2 t ht w η
  have hg_deriv : ∀ k ≤ b, ∀ η₀ : ℝ, HasDerivAt (g k) (g (k + 1) η₀) η₀ := by
    intro k hk η₀
    have hk1 : k ≤ b + 1 := by omega
    have hk2 : k + 1 ≤ b + 1 := by omega
    set B_k1 : ℝ := ∫ w : ℝ, dom (k + 1) w
    have hI_meas : ∀ η : ℝ,
        AEStronglyMeasurable (fun t => ∫ w : ℝ, Φ k t w η) (volume.restrict (uIoc a d)) := by
      intro η
      rw [uIoc_of_le had]
      exact aestronglyMeasurable_parametric_integral_Ioc (hΦ_cont k hk1 η)
    have hI_int : IntervalIntegrable (fun t => ∫ w : ℝ, Φ k t w η₀) volume a d :=
      hI_int_all k hk1 η₀
    have hI'_meas : AEStronglyMeasurable (fun t => ∫ w : ℝ, Φ (k + 1) t w η₀)
        (volume.restrict (uIoc a d)) := by
      rw [uIoc_of_le had]
      exact aestronglyMeasurable_parametric_integral_Ioc (hΦ_cont (k + 1) hk2 η₀)
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun η t => ∫ w : ℝ, Φ k t w η)
      (F' := fun η t => ∫ w : ℝ, Φ (k + 1) t w η)
      (s := univ) (bound := fun _ => B_k1) univ_mem
      (Eventually.of_forall hI_meas) hI_int hI'_meas
      (Eventually.of_forall fun t ht => fun η _ => ?_)
      intervalIntegrable_const
      (Eventually.of_forall fun t ht => fun η _ => ?_)).2
    · rw [uIoc_of_le had] at ht
      exact norm_integral_le_of_norm_le (hdom_int (k + 1) hk2) (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        exact hΦ_bd (k + 1) hk2 t ht w η)
    · rw [uIoc_of_le had] at ht
      exact hI_deriv k hk t ht η
  have hmain := iteratedDeriv_eq_of_hasDerivAt_le b g hg_deriv
  exact ⟨hmain.1, hmain.2, hI_int_all⟩

private theorem integrable_heatKernel1_one : Integrable (heatKernel1 1) volume := by
  have h0 := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := 0) (by norm_num)
  have h1 : Integrable (fun z : ℝ => Real.exp (-(1 / 4) * z ^ 2)) volume := by
    simpa using h0
  refine (h1.const_mul (Real.sqrt (4 * Real.pi * 1))⁻¹).congr (ae_of_all _ fun z => ?_)
  dsimp [heatKernel1]
  rw [show -(z ^ 2) / (4 * 1) = -(1 / 4) * z ^ 2 by ring]

private theorem iteratedDeriv_meanSourceFar (b : ℕ) {ν c : ℝ} (_hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c)
    (B_k : ℕ → ℝ) (_hB_nn : ∀ k ≤ b + 1, 0 ≤ B_k k)
    (hB : ∀ k ≤ b + 1, ∀ t : ℝ, 0 < t → ∀ y : ℝ, |iteratedDeriv k (meanStress tr t) y| ≤ B_k k)
    {s : ℝ} (hs : 1 ≤ s) :
    (∀ η : ℝ,
      iteratedDeriv b (meanSourceFar tr s) η =
        ∫ t in (s / 2)..s, ∫ z : ℝ,
          heatKernel1 1 z *
            iteratedDeriv b (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z)) ∧
    ContDiff ℝ (b : WithTop ℕ∞) (meanSourceFar tr s) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hs2 : s / 2 ≤ s := by linarith
  let Φ : ℕ → ℝ → ℝ → ℝ → ℝ := fun k t z η =>
    heatKernel1 1 z * iteratedDeriv k (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z)
  let dom : ℕ → ℝ → ℝ := fun k z => B_k k * heatKernel1 1 z
  have hdom_int : ∀ k ≤ b + 1, Integrable (dom k) volume :=
    fun k _ => integrable_heatKernel1_one.const_mul (B_k k)
  have hΦ_cont : ∀ k ≤ b + 1, ∀ η : ℝ,
      ContinuousOn (fun p : ℝ × ℝ => Φ k p.1 p.2 η) (Ioc (s / 2) s ×ˢ univ) := by
    intro k _ η
    have hms_k : ContDiffOn ℝ ∞
        (fun x : ℝ × ℝ => iteratedDeriv k (meanStress tr x.1) x.2) (Ioi 0 ×ˢ univ) :=
      UnforcedLeray.Short.PartIIa.etaDerivIter_contDiffOn (meanStress tr)
        (PartI_T23.contDiffOn_meanStress hc tr) k
    have hmap : Continuous (fun p : ℝ × ℝ =>
        ((p.1, η - Real.sqrt (ν * (s - p.1)) * p.2) : ℝ × ℝ)) :=
      continuous_fst.prodMk
        (continuous_const.sub
          ((Real.continuous_sqrt.comp
            (continuous_const.mul (continuous_const.sub continuous_fst))).mul continuous_snd))
    have hcomp : ContinuousOn
        (fun p : ℝ × ℝ => iteratedDeriv k (meanStress tr p.1)
          (η - Real.sqrt (ν * (s - p.1)) * p.2))
        (Ioc (s / 2) s ×ˢ univ) :=
      hms_k.continuousOn.comp hmap.continuousOn
        (fun p hp => ⟨lt_of_lt_of_le (by positivity : 0 < s / 2) hp.1.1.le, mem_univ _⟩)
    exact ((contDiff_heatKernel1 1).continuous.comp continuous_snd).continuousOn.mul hcomp
  have hΦ_deriv : ∀ k ≤ b, ∀ t ∈ Ioc (s / 2) s, ∀ z η : ℝ,
      HasDerivAt (Φ k t z) (Φ (k + 1) t z η) η := by
    intro k _ t ht z η
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < s / 2) ht.1.le
    have hms_sm : ContDiff ℝ ∞ (meanStress tr t) := by
      have hcomp : ContDiffOn ℝ ∞
          ((fun x : ℝ × ℝ => meanStress tr x.1 x.2) ∘ (fun y : ℝ => ((t, y) : ℝ × ℝ))) univ :=
        (PartI_T23.contDiffOn_meanStress hc tr).comp
          (contDiffOn_univ.2 (contDiff_const.prodMk contDiff_id))
          (fun y _ => ⟨ht0, mem_univ y⟩)
      exact contDiffOn_univ.1 hcomp
    have hd : DifferentiableAt ℝ (iteratedDeriv k (meanStress tr t))
        (η - Real.sqrt (ν * (s - t)) * z) :=
      (contDiff_iteratedDeriv _ hms_sm k).differentiable (by simp) _
    have h1 := hd.hasDerivAt
    rw [← iteratedDeriv_succ] at h1
    have hsub : HasDerivAt (fun η' : ℝ => η' - Real.sqrt (ν * (s - t)) * z) 1 η :=
      (hasDerivAt_id' η).sub_const _
    have hcomp := (h1.comp η hsub).const_mul (heatKernel1 1 z)
    refine hcomp.congr_deriv ?_
    dsimp [Φ]
    ring
  have hΦ_bd : ∀ k ≤ b + 1, ∀ t ∈ Ioc (s / 2) s, ∀ z η : ℝ, |Φ k t z η| ≤ dom k z := by
    intro k hk t ht z η
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < s / 2) ht.1.le
    have hK1_nn : 0 ≤ heatKernel1 1 z := by unfold heatKernel1; positivity
    dsimp [Φ, dom]
    rw [abs_mul, abs_of_nonneg hK1_nn, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB k hk t ht0 _) hK1_nn
  have hmain := iteratedDeriv_intervalIntegral_integral b hs2 Φ dom hdom_int hΦ_cont hΦ_deriv hΦ_bd
  have h0 : (fun η' => ∫ t in (s / 2)..s, ∫ z : ℝ, Φ 0 t z η') = meanSourceFar tr s := by
    funext η'
    rfl
  rw [h0] at hmain
  exact ⟨hmain.1 b le_rfl, hmain.2.1⟩

end MeanSourceFarBoundFixedAux

/-- **Main theorem (`PartII-a:R06/2`)**: fixed-parameter spatial-derivative bound for the far-time
source Duhamel integral `meanSourceFar`. -/
theorem meanSourceFarBoundFixed : MeanSourceFarBoundFixed := by
  intro ν c hν _hν1 hc1 tr _htr hDecay N b
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  choose C_k κ_k hC_k hκ_k hbd_k using hDecay
  set α : ℝ := (-(b : ℝ) - 2 * N - 3) / 2
  obtain ⟨K_exp, hK_exp, h_exp⟩ := exp_neg_le_rpow_any (κ_k b / 2) (half_pos (hκ_k b)) (α - 1)
  refine ⟨C_k b * K_exp, fun s hs => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hs2_le_s : s / 2 ≤ s := by linarith
  have hB_nn : ∀ k ≤ b + 1, 0 ≤ C_k k := fun k _ => (hC_k k).le
  have hB_bd : ∀ k ≤ b + 1, ∀ t : ℝ, 0 < t → ∀ y : ℝ,
      |iteratedDeriv k (meanStress tr t) y| ≤ C_k k := by
    intro k _ t ht y
    have h := hbd_k k t ht y
    have hexp1 : Real.exp (-(κ_k k * t)) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.2
      have : 0 ≤ κ_k k * t := mul_nonneg (hκ_k k).le ht.le
      linarith
    exact h.trans (mul_le_of_le_one_right (hC_k k).le hexp1)
  obtain ⟨hD_far_deriv, hD_far_cd⟩ :=
    MeanSourceFarBoundFixedAux.iteratedDeriv_meanSourceFar b hν hc0 tr C_k hB_nn hB_bd hs
  refine ⟨hD_far_cd, fun η => ?_⟩
  rw [hD_far_deriv η, intervalIntegral.integral_of_le hs2_le_s, ← Real.norm_eq_abs]
  set E_b : ℝ := C_k b * Real.exp (-((κ_k b / 2) * s))
  have hEb_nn : 0 ≤ E_b := by dsimp [E_b]; have := hC_k b; positivity
  have hpt_far : ∀ t ∈ Ioc (s / 2) s,
      ‖∫ z : ℝ,
        heatKernel1 1 z * iteratedDeriv b (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z)‖ ≤
        E_b := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < s / 2) ht.1.le
    have hdom_z : Integrable (fun z : ℝ => E_b * heatKernel1 1 z) volume :=
      MeanSourceFarBoundFixedAux.integrable_heatKernel1_one.const_mul E_b
    have hpt_z : ∀ z : ℝ,
        ‖heatKernel1 1 z *
          iteratedDeriv b (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z)‖ ≤
          E_b * heatKernel1 1 z := by
      intro z
      have hK1_nn : 0 ≤ heatKernel1 1 z := by unfold heatKernel1; positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK1_nn, mul_comm]
      have h1 := hbd_k b t ht0 (η - Real.sqrt (ν * (s - t)) * z)
      have hexp_le : Real.exp (-(κ_k b * t)) ≤ Real.exp (-((κ_k b / 2) * s)) := by
        apply Real.exp_le_exp.2
        have ht1 := ht.1
        have hκb := hκ_k b
        nlinarith
      exact mul_le_mul_of_nonneg_right
        (h1.trans (mul_le_mul_of_nonneg_left hexp_le (hC_k b).le)) hK1_nn
    calc ‖∫ z : ℝ,
          heatKernel1 1 z * iteratedDeriv b (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z)‖
        ≤ ∫ z : ℝ, E_b * heatKernel1 1 z :=
          norm_integral_le_of_norm_le hdom_z (Eventually.of_forall hpt_z)
      _ = E_b * ∫ z : ℝ, heatKernel1 1 z := integral_const_mul _ _
      _ = E_b := by rw [PartI_T23.integral_heatKernel1_eq_one one_pos, mul_one]
  have hint_bd := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Ioc (s / 2) s) measure_Ioc_lt_top hpt_far
  rw [Real.volume_real_Ioc_of_le hs2_le_s] at hint_bd
  have hs_len : s - s / 2 ≤ s := by linarith
  have hexp_abs := h_exp s hs
  have hrpow_mul : s ^ (α - 1) * s = s ^ α := by
    calc s ^ (α - 1) * s = s ^ (α - 1) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = s ^ (α - 1 + 1) := (Real.rpow_add hs0 (α - 1) 1).symm
      _ = s ^ α := by ring_nf
  calc ‖∫ t in Ioc (s / 2) s, ∫ z : ℝ,
        heatKernel1 1 z * iteratedDeriv b (meanStress tr t) (η - Real.sqrt (ν * (s - t)) * z)‖
      ≤ E_b * (s - s / 2) := hint_bd
    _ ≤ E_b * s := mul_le_mul_of_nonneg_left hs_len hEb_nn
    _ = C_k b * Real.exp (-((κ_k b / 2) * s)) * s := rfl
    _ ≤ C_k b * (K_exp * s ^ (α - 1)) * s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp_abs (hC_k b).le) hs0.le
    _ = (C_k b * K_exp) * (s ^ (α - 1) * s) := by ring
    _ = (C_k b * K_exp) * s ^ α := by rw [hrpow_mul]

end UnforcedLeray.Short.PartIIa
