import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.ParamDmuSpace

/-!
# `D_{μ'}` under a causal parametric integral

Source `the November 2 reference manuscript` 3611-3621, 4171-4186.  Assembly of the
time part (`pdc_time`), the first spatial derivative (`pdc_space1`) and the second spatial
derivative (`pdc_second`) into `ParamDmuCausal`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma pdc_physPd2_bound (f : Space → Space) (y : Space) (hf : ContDiffAt ℝ 2 f y) (j l : Fin 3)
    (hnorm : ∀ i : Fin 3, ‖(coordinateVector i : Space)‖ = 1) :
    physPd2 f j l y = iteratedFDeriv ℝ 2 f y ![coordinateVector j, coordinateVector l] ∧
      ‖physPd2 f j l y‖ ≤ ‖iteratedFDeriv ℝ 2 f y‖ := by
  have h := pdc_fderiv_apply_bound f y hf (coordinateVector l)
  have e : physPd2 f j l y = (fderiv ℝ (fderiv ℝ f) y).flip (coordinateVector l)
      (coordinateVector j) := by
    show fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector l)) y (coordinateVector j) = _
    rw [h.1.fderiv]
  have e2 := h.2.2 (coordinateVector j)
  refine ⟨e.trans e2, ?_⟩
  rw [e]
  calc _ ≤ ‖(fderiv ℝ (fderiv ℝ f) y).flip (coordinateVector l)‖ * ‖(coordinateVector j : Space)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖iteratedFDeriv ℝ 2 f y‖ := by
        have := h.2.1
        rw [hnorm l] at this
        rw [hnorm j]
        linarith

theorem paramDmuCausal : ParamDmuCausal := by
  classical
  intro ν μ' k τ₀ y₀ ε B hε hB hdiff hlim hbd hm0 hm1 hm2 hm3
  have hy0 : y₀ ∈ Metric.ball y₀ ε := Metric.mem_ball_self hε
  have hτ0 : τ₀ ∈ Metric.ball τ₀ ε := Metric.mem_ball_self hε
  have hnorm : ∀ i : Fin 3, ‖(coordinateVector i : Space)‖ = 1 := by
    intro i; simp [coordinateVector]
  have hT := pdc_time k τ₀ y₀ ε B hε hB hdiff hlim
    (fun e τ hτ hlt y hy => ⟨(hbd e τ hτ hlt y hy).1, (hbd e τ hτ hlt y hy).2.1⟩) hm0 hm1
  have hS := pdc_space1 k τ₀ y₀ ε B hε hB hdiff
    (fun e τ hτ hlt y hy => ⟨(hbd e τ hτ hlt y hy).1, (hbd e τ hτ hlt y hy).2.2.1⟩) hm0 hm2
    y₀ hy0
  have hL : ∀ j : Fin 3, physPd2 (fun y => ∫ e : ℝ × Space, if e.1 < τ₀ then k (τ₀ - e.1) y e
      else 0) j j y₀ = ∫ e : ℝ × Space,
        if e.1 < τ₀ then physPd2 (fun y => k (τ₀ - e.1) y e) j j y₀ else 0 :=
    fun j => pdc_second k τ₀ y₀ ε B hε hB hdiff
      (fun e τ hτ hlt y hy => ⟨(hbd e τ hτ hlt y hy).1, (hbd e τ hτ hlt y hy).2.2.1,
        (hbd e τ hτ hlt y hy).2.2.2⟩) hm0 hm2 hm3 j j
  -- integrands
  have ha : Integrable (fun e : ℝ × Space =>
      if e.1 < τ₀ then deriv (fun h => k h y₀ e) (τ₀ - e.1) else 0) := by
    refine Integrable.mono' hB.norm (hm1 τ₀ y₀) (Eventually.of_forall fun e => ?_)
    by_cases h : e.1 < τ₀
    · simp only [h, ↓reduceIte]
      exact (hbd e τ₀ hτ0 h y₀ hy0).2.1.trans (Real.le_norm_self _)
    · simp only [h, ↓reduceIte, norm_zero]; exact norm_nonneg _
  have hb : Integrable (fun e : ℝ × Space =>
      if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y₀ y₀ else 0) := by
    have hmeas := (hm2 τ₀ y₀).apply_continuousLinearMap y₀
    have hmeas' : AEStronglyMeasurable (fun e : ℝ × Space =>
        if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y₀ y₀ else 0) volume :=
      hmeas.congr (Eventually.of_forall fun e => by by_cases h : e.1 < τ₀ <;> simp [h])
    refine Integrable.mono' (hB.norm.mul_const ‖y₀‖) hmeas' (Eventually.of_forall fun e => ?_)
    by_cases h : e.1 < τ₀
    · simp only [h, ↓reduceIte]
      calc _ ≤ ‖fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y₀‖ * ‖y₀‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖B e‖ * ‖y₀‖ :=
            mul_le_mul_of_nonneg_right
              ((hbd e τ₀ hτ0 h y₀ hy0).2.2.1.trans (Real.le_norm_self _)) (norm_nonneg _)
    · simp only [h, ↓reduceIte, norm_zero]; positivity
  have hc : ∀ j : Fin 3, Integrable (fun e : ℝ × Space =>
      if e.1 < τ₀ then physPd2 (fun y => k (τ₀ - e.1) y e) j j y₀ else 0) := by
    intro j
    have hm := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) Space
      ![coordinateVector j, coordinateVector j]).continuous.comp_aestronglyMeasurable
      (hm3 τ₀ y₀)
    have hm' : AEStronglyMeasurable (fun e : ℝ × Space =>
        if e.1 < τ₀ then physPd2 (fun y => k (τ₀ - e.1) y e) j j y₀ else 0) volume := by
      refine hm.congr (Eventually.of_forall fun e => ?_)
      by_cases h : e.1 < τ₀
      · have hcd := (hdiff e (τ₀ - e.1) (by linarith) y₀ hy0).1
        simp only [h, ↓reduceIte]
        exact ((pdc_physPd2_bound _ y₀ hcd j j hnorm).1).symm
      · simp [h]
    refine Integrable.mono' hB.norm hm' (Eventually.of_forall fun e => ?_)
    by_cases h : e.1 < τ₀
    · have hcd := (hdiff e (τ₀ - e.1) (by linarith) y₀ hy0).1
      simp only [h, ↓reduceIte]
      exact ((pdc_physPd2_bound _ y₀ hcd j j hnorm).2).trans
        ((hbd e τ₀ hτ0 h y₀ hy0).2.2.2.trans (Real.le_norm_self _))
    · simp only [h, ↓reduceIte, norm_zero]; exact norm_nonneg _
  have hd : Integrable (fun e : ℝ × Space =>
      if e.1 < τ₀ then k (τ₀ - e.1) y₀ e else 0) := by
    refine Integrable.mono' hB.norm (hm0 τ₀ y₀) (Eventually.of_forall fun e => ?_)
    by_cases h : e.1 < τ₀
    · simp only [h, ↓reduceIte]
      exact (hbd e τ₀ hτ0 h y₀ hy0).1.trans (Real.le_norm_self _)
    · simp only [h, ↓reduceIte, norm_zero]; exact norm_nonneg _
  have hFint : Integrable (fun e : ℝ × Space =>
      if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y₀ else 0) := by
    refine Integrable.mono' hB.norm (hm2 τ₀ y₀) (Eventually.of_forall fun e => ?_)
    by_cases h : e.1 < τ₀
    · simp only [h, ↓reduceIte]
      exact (hbd e τ₀ hτ0 h y₀ hy0).2.2.1.trans (Real.le_norm_self _)
    · simp only [h, ↓reduceIte, norm_zero]; exact norm_nonneg _
  have hcs : Integrable (fun e : ℝ × Space => ∑ j : Fin 3,
      if e.1 < τ₀ then physPd2 (fun y => k (τ₀ - e.1) y e) j j y₀ else 0) :=
    integrable_finset_sum _ (fun j _ => hc j)
  -- right-hand side
  have hrhs : (∫ e : ℝ × Space, if e.1 < τ₀ then
      physDmu ν μ' (fun h y => k h y e) (τ₀ - e.1) y₀ else 0) =
      (∫ e : ℝ × Space, if e.1 < τ₀ then deriv (fun h => k h y₀ e) (τ₀ - e.1) else 0) -
      (1 / 2 : ℝ) • (∫ e : ℝ × Space,
        if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y₀ y₀ else 0) -
      ν • (∫ e : ℝ × Space, ∑ j : Fin 3,
        if e.1 < τ₀ then physPd2 (fun y => k (τ₀ - e.1) y e) j j y₀ else 0) +
      (μ' - 1 / 2) • (∫ e : ℝ × Space, if e.1 < τ₀ then k (τ₀ - e.1) y₀ e else 0) := by
    have hint : (fun e : ℝ × Space => if e.1 < τ₀ then
        physDmu ν μ' (fun h y => k h y e) (τ₀ - e.1) y₀ else 0) = fun e =>
        ((if e.1 < τ₀ then deriv (fun h => k h y₀ e) (τ₀ - e.1) else 0) -
          (1 / 2 : ℝ) • (if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y₀ y₀ else 0)) -
          ν • (∑ j : Fin 3, if e.1 < τ₀ then physPd2 (fun y => k (τ₀ - e.1) y e) j j y₀ else 0) +
          (μ' - 1 / 2) • (if e.1 < τ₀ then k (τ₀ - e.1) y₀ e else 0) := by
      funext e
      by_cases h : e.1 < τ₀
      · simp [h, physDmu, physLap]
      · simp [h]
    set A : ℝ × Space → Space := fun e => if e.1 < τ₀ then deriv (fun h => k h y₀ e) (τ₀ - e.1)
      else 0 with hA
    set Bb : ℝ × Space → Space := fun e =>
      if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y₀ y₀ else 0 with hBb
    set C : ℝ × Space → Space := fun e => ∑ j : Fin 3,
      if e.1 < τ₀ then physPd2 (fun y => k (τ₀ - e.1) y e) j j y₀ else 0 with hC
    set D : ℝ × Space → Space := fun e => if e.1 < τ₀ then k (τ₀ - e.1) y₀ e else 0 with hD
    have i1 : Integrable (fun e => (1 / 2 : ℝ) • Bb e) := hb.smul (1 / 2 : ℝ)
    have i2 : Integrable (fun e => ν • C e) := hcs.smul ν
    have i3 : Integrable (fun e => (μ' - 1 / 2) • D e) := hd.smul (μ' - 1 / 2)
    have i4 : Integrable (fun e => A e - (1 / 2 : ℝ) • Bb e) := ha.sub i1
    have i5 : Integrable (fun e => (A e - (1 / 2 : ℝ) • Bb e) - ν • C e) := i4.sub i2
    rw [hint]
    rw [integral_add i5 i3, integral_sub i4 i2, integral_sub ha i1,
      integral_smul, integral_smul, integral_smul]
  rw [hrhs]
  simp only [physDmu]
  rw [hT.deriv, hS.fderiv, ContinuousLinearMap.integral_apply hFint, physLap]
  have hlap : (∑ j : Fin 3, physPd2 (fun y => ∫ e : ℝ × Space,
      if e.1 < τ₀ then k (τ₀ - e.1) y e else 0) j j y₀) = ∫ e : ℝ × Space, ∑ j : Fin 3,
        if e.1 < τ₀ then physPd2 (fun y => k (τ₀ - e.1) y e) j j y₀ else 0 := by
    rw [integral_finset_sum _ (fun j _ => hc j)]
    exact Finset.sum_congr rfl (fun j _ => hL j)
  rw [hlap]
  have hfb : (∫ x : ℝ × Space, (if x.1 < τ₀ then
      fderiv ℝ (fun y' => k (τ₀ - x.1) y' x) y₀ else 0) y₀) = ∫ e : ℝ × Space,
      if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y₀ y₀ else 0 := by
    congr 1; funext e
    by_cases h : e.1 < τ₀ <;> simp [h]
  rw [hfb]

end UnforcedLeray.Short.PartIIIb.Concrete

end
