import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.ParamDmuTime

/-!
# Second spatial derivative under the causal integral (helper leaves)

Source `the November 2 reference manuscript` 3611-3621, 4171-4186.  Helper for
`ParamDmu.lean`: `physPd2` of the causal integral is the causal integral of `physPd2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma pdc_clm_eq (T : Space →L[ℝ] Space) :
    T = ∑ i : Fin 3, (EuclideanSpace.proj i : Space →L[ℝ] ℝ).smulRight (T (coordinateVector i)) := by
  ext w : 1
  have hw : w = ∑ i : Fin 3, w i • coordinateVector i := by
    ext j
    simp [coordinateVector, Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum]

lemma pdc_aesm_clm {α : Type*} [MeasurableSpace α] {μ : Measure α} (g : α → Space →L[ℝ] Space)
    (h : ∀ i : Fin 3, AEStronglyMeasurable (fun a => g a (coordinateVector i)) μ) :
    AEStronglyMeasurable g μ := by
  have : g = fun a => ∑ i : Fin 3,
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).smulRight (g a (coordinateVector i)) := by
    funext a; exact pdc_clm_eq (g a)
  rw [this]
  refine Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin 3)) (fun i _ => ?_)
  exact (ContinuousLinearMap.smulRightL ℝ Space Space
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable (h i)

/-- `y ↦ fderiv f y v` has derivative `(fderiv (fderiv f) y).flip v`, bounded by the second
iterated derivative. -/
lemma pdc_fderiv_apply_bound (f : Space → Space) (y : Space) (hf : ContDiffAt ℝ 2 f y) (v : Space) :
    HasFDerivAt (fun y' => fderiv ℝ f y' v) ((fderiv ℝ (fderiv ℝ f) y).flip v) y ∧
    ‖(fderiv ℝ (fderiv ℝ f) y).flip v‖ ≤ ‖iteratedFDeriv ℝ 2 f y‖ * ‖v‖ ∧
    ∀ w : Space, (fderiv ℝ (fderiv ℝ f) y).flip v w = iteratedFDeriv ℝ 2 f y ![w, v] := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) y := hf.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y := h1.differentiableAt (by norm_num)
  have happly : ∀ w : Space, (fderiv ℝ (fderiv ℝ f) y).flip v w = iteratedFDeriv ℝ 2 f y ![w, v] := by
    intro w
    rw [iteratedFDeriv_two_apply]
    simp
  refine ⟨?_, ?_, happly⟩
  · have := (hd.clm_apply (differentiableAt_const v)).hasFDerivAt
    have e : fderiv ℝ (fun y' => fderiv ℝ f y' v) y = (fderiv ℝ (fderiv ℝ f) y).flip v := by
      rw [fderiv_clm_apply hd (differentiableAt_const v)]
      simp
    rw [← e]
    exact this
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
    rw [happly]
    have := (iteratedFDeriv ℝ 2 f y).le_opNorm ![w, v]
    simpa [Fin.prod_univ_two, mul_comm, mul_assoc, mul_left_comm] using this

/-- Second spatial derivative of the causal integral (source 3611-3621, 4171-4186). -/
lemma pdc_second (k : ℝ → Space → ℝ × Space → Space) (τ₀ : ℝ) (y₀ : Space) (ε : ℝ)
    (B : ℝ × Space → ℝ) (hε : 0 < ε) (hB : Integrable B)
    (hdiff : ∀ (e : ℝ × Space) (h : ℝ), 0 < h → ∀ y ∈ Metric.ball y₀ ε,
      ContDiffAt ℝ 2 (fun y' => k h y' e) y ∧ DifferentiableAt ℝ (fun h' => k h' y e) h)
    (hbd : ∀ (e : ℝ × Space), ∀ τ ∈ Metric.ball τ₀ ε, e.1 < τ → ∀ y ∈ Metric.ball y₀ ε,
      ‖k (τ - e.1) y e‖ ≤ B e ∧ ‖fderiv ℝ (fun y' => k (τ - e.1) y' e) y‖ ≤ B e ∧
        ‖iteratedFDeriv ℝ 2 (fun y' => k (τ - e.1) y' e) y‖ ≤ B e)
    (hmeas0 : ∀ (τ : ℝ) (y : Space), AEStronglyMeasurable
      (fun e : ℝ × Space => if e.1 < τ then k (τ - e.1) y e else 0) volume)
    (hmeas2 : ∀ (τ : ℝ) (y : Space), AEStronglyMeasurable
      (fun e : ℝ × Space => if e.1 < τ then fderiv ℝ (fun y' => k (τ - e.1) y' e) y else 0)
      volume)
    (hmeas3 : ∀ (τ : ℝ) (y : Space), AEStronglyMeasurable
      (fun e : ℝ × Space =>
        if e.1 < τ then iteratedFDeriv ℝ 2 (fun y' => k (τ - e.1) y' e) y else 0) volume)
    (j l : Fin 3) :
    physPd2 (fun y => ∫ e : ℝ × Space, if e.1 < τ₀ then k (τ₀ - e.1) y e else 0) j l y₀ =
      ∫ e : ℝ × Space, if e.1 < τ₀ then physPd2 (fun y => k (τ₀ - e.1) y e) j l y₀ else 0 := by
  classical
  have hτ0 : τ₀ ∈ Metric.ball τ₀ ε := Metric.mem_ball_self hε
  have hy0 : y₀ ∈ Metric.ball y₀ ε := Metric.mem_ball_self hε
  have hnorm_cv : ‖(coordinateVector l : Space)‖ = 1 := by simp [coordinateVector]
  set G : Space → Space := fun y => ∫ e : ℝ × Space, if e.1 < τ₀ then k (τ₀ - e.1) y e else 0
    with hG
  have hs1 : ∀ c ∈ Metric.ball y₀ ε, HasFDerivAt G
      (∫ e : ℝ × Space, if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) c else 0) c :=
    fun c hc => pdc_space1 k τ₀ y₀ ε B hε hB hdiff
      (fun e τ hτ hlt y hy => ⟨(hbd e τ hτ hlt y hy).1, (hbd e τ hτ hlt y hy).2.1⟩)
      hmeas0 hmeas2 c hc
  have hF'int : ∀ c ∈ Metric.ball y₀ ε, Integrable
      (fun e : ℝ × Space => if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) c else 0) := by
    intro c hc
    refine Integrable.mono' hB.norm (hmeas2 τ₀ c) (Eventually.of_forall fun e => ?_)
    by_cases h : e.1 < τ₀
    · simp only [h, ↓reduceIte]
      exact ((hbd e τ₀ hτ0 h c hc).2.1).trans (Real.le_norm_self _)
    · simp only [h, ↓reduceIte, norm_zero]
      exact norm_nonneg _
  have hpd : ∀ c ∈ Metric.ball y₀ ε, physPd G l c =
      ∫ e : ℝ × Space, if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) c
        (coordinateVector l) else 0 := by
    intro c hc
    unfold physPd
    rw [(hs1 c hc).fderiv, ContinuousLinearMap.integral_apply (hF'int c hc)]
    congr 1; funext e; split_ifs <;> simp
  let F2 : Space → ℝ × Space → Space := fun y e =>
    if e.1 < τ₀ then fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y (coordinateVector l) else 0
  let F2' : Space → ℝ × Space → Space →L[ℝ] Space := fun y e =>
    if e.1 < τ₀ then (fderiv ℝ (fderiv ℝ (fun y' => k (τ₀ - e.1) y' e)) y).flip
      (coordinateVector l) else 0
  have hF2meas : ∀ y, AEStronglyMeasurable (F2 y) volume := by
    intro y
    have := (hmeas2 τ₀ y).apply_continuousLinearMap (coordinateVector l)
    refine this.congr (Eventually.of_forall fun e => ?_)
    by_cases h : e.1 < τ₀ <;> simp [F2, h]
  have hF2'bound : ∀ e : ℝ × Space, ∀ y ∈ Metric.ball y₀ ε, ‖F2' y e‖ ≤ ‖B e‖ := by
    intro e y hy
    by_cases h : e.1 < τ₀
    · simp only [F2', h, ↓reduceIte]
      have hc := (hdiff e (τ₀ - e.1) (by linarith) y hy).1
      have := (pdc_fderiv_apply_bound _ y hc (coordinateVector l)).2.1
      rw [hnorm_cv, mul_one] at this
      exact this.trans ((hbd e τ₀ hτ0 h y hy).2.2.trans (Real.le_norm_self _))
    · simp only [F2', h, ↓reduceIte, norm_zero]
      exact norm_nonneg _
  have hF2'meas : AEStronglyMeasurable (F2' y₀) volume := by
    refine pdc_aesm_clm _ (fun i => ?_)
    have hm := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) Space
      ![coordinateVector i, coordinateVector l]).continuous.comp_aestronglyMeasurable
      (hmeas3 τ₀ y₀)
    refine hm.congr (Eventually.of_forall fun e => ?_)
    by_cases h : e.1 < τ₀
    · have hc := (hdiff e (τ₀ - e.1) (by linarith) y₀ hy0).1
      simp only [F2', h, ↓reduceIte]
      rw [(pdc_fderiv_apply_bound _ y₀ hc (coordinateVector l)).2.2]
      simp
    · simp [F2', h]
  have hF2int : Integrable (F2 y₀) volume := by
    refine Integrable.mono' hB.norm (hF2meas y₀) (Eventually.of_forall fun e => ?_)
    by_cases h : e.1 < τ₀
    · simp only [F2, h, ↓reduceIte]
      calc ‖fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y₀ (coordinateVector l)‖
          ≤ ‖fderiv ℝ (fun y' => k (τ₀ - e.1) y' e) y₀‖ * ‖(coordinateVector l : Space)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖B e‖ := by
            rw [hnorm_cv, mul_one]
            exact ((hbd e τ₀ hτ0 h y₀ hy0).2.1).trans (Real.le_norm_self _)
    · simp only [F2, h, ↓reduceIte, norm_zero]
      exact norm_nonneg _
  have hH : HasFDerivAt (fun y => ∫ e : ℝ × Space, F2 y e) (∫ e : ℝ × Space, F2' y₀ e) y₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun y e => F2 y e) (F' := F2') (bound := fun e => ‖B e‖)
      (Metric.ball_mem_nhds y₀ hε) (Eventually.of_forall fun y => hF2meas y) hF2int
      hF2'meas ?_ hB.norm ?_
    · exact Eventually.of_forall fun e y hy => hF2'bound e y hy
    · refine Eventually.of_forall fun e y hy => ?_
      by_cases h : e.1 < τ₀
      · simp only [F2, F2', h, ↓reduceIte]
        have hc := (hdiff e (τ₀ - e.1) (by linarith) y hy).1
        exact (pdc_fderiv_apply_bound _ y hc (coordinateVector l)).1
      · simp only [F2, F2', h, ↓reduceIte]
        exact hasFDerivAt_const _ _
  have hHeq : (fun y => physPd G l y) =ᶠ[𝓝 y₀] fun y => ∫ e : ℝ × Space, F2 y e :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds y₀ hε) (fun y hy => hpd y hy)
  have hF2'int : Integrable (F2' y₀) volume :=
    Integrable.mono' hB.norm hF2'meas (Eventually.of_forall fun e => hF2'bound e y₀ hy0)
  unfold physPd2
  have hlhs : physPd (fun y' => physPd G l y') j y₀ =
      fderiv ℝ (fun y' => physPd G l y') y₀ (coordinateVector j) := rfl
  rw [hlhs, hHeq.fderiv_eq, hH.fderiv, ContinuousLinearMap.integral_apply hF2'int]
  congr 1; funext e
  by_cases h : e.1 < τ₀
  · have hc := (hdiff e (τ₀ - e.1) (by linarith) y₀ hy0).1
    simp only [F2', h, ↓reduceIte]
    rw [show physPd (fun y' => physPd (fun y => k (τ₀ - e.1) y e) l y') j y₀ =
      fderiv ℝ (fun y' => fderiv ℝ (fun y => k (τ₀ - e.1) y e) y' (coordinateVector l)) y₀
        (coordinateVector j) from rfl]
    rw [← (pdc_fderiv_apply_bound _ y₀ hc (coordinateVector l)).1.fderiv]
  · simp [F2', h]

end UnforcedLeray.Short.PartIIIb.Concrete

end
