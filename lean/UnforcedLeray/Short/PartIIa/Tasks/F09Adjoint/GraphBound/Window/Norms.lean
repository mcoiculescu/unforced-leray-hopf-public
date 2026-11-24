import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Chart.Rev

/-!


Proves `AdjointWindowNorms` of `Sub/«PartII-a_F09_3_1»`.  Source of record:
`the November 2 reference manuscript`,
lines 1431-1441 reversed (`θ = 1 - e^{-t}`, `x = e^{-t/2} y`).  The structure is that of
`windowNorms` (`Tasks/F03bWindowNorms.lean`), with the chart `revChart` of
`Chart/Rev.lean` (Jacobian `e^{-5t/2}`) and the force weight `e^{t}` of `adjWindowForce`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.Short.PartIIa.Rep UnforcedLeray.B0424

variable {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)]

theorem rn_comp_norm_le (a b M : ℝ) (μ : ℂ) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖(a : ℂ) - (1 + (starRingEnd ℂ) μ) * (b : ℂ)‖ₑ ≤ ENNReal.ofReal (2 * M * (1 + ‖μ‖)) := by
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have ha' : ‖(a : ℂ)‖ ≤ M := by rwa [Complex.norm_real]
  have hb' : ‖(b : ℂ)‖ ≤ M := by rwa [Complex.norm_real]
  have hM : 0 ≤ M := (norm_nonneg _).trans ha
  have hc : ‖(1 : ℂ) + (starRingEnd ℂ) μ‖ ≤ 1 + ‖μ‖ := by
    refine (norm_add_le _ _).trans ?_
    simp
  calc ‖(a : ℂ) - (1 + (starRingEnd ℂ) μ) * (b : ℂ)‖
      ≤ ‖(a : ℂ)‖ + ‖(1 : ℂ) + (starRingEnd ℂ) μ‖ * ‖(b : ℂ)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ M + (1 + ‖μ‖) * M := by gcongr
    _ ≤ 2 * M * (1 + ‖μ‖) := by nlinarith [norm_nonneg μ]

/-! ### Pointwise bounds -/

theorem rn_force_pointwise {χ : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hMχ : ∀ t, ‖χ t‖ ≤ M)
    (hMd : ∀ t, ‖deriv χ t‖ ≤ M) (hχ : WindowCutoff χ) {q : ℝ} (hq : 0 < q) {C : ℝ≥0∞}
    (hC : ∀ x y : ℝ≥0∞, (x + y) ^ q ≤ C * (x ^ q + y ^ q)) (μ : ℂ) (τ₀ : ℝ)
    (W Fr : ℝ × Space → CVec3) (c : Fin 3) (p : ℝ × Space) :
    ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) *
        ‖adjWindowForce μ χ τ₀ W Fr c (revChart p)‖ₑ ^ q ≤
      (Ioo (-2 : ℝ) 2).indicator
          (fun t => ENNReal.ofReal (Real.exp ((q - 5 / 2) * t)) * C) p.1 *
        (ENNReal.ofReal (2 * M * (1 + ‖μ‖)) ^ q * ‖W (τ₀ - p.1, p.2)‖ₑ ^ q +
          ENNReal.ofReal (2 * M) ^ q * ‖Fr (τ₀ - p.1, p.2)‖ₑ ^ q) := by
  by_cases ht : p.1 ∈ Ioo (-2 : ℝ) 2
  · rw [Set.indicator_of_mem ht, rev_windowForce_chart, enorm_mul, wn_enorm_real,
      abs_of_pos (Real.exp_pos _), ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    have hZ : ‖(((deriv χ p.1 : ℝ) : ℂ) - (1 + (starRingEnd ℂ) μ) * ((χ p.1 : ℝ) : ℂ)) *
          W (τ₀ - p.1, p.2) c + ((χ p.1 : ℝ) : ℂ) * Fr (τ₀ - p.1, p.2) c‖ₑ ≤
        ENNReal.ofReal (2 * M * (1 + ‖μ‖)) * ‖W (τ₀ - p.1, p.2)‖ₑ +
          ENNReal.ofReal (2 * M) * ‖Fr (τ₀ - p.1, p.2)‖ₑ := by
      refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [enorm_mul]
        exact mul_le_mul' (rn_comp_norm_le _ _ M μ (hMd p.1) (hMχ p.1))
          (PiLp.enorm_apply_le _ _)
      · rw [enorm_mul]
        exact mul_le_mul' (wn_enorm_real_le _ (2 * M) ((hMχ p.1).trans (by linarith)))
          (PiLp.enorm_apply_le _ _)
    have hZpow := (ENNReal.rpow_le_rpow hZ hq.le).trans (hC _ _)
    calc _ ≤ ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) * (ENNReal.ofReal (Real.exp p.1) ^ q *
            (C * ((ENNReal.ofReal (2 * M * (1 + ‖μ‖)) * ‖W (τ₀ - p.1, p.2)‖ₑ) ^ q +
              (ENNReal.ofReal (2 * M) * ‖Fr (τ₀ - p.1, p.2)‖ₑ) ^ q))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hZpow)
      _ = (ENNReal.ofReal (Real.exp ((q - 5 / 2) * p.1)) * C) *
          (ENNReal.ofReal (2 * M * (1 + ‖μ‖)) ^ q * ‖W (τ₀ - p.1, p.2)‖ₑ ^ q +
            ENNReal.ofReal (2 * M) ^ q * ‖Fr (τ₀ - p.1, p.2)‖ₑ ^ q) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
            wn_ofReal_exp_rpow _ _ hq.le,
            ← wn_ofReal_exp_mul (-(5 * p.1 / 2)) (p.1 * q) ((q - 5 / 2) * p.1) (by ring)]
          ring
  · obtain ⟨h0, hd0⟩ := wn_cutoff_zero hχ ht
    rw [Set.indicator_of_notMem ht, rev_windowForce_chart, h0, hd0]
    simp [ENNReal.zero_rpow_of_pos hq]

theorem rn_field_pointwise {χ : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hMχ : ∀ t, ‖χ t‖ ≤ M)
    (hχ : WindowCutoff χ) {q : ℝ} (hq : 0 < q) (τ₀ : ℝ) (W : ℝ × Space → CVec3) (c : Fin 3)
    (p : ℝ × Space) :
    ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) * ‖adjWindowField χ τ₀ W c (revChart p)‖ₑ ^ q ≤
      (Ioo (-2 : ℝ) 2).indicator (fun t => ENNReal.ofReal (Real.exp (-(5 * t / 2)))) p.1 *
        (ENNReal.ofReal M ^ q * ‖W (τ₀ - p.1, p.2)‖ₑ ^ q) := by
  by_cases ht : p.1 ∈ Ioo (-2 : ℝ) 2
  · rw [Set.indicator_of_mem ht, rev_windowField_chart]
    have hu : ‖((χ p.1 : ℝ) : ℂ) * W (τ₀ - p.1, p.2) c‖ₑ ≤
        ENNReal.ofReal M * ‖W (τ₀ - p.1, p.2)‖ₑ := by
      rw [enorm_mul]
      exact mul_le_mul' (wn_enorm_real_le _ M (hMχ p.1)) (PiLp.enorm_apply_le _ _)
    calc _ ≤ ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) *
            (ENNReal.ofReal M * ‖W (τ₀ - p.1, p.2)‖ₑ) ^ q :=
          mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hu hq.le)
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  · obtain ⟨h0, -⟩ := wn_cutoff_zero hχ ht
    rw [Set.indicator_of_notMem ht, rev_windowField_chart, h0]
    simp [ENNReal.zero_rpow_of_pos hq]

/-! ### Measurability -/

theorem rn_measurable_pt {W : ℝ × Space → CVec3} (hW : Measurable W) (τ₀ : ℝ) (c : Fin 3) :
    Measurable (fun p : ℝ × Space =>
      W (τ₀ + Real.log (1 - p.1), Real.exp (-Real.log (1 - p.1) / 2) • p.2) c) := by
  have hcomp : Measurable (fun v : CVec3 => v c) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) c).measurable
  have hφ : Measurable (fun p : ℝ × Space =>
      (τ₀ + Real.log (1 - p.1), Real.exp (-Real.log (1 - p.1) / 2) • p.2)) := by
    fun_prop
  exact hcomp.comp (hW.comp hφ)

theorem rn_measurable_adjWindowField {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ : ℝ)
    {W : ℝ × Space → CVec3} (hW : Measurable W) (c : Fin 3) :
    Measurable (adjWindowField χ τ₀ W c) := by
  have hχm : Measurable χ := hχ.smooth.continuous.measurable
  have hlog : Measurable (fun p : PS 3 => -Real.log (1 - p.1)) :=
    (Real.measurable_log.comp (measurable_const.sub measurable_fst)).neg
  have hr : Measurable (fun p : PS 3 => ((χ (-Real.log (1 - p.1)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (hχm.comp hlog)
  have hpt := rn_measurable_pt hW τ₀ c
  unfold adjWindowField
  refine Measurable.ite (measurableSet_lt measurable_fst measurable_const) ?_ measurable_const
  exact hr.mul hpt

theorem rn_measurable_adjWindowForce (μ : ℂ) {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ : ℝ)
    {W Fr : ℝ × Space → CVec3} (hW : Measurable W) (hFr : Measurable Fr) (c : Fin 3) :
    Measurable (adjWindowForce μ χ τ₀ W Fr c) := by
  have hχm : Measurable χ := hχ.smooth.continuous.measurable
  have hdm : Measurable (deriv χ) := (hχ.smooth.continuous_deriv (by simp)).measurable
  have hlog : Measurable (fun p : PS 3 => -Real.log (1 - p.1)) :=
    (Real.measurable_log.comp (measurable_const.sub measurable_fst)).neg
  have hχl : Measurable (fun p : PS 3 => χ (-Real.log (1 - p.1))) := hχm.comp hlog
  have hdl : Measurable (fun p : PS 3 => deriv χ (-Real.log (1 - p.1))) := hdm.comp hlog
  have hpt := rn_measurable_pt hW τ₀ c
  have hpt' := rn_measurable_pt hFr τ₀ c
  have hexp : Measurable (fun p : PS 3 => ((Real.exp (-Real.log (1 - p.1)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp hlog)
  have hA : Measurable (fun p : PS 3 =>
      ((deriv χ (-Real.log (1 - p.1)) : ℝ) : ℂ) -
        (1 + (starRingEnd ℂ) μ) * ((χ (-Real.log (1 - p.1)) : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp hdl).sub
      (measurable_const.mul (Complex.measurable_ofReal.comp hχl))
  have hB : Measurable (fun p : PS 3 => ((χ (-Real.log (1 - p.1)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp hχl
  unfold adjWindowForce
  refine Measurable.ite (measurableSet_lt measurable_fst measurable_const) ?_ measurable_const
  exact hexp.mul ((hA.mul hpt).add (hB.mul hpt'))

/-! ### Lebesgue integrals through the chart -/

theorem rn_lintegral_chart {f : PS 3 → ℂ} {s : ℝ} (hm : Measurable f)
    (hf0 : ∀ p : ℝ × Space, 1 ≤ p.1 → f p = 0) (hs : 0 < s) :
    ∫⁻ p, ‖f p‖ₑ ^ s =
      ∫⁻ p, ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) * ‖f (revChart p)‖ₑ ^ s :=
  rev_lintegral (fun p => ‖f p‖ₑ ^ s) (hm.enorm.pow_const _) fun p hp => by
    simp [hf0 p hp, ENNReal.zero_rpow_of_pos hs]

theorem rn_pullback_mul (hrt : r ≠ ⊤) {w : Yq P r} {W : ℝ × Space → CVec3} (hW : IsRep w W)
    (τ₀ : ℝ) {m : ℝ → ℝ≥0∞} (hm : Measurable m) {A : ℝ≥0∞} (hA : A ≠ ⊤) :
    ∫⁻ p : ℝ × Space, m p.1 * (A * ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal) =
      A * ∫⁻ t, m t * ‖w ((τ₀ - t : ℝ) : AddCircle P)‖ₑ ^ r.toReal := by
  calc ∫⁻ p : ℝ × Space, m p.1 * (A * ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal)
      = ∫⁻ p : ℝ × Space, A * (m p.1 * ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal) :=
        lintegral_congr fun p => by ring
    _ = A * ∫⁻ p : ℝ × Space, m p.1 * ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal :=
        lintegral_const_mul' A _ hA
    _ = _ := by rw [rev_lintegral_rep hrt hW τ₀ hm]

/-! ### Finiteness of the field -/

theorem rn_field_lt_top {χ : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hMχ : ∀ t, ‖χ t‖ ≤ M)
    (hχ : WindowCutoff χ) (hrt : r ≠ ⊤) (hr0 : 0 < r.toReal) (τ₀ : ℝ) {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) (c : Fin 3) :
    ∫⁻ p, ‖adjWindowField χ τ₀ W c p‖ₑ ^ r.toReal < ⊤ := by
  have hmU : Measurable ((Ioo (-2 : ℝ) 2).indicator
      (fun t => ENNReal.ofReal (Real.exp (-(5 * t / 2))))) :=
    Measurable.indicator (by fun_prop) measurableSet_Ioo
  rw [rn_lintegral_chart (rn_measurable_adjWindowField hχ τ₀ hW.meas.measurable c)
    (fun p hp => by simp [adjWindowField, not_lt.2 hp]) hr0]
  refine lt_of_le_of_lt (lintegral_mono fun p => rn_field_pointwise hM0 hMχ hχ hr0 τ₀ W c p) ?_
  rw [rn_pullback_mul hrt hW τ₀ hmU (ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top)]
  refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hr0.le ENNReal.ofReal_ne_top) ?_
  refine lt_of_le_of_lt (wn_weight_le (g := (Ioo (-2 : ℝ) 2).indicator
    (fun t => ENNReal.ofReal (Real.exp (-(5 * t / 2)))))
    (c := ENNReal.ofReal (Real.exp (2 * |(-(5 / 2) : ℝ)|))) ENNReal.ofReal_ne_top ?_ ?_
    (X := fun t => ‖w ((τ₀ - t : ℝ) : AddCircle P)‖ₑ ^ r.toReal)) ?_
  · intro t ht
    rw [Set.indicator_of_mem ht]
    exact ENNReal.ofReal_le_ofReal (by
      have := wn_exp_le (-(5 / 2)) t ht
      rwa [show -(5 / 2 : ℝ) * t = -(5 * t / 2) by ring] at this)
  · intro t ht
    rw [Set.indicator_of_notMem ht]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  rw [rev_window_transfer w τ₀]
  exact wn_window_lt_top hrt w τ₀

/-! ### The main theorem -/

theorem adjointWindowNorms : AdjointWindowNorms := by
  intro r _ hr1 hrt χ hχ
  have hr : 1 < r.toReal := by
    have := ENNReal.toReal_strict_mono hrt hr1
    simpa using this
  have hr0 : 0 < r.toReal := by linarith
  have hr1' : (1 : ℝ) ≤ r.toReal := hr.le
  obtain ⟨M, hM0, hMχ, hMd⟩ := wn_cutoff_bound hχ
  have h2nn : (0 : ℝ) ≤ (2 : ℝ) ^ (r.toReal - 1) := Real.rpow_nonneg (by norm_num) _
  have hX1 : 0 ≤ (2 : ℝ) ^ (r.toReal - 1) * Real.exp (2 * |r.toReal - 5 / 2|) :=
    mul_nonneg h2nn (Real.exp_pos _).le
  have hX : 0 ≤ (2 : ℝ) ^ (r.toReal - 1) * Real.exp (2 * |r.toReal - 5 / 2|) *
      (2 * M) ^ r.toReal := mul_nonneg hX1 (Real.rpow_nonneg (by linarith) _)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ((2 : ℝ) ^ (r.toReal - 1) *
      Real.exp (2 * |r.toReal - 5 / 2|) * (2 * M) ^ r.toReal) ^ (1 / r.toReal) :=
    ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact Real.rpow_nonneg hX _
  have hKpow : K ^ r.toReal = (2 : ℝ) ^ (r.toReal - 1) *
      Real.exp (2 * |r.toReal - 5 / 2|) * (2 * M) ^ r.toReal := by
    rw [hKdef, one_div, Real.rpow_inv_rpow hX hr0.ne']
  have h2 : ENNReal.ofReal ((2 : ℝ) ^ (r.toReal - 1)) = (2 : ℝ≥0∞) ^ (r.toReal - 1) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (x := 2) (p := r.toReal - 1) (by norm_num) (by linarith),
      ENNReal.ofReal_ofNat]
  have hKeq : ENNReal.ofReal K ^ r.toReal =
      ENNReal.ofReal (Real.exp (2 * |r.toReal - 5 / 2|)) *
        (2 : ℝ≥0∞) ^ (r.toReal - 1) * ENNReal.ofReal (2 * M) ^ r.toReal := by
    rw [ENNReal.ofReal_rpow_of_nonneg hK0 hr0.le, hKpow, ← h2,
      ENNReal.ofReal_mul hX1, ENNReal.ofReal_mul h2nn,
      ENNReal.ofReal_rpow_of_nonneg (by linarith) hr0.le]
    ring
  have hC : ∀ x y : ℝ≥0∞, (x + y) ^ r.toReal ≤
      (2 : ℝ≥0∞) ^ (r.toReal - 1) * (x ^ r.toReal + y ^ r.toReal) :=
    fun x y => ENNReal.rpow_add_le_mul_rpow_add_rpow x y hr1'
  have hBne : ENNReal.ofReal (Real.exp (2 * |r.toReal - 5 / 2|)) *
      (2 : ℝ≥0∞) ^ (r.toReal - 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num))
  refine ⟨K, hK0, ?_⟩
  intro P _ μ f w W Fr hW hFr τ₀ c
  have hWm : Measurable W := hW.meas.measurable
  have hFm : Measurable Fr := hFr.meas.measurable
  have hu_mem : MemLp (adjWindowField χ τ₀ W c) (ENNReal.ofReal r.toReal) volume :=
    wn_memLp hr0 (rn_measurable_adjWindowField hχ τ₀ hWm c).aestronglyMeasurable
      (rn_field_lt_top hM0 hMχ hχ hrt hr0 τ₀ hW c)
  set mF : ℝ → ℝ≥0∞ := (Ioo (-2 : ℝ) 2).indicator (fun t =>
    ENNReal.ofReal (Real.exp ((r.toReal - 5 / 2) * t)) * (2 : ℝ≥0∞) ^ (r.toReal - 1)) with hmF
  set AW : ℝ≥0∞ := ENNReal.ofReal (2 * M * (1 + ‖μ‖)) ^ r.toReal with hAWdef
  set Af : ℝ≥0∞ := ENNReal.ofReal (2 * M) ^ r.toReal with hAfdef
  set c' : ℝ≥0∞ := ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal with hc'def
  set B' : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * |r.toReal - 5 / 2|)) *
    (2 : ℝ≥0∞) ^ (r.toReal - 1) with hB'def
  set IW : ℝ≥0∞ := ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), ‖w (τ : AddCircle P)‖ₑ ^ r.toReal with hIWdef
  set IF : ℝ≥0∞ := ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), ‖f (τ : AddCircle P)‖ₑ ^ r.toReal with hIFdef
  have hmF_meas : Measurable mF :=
    Measurable.indicator (by fun_prop) measurableSet_Ioo
  have hAW_ne : AW ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top
  have hAf_ne : Af ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top
  have hc'_ne : c' ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top
  have hAW_split : AW = Af * c' := by
    rw [hAWdef, hAfdef, hc'def, ENNReal.ofReal_mul (by linarith),
      ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
  have hwb : ∫⁻ t, mF t * ‖w ((τ₀ - t : ℝ) : AddCircle P)‖ₑ ^ r.toReal ≤ B' * IW := by
    rw [hIWdef, ← rev_window_transfer w τ₀]
    refine wn_weight_le (c := B') hBne ?_ ?_
    · intro t ht
      rw [hmF, Set.indicator_of_mem ht]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (wn_exp_le _ t ht)) le_rfl
    · intro t ht
      rw [hmF, Set.indicator_of_notMem ht]
  have hfb : ∫⁻ t, mF t * ‖f ((τ₀ - t : ℝ) : AddCircle P)‖ₑ ^ r.toReal ≤ B' * IF := by
    rw [hIFdef, ← rev_window_transfer f τ₀]
    refine wn_weight_le (c := B') hBne ?_ ?_
    · intro t ht
      rw [hmF, Set.indicator_of_mem ht]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (wn_exp_le _ t ht)) le_rfl
    · intro t ht
      rw [hmF, Set.indicator_of_notMem ht]
  have hF_meas : Measurable (adjWindowForce μ χ τ₀ W Fr c) :=
    rn_measurable_adjWindowForce μ hχ τ₀ hWm hFm c
  have hFzero : ∀ p : ℝ × Space, 1 ≤ p.1 → adjWindowForce μ χ τ₀ W Fr c p = 0 := fun p hp => by
    simp [adjWindowForce, not_lt.2 hp]
  have hφ2 : Measurable (fun p : ℝ × Space => (τ₀ - p.1, p.2)) := by fun_prop
  have hVW : Measurable (fun p : ℝ × Space => ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal) :=
    ((hWm.comp hφ2).enorm).pow_const _
  have hmeasA : Measurable (fun p : ℝ × Space =>
      mF p.1 * (AW * ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal)) :=
    (hmF_meas.comp measurable_fst).mul (measurable_const.mul hVW)
  have hmain : ∫⁻ p, ‖adjWindowForce μ χ τ₀ W Fr c p‖ₑ ^ r.toReal ≤
      AW * (B' * IW) + Af * (B' * IF) := by
    calc ∫⁻ p, ‖adjWindowForce μ χ τ₀ W Fr c p‖ₑ ^ r.toReal
        = ∫⁻ p, ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) *
            ‖adjWindowForce μ χ τ₀ W Fr c (revChart p)‖ₑ ^ r.toReal :=
          rn_lintegral_chart hF_meas hFzero hr0
      _ ≤ ∫⁻ p : ℝ × Space, mF p.1 * (AW * ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal +
            Af * ‖Fr (τ₀ - p.1, p.2)‖ₑ ^ r.toReal) :=
          lintegral_mono fun p => rn_force_pointwise hM0 hMχ hMd hχ hr0 hC μ τ₀ W Fr c p
      _ = ∫⁻ p : ℝ × Space, (mF p.1 * (AW * ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal) +
            mF p.1 * (Af * ‖Fr (τ₀ - p.1, p.2)‖ₑ ^ r.toReal)) :=
          lintegral_congr fun p => mul_add _ _ _
      _ = (∫⁻ p : ℝ × Space, mF p.1 * (AW * ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal)) +
            ∫⁻ p : ℝ × Space, mF p.1 * (Af * ‖Fr (τ₀ - p.1, p.2)‖ₑ ^ r.toReal) :=
          lintegral_add_left hmeasA _
      _ = AW * (∫⁻ t, mF t * ‖w ((τ₀ - t : ℝ) : AddCircle P)‖ₑ ^ r.toReal) +
          Af * (∫⁻ t, mF t * ‖f ((τ₀ - t : ℝ) : AddCircle P)‖ₑ ^ r.toReal) := by
          rw [rn_pullback_mul hrt hW τ₀ hmF_meas hAW_ne, rn_pullback_mul hrt hFr τ₀ hmF_meas hAf_ne]
      _ ≤ AW * (B' * IW) + Af * (B' * IF) :=
          add_le_add (mul_le_mul' le_rfl hwb) (mul_le_mul' le_rfl hfb)
  have hmain' : eLpNorm (adjWindowForce μ χ τ₀ W Fr c) (ENNReal.ofReal r.toReal) volume ^
      r.toReal ≤ AW * (B' * IW) + Af * (B' * IF) := by
    rw [wn_eLpNorm_rpow hr0]
    exact hmain
  have hIW_lt : IW < ⊤ := wn_window_lt_top hrt w τ₀
  have hIF_lt : IF < ⊤ := wn_window_lt_top hrt f τ₀
  have hfin : AW * (B' * IW) + Af * (B' * IF) < ⊤ :=
    ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hAW_ne)
        (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hBne) hIW_lt),
       ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hAf_ne)
        (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hBne) hIF_lt)⟩
  have hF_lt : eLpNorm (adjWindowForce μ χ τ₀ W Fr c) (ENNReal.ofReal r.toReal) volume < ⊤ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    have h1 := hmain'.trans_lt hfin
    rw [hcon, ENNReal.top_rpow_of_pos hr0] at h1
    exact lt_irrefl _ h1
  have hbound : eLpNorm (adjWindowForce μ χ τ₀ W Fr c) (ENNReal.ofReal r.toReal) volume ^
      r.toReal ≤ ENNReal.ofReal K ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
        (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
          ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) := by
    refine hmain'.trans ?_
    have hsum : IF + c' * IW ≤ ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
        (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
          ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) := by
      have h1 : ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
          c' * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal = c' * IW :=
        lintegral_const_mul' c' _ hc'_ne
      rw [← h1]
      exact le_lintegral_add _ _
    calc AW * (B' * IW) + Af * (B' * IF) = ENNReal.ofReal K ^ r.toReal * (IF + c' * IW) := by
          rw [hKeq, hAW_split]
          ring
      _ ≤ ENNReal.ofReal K ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
          (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
            ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) :=
          mul_le_mul' le_rfl hsum
  exact ⟨hu_mem, ⟨hF_meas.aestronglyMeasurable, hF_lt⟩, hbound⟩

end UnforcedLeray.Short.PartIIa
