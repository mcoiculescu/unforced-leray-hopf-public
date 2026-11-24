import UnforcedLeray.Lib.HeatR3
import UnforcedLeray.Lib.PhaseSpace.Cutoff

/-!
# Weak Laplacians, decaying tests, and the heat flow of a weak-Laplacian pair (INF11 S9b, part 1)

Helper for target **S9b** (`gradient_interp`, heat `L^q` gradient interpolation, decision D15)

`scoping/INF01-CZ.md` §4.4; manuscript `paper/main.tex` lines 7536–7548 (`eq:free-stress-19`,
blueprint B0428) and 3637–3639 (B0432).

* `IsWeakLaplacian w L`: `L = Δw` in distributions, `∫ (Δφ) • w = ∫ φ • L` for every
  `φ ∈ C_c^∞(ℝ³)` (the manuscript's "`w, Δw ∈ Y_q` in distributions", spatial slice);
* `laplacian_mul`: `Δ(aψ) = aΔψ + 2∑ⱼ ∂ⱼa ∂ⱼψ + (Δa)ψ`;
* `IsWeakLaplacian.extend`: the identity extends to smooth tests that decay, with `|ψ|`,
  `|∂ⱼψ|`, `|Δψ| ≤ C(1 + |y|)^{-m}`, when `(1 + |y|)^{-m}w` and `(1 + |y|)^{-m}L` are integrable
  (cutoff `χₙψ`, dominated convergence);
* `vlap_average_eq`: for a weak-Laplacian pair of admissible fields and `θ > 0`,
  `Δ(e^{θΔ}w) = e^{θΔ}L` at every point (test `G_θ(x - ·)`).

Status: infrastructure for S9b only; no manuscript unit is closed here.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal ContDiff
open UnforcedLeray.PhaseSpace (sd cutχ cutC GoodMult)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The distributional Laplacian -/

/-- **Weak Laplacian** (S9b; tex 7541–7548): `L = Δw` in distributions on `ℝ³`, tested against
`C_c^∞` scalar tests, `∫ (Δφ) • w = ∫ φ • L`. For `w, L ∈ L^q_loc` both pairings converge. -/
structure IsWeakLaplacian (w L : Space → E) : Prop where
  identity : ∀ φ : Space → ℝ, IsSpatialTest φ → ∫ x, laplacian φ x • w x = ∫ x, φ x • L x

theorem laplacian_eq_sum_sd (f : Space → ℝ) (y : Space) :
    laplacian f y = ∑ j : Fin 3, sd j (sd j f) y := rfl

/-! ### Product rule -/

theorem sd_mul {a ψ : Space → ℝ} (ha : Differentiable ℝ a) (hψ : Differentiable ℝ ψ) (j : Fin 3) :
    sd j (fun y => a y * ψ y) = fun y => sd j a y * ψ y + a y * sd j ψ y := by
  funext y
  simp only [sd]
  rw [fderiv_fun_mul (ha y) (hψ y)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `Δ(aψ) = aΔψ + 2∑ⱼ ∂ⱼa ∂ⱼψ + (Δa)ψ` for `C^∞` scalars. -/
theorem laplacian_mul {a ψ : Space → ℝ} (ha : ContDiff ℝ ∞ a) (hψ : ContDiff ℝ ∞ ψ) (y : Space) :
    laplacian (fun y => a y * ψ y) y =
      a y * laplacian ψ y + 2 * ∑ j : Fin 3, sd j a y * sd j ψ y + laplacian a y * ψ y := by
  have hd : ∀ {f : Space → ℝ}, ContDiff ℝ ∞ f → Differentiable ℝ f :=
    fun hf => hf.differentiable (by simp)
  have hsd : ∀ {f : Space → ℝ}, ContDiff ℝ ∞ f → ∀ j, ContDiff ℝ ∞ (sd j f) :=
    fun hf j => PhaseSpace.contDiff_sd hf j
  simp only [laplacian_eq_sum_sd]
  have h1 : ∀ j : Fin 3, sd j (sd j (fun y => a y * ψ y)) y =
      a y * sd j (sd j ψ) y + 2 * (sd j a y * sd j ψ y) + sd j (sd j a) y * ψ y := by
    intro j
    rw [sd_mul (hd ha) (hd hψ) j]
    have e : (fun y => sd j a y * ψ y + a y * sd j ψ y) =
        (fun y => sd j a y * ψ y) + (fun y => a y * sd j ψ y) := rfl
    have hA : Differentiable ℝ (fun y => sd j a y * ψ y) := (hd (hsd ha j)).mul (hd hψ)
    have hB : Differentiable ℝ (fun y => a y * sd j ψ y) := (hd ha).mul (hd (hsd hψ j))
    have hsum : ∀ F G : Space → ℝ, Differentiable ℝ F → Differentiable ℝ G →
        sd j (F + G) y = sd j F y + sd j G y := fun F G hF hG => by
      show fderiv ℝ (F + G) y (coordinateVector j) =
        fderiv ℝ F y (coordinateVector j) + fderiv ℝ G y (coordinateVector j)
      rw [fderiv_add (hF y) (hG y)]; rfl
    rw [e, hsum _ _ hA hB, sd_mul (hd (hsd ha j)) (hd hψ) j, sd_mul (hd ha) (hd (hsd hψ j)) j]
    ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_mul]

/-! ### The cutoff family -/

theorem hasCompactSupport_cutχ (n : ℕ) : HasCompactSupport (cutχ n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * ((n : ℝ) + 1)))
    fun y hy => ?_
  refine PhaseSpace.cutχ_eq_zero n ?_
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hy
  exact hy.le

theorem isSpatialTest_cut (n : ℕ) {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    IsSpatialTest (fun y => cutχ n y * ψ y) :=
  ⟨(PhaseSpace.contDiff_cutχ n).mul hψ, (hasCompactSupport_cutχ n).mul_right⟩

/-! ### Extension to decaying tests -/

theorem weight_pos (m : ℝ) (y : Space) : 0 < (1 + ‖y‖) ^ (-m) := by positivity

/-- **Extension of the weak Laplacian to decaying tests.** If `(1+|y|)^{-m} w` and
`(1+|y|)^{-m} L` are integrable and `ψ` is smooth with `|ψ|, |∂ⱼψ|, |Δψ| ≤ C(1+|y|)^{-m}`, then
`∫ (Δψ) • w = ∫ ψ • L`. -/
theorem IsWeakLaplacian.extend {w L : Space → E} (hWL : IsWeakLaplacian w L)
    (hwm : AEStronglyMeasurable w volume) (hLm : AEStronglyMeasurable L volume) {m : ℝ}
    (hw : Integrable (fun y => (1 + ‖y‖) ^ (-m) • w y))
    (hL : Integrable (fun y => (1 + ‖y‖) ^ (-m) • L y))
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) {C : ℝ}
    (hb0 : ∀ y, |ψ y| ≤ C * (1 + ‖y‖) ^ (-m))
    (hb1 : ∀ j y, |sd j ψ y| ≤ C * (1 + ‖y‖) ^ (-m))
    (hb2 : ∀ y, |laplacian ψ y| ≤ C * (1 + ‖y‖) ^ (-m)) :
    ∫ x, laplacian ψ x • w x = ∫ x, ψ x • L x := by
  obtain ⟨L0, hL0⟩ := PhaseSpace.goodMult_cutχ_sub_one.bound
  have hL1 : ∀ j : Fin 3, GoodMult fun n y => (1 : ℝ) * sd j (cutχ n) y :=
    fun j => PhaseSpace.goodMult_sd_cutχ j 1
  choose L1 hL1b using fun j => (hL1 j).bound
  obtain ⟨L2, hL2⟩ := PhaseSpace.goodMult_lapS_cutχ.bound
  have hcut : ∀ n y, |cutχ n y| ≤ L0 + 1 := by
    intro n y
    have := hL0 n y
    calc |cutχ n y| = |(cutχ n y - 1) + 1| := by ring_nf
      _ ≤ |cutχ n y - 1| + |1| := abs_add_le _ _
      _ ≤ L0 + 1 := by rw [abs_one]; linarith
  have hsdcut : ∀ j n y, |sd j (cutχ n) y| ≤ L1 j := by
    intro j n y; simpa using hL1b j n y
  have hlapcut : ∀ n y, |laplacian (cutχ n) y| ≤ L2 := fun n y => hL2 n y
  set K : ℝ := (L0 + 1) + 2 * ∑ j : Fin 3, L1 j + L2 with hK
  have hlapn : ∀ n y, laplacian (fun y => cutχ n y * ψ y) y =
      cutχ n y * laplacian ψ y + 2 * ∑ j : Fin 3, sd j (cutχ n) y * sd j ψ y +
        laplacian (cutχ n) y * ψ y :=
    fun n y => laplacian_mul (PhaseSpace.contDiff_cutχ n) hψ y
  have hbound : ∀ n y, |laplacian (fun y => cutχ n y * ψ y) y| ≤
      K * (C * (1 + ‖y‖) ^ (-m)) := by
    intro n y
    rw [hlapn n y]
    have hW := weight_pos m y
    have t1 : |cutχ n y * laplacian ψ y| ≤ (L0 + 1) * (C * (1 + ‖y‖) ^ (-m)) := by
      rw [abs_mul]; exact mul_le_mul (hcut n y) (hb2 y) (abs_nonneg _)
        ((abs_nonneg _).trans (hcut n y))
    have t2 : |2 * ∑ j : Fin 3, sd j (cutχ n) y * sd j ψ y| ≤
        2 * ∑ j : Fin 3, L1 j * (C * (1 + ‖y‖) ^ (-m)) := by
      rw [abs_mul, abs_two]
      gcongr
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul (hsdcut j n y) (hb1 j y) (abs_nonneg _)
        ((abs_nonneg _).trans (hsdcut j n y))
    have t3 : |laplacian (cutχ n) y * ψ y| ≤ L2 * (C * (1 + ‖y‖) ^ (-m)) := by
      rw [abs_mul]; exact mul_le_mul (hlapcut n y) (hb0 y) (abs_nonneg _)
        ((abs_nonneg _).trans (hlapcut n y))
    calc _ ≤ |cutχ n y * laplacian ψ y| + |2 * ∑ j : Fin 3, sd j (cutχ n) y * sd j ψ y| +
          |laplacian (cutχ n) y * ψ y| := abs_add_three _ _ _
      _ ≤ (L0 + 1) * (C * (1 + ‖y‖) ^ (-m)) +
          2 * ∑ j : Fin 3, L1 j * (C * (1 + ‖y‖) ^ (-m)) + L2 * (C * (1 + ‖y‖) ^ (-m)) := by
          linarith
      _ = K * (C * (1 + ‖y‖) ^ (-m)) := by rw [hK, ← Finset.sum_mul]; ring
  -- pointwise limits
  have hlim_cut : ∀ y, Tendsto (fun n => cutχ n y) atTop (𝓝 1) := by
    intro y
    have := PhaseSpace.goodMult_cutχ_sub_one.lim y
    simpa using this.add_const 1
  have hlim_lap : ∀ y, Tendsto (fun n => laplacian (fun y => cutχ n y * ψ y) y) atTop
      (𝓝 (laplacian ψ y)) := by
    intro y
    simp_rw [hlapn _ y]
    have h1 : Tendsto (fun n => cutχ n y * laplacian ψ y) atTop (𝓝 (1 * laplacian ψ y)) :=
      (hlim_cut y).mul_const _
    have h2 : Tendsto (fun n => 2 * ∑ j : Fin 3, sd j (cutχ n) y * sd j ψ y) atTop
        (𝓝 (2 * ∑ j : Fin 3, (0 : ℝ) * sd j ψ y)) := by
      refine (tendsto_finsetSum _ fun j _ => ?_).const_mul 2
      have := (hL1 j).lim y
      simpa using this.mul_const (sd j ψ y)
    have h3 : Tendsto (fun n => laplacian (cutχ n) y * ψ y) atTop (𝓝 (0 * ψ y)) :=
      (PhaseSpace.goodMult_lapS_cutχ.lim y).mul_const _
    have := (h1.add h2).add h3
    simpa using this
  -- the identity for each cutoff test
  have hid : ∀ n, ∫ x, laplacian (fun y => cutχ n y * ψ y) x • w x =
      ∫ x, (cutχ n x * ψ x) • L x := fun n => hWL.identity _ (isSpatialTest_cut n hψ)
  -- limits of both sides
  have hcontlap : ∀ n, Continuous (laplacian (fun y => cutχ n y * ψ y)) := by
    intro n
    have hf := (PhaseSpace.contDiff_cutχ n).mul hψ
    have e : laplacian (fun y => cutχ n y * ψ y) =
        fun y => ∑ j : Fin 3, sd j (sd j (fun y => cutχ n y * ψ y)) y := rfl
    rw [e]
    refine continuous_finset_sum _ fun j _ => ?_
    exact (PhaseSpace.contDiff_sd (PhaseSpace.contDiff_sd hf j) j).continuous
  have hLHS : Tendsto (fun n => ∫ x, laplacian (fun y => cutχ n y * ψ y) x • w x) atTop
      (𝓝 (∫ x, laplacian ψ x • w x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => K * C * ‖(1 + ‖y‖) ^ (-m) • w y‖) (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact (hcontlap n).aestronglyMeasurable.smul hwm
    · exact hw.norm.const_mul _
    · refine Eventually.of_forall fun y => ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (weight_pos m y).le]
      calc |laplacian (fun y => cutχ n y * ψ y) y| * ‖w y‖
          ≤ K * (C * (1 + ‖y‖) ^ (-m)) * ‖w y‖ :=
            mul_le_mul_of_nonneg_right (hbound n y) (norm_nonneg _)
        _ = K * C * ((1 + ‖y‖) ^ (-m) * ‖w y‖) := by ring
    · exact Eventually.of_forall fun y => (hlim_lap y).smul_const (w y)
  have hRHS : Tendsto (fun n => ∫ x, (cutχ n x * ψ x) • L x) atTop
      (𝓝 (∫ x, ψ x • L x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => (L0 + 1) * C * ‖(1 + ‖y‖) ^ (-m) • L y‖) (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact (((PhaseSpace.contDiff_cutχ n).mul hψ).continuous).aestronglyMeasurable.smul hLm
    · exact hL.norm.const_mul _
    · refine Eventually.of_forall fun y => ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (weight_pos m y).le,
        abs_mul]
      calc |cutχ n y| * |ψ y| * ‖L y‖ ≤ (L0 + 1) * (C * (1 + ‖y‖) ^ (-m)) * ‖L y‖ := by
            gcongr
            · exact (abs_nonneg _).trans (hcut n y)
            · exact hcut n y
            · exact hb0 y
        _ = (L0 + 1) * C * ((1 + ‖y‖) ^ (-m) * ‖L y‖) := by ring
    · refine Eventually.of_forall fun y => ?_
      have := ((hlim_cut y).mul_const (ψ y)).smul_const (L y)
      simpa using this
  have hseq : (fun n => ∫ x, laplacian (fun y => cutχ n y * ψ y) x • w x) =
      fun n => ∫ x, (cutχ n x * ψ x) • L x := funext hid
  rw [hseq] at hLHS
  exact tendsto_nhds_unique hLHS hRHS

/-! ### Reflected translates -/

theorem hasFDerivAt_comp_sub_left {f : Space → ℝ} (hf : Differentiable ℝ f) (x z : Space) :
    HasFDerivAt (fun z => f (x - z))
      ((fderiv ℝ f (x - z)).comp (-ContinuousLinearMap.id ℝ Space)) z :=
  (hf (x - z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_sub x)

theorem sd_comp_sub_left {f : Space → ℝ} (hf : Differentiable ℝ f) (x : Space) (j : Fin 3) :
    sd j (fun z => f (x - z)) = fun z => -(sd j f (x - z)) := by
  funext z
  simp only [sd]
  rw [(hasFDerivAt_comp_sub_left hf x z).fderiv]
  simp

theorem laplacian_comp_sub_left {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (x z : Space) :
    laplacian (fun z => f (x - z)) z = laplacian f (x - z) := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  simp only [laplacian_eq_sum_sd]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sd_comp_sub_left hd x j]
  have hdj : Differentiable ℝ (sd j f) :=
    (PhaseSpace.contDiff_sd hf j).differentiable (by simp)
  have e : (fun z => -(sd j f (x - z))) = fun z => (-1 : ℝ) * sd j f (x - z) := by
    funext z; ring
  have hdiff : Differentiable ℝ (fun z => sd j f (x - z)) :=
    fun z => (hdj (x - z)).comp z (differentiableAt_id.const_sub x)
  rw [e, PhaseSpace.sd_const_mul hdiff (-1) j, sd_comp_sub_left hdj x j]
  ring

/-! ### Derivative bounds through `iteratedFDeriv` -/

theorem abs_sd_le (f : Space → ℝ) (j : Fin 3) (y : Space) :
    |sd j f y| ≤ ‖iteratedFDeriv ℝ 1 f y‖ := by
  rw [norm_iteratedFDeriv_one, ← Real.norm_eq_abs]
  calc ‖fderiv ℝ f y (coordinateVector j)‖ ≤ ‖fderiv ℝ f y‖ * ‖coordinateVector j‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ f y‖ := by rw [norm_coordinateVector, mul_one]

theorem abs_laplacian_le {f : Space → ℝ} (hf : ContDiff ℝ 2 f) (y : Space) :
    |laplacian f y| ≤ 3 * ‖iteratedFDeriv ℝ 2 f y‖ := by
  rw [laplacian_eq_sum_fderiv_fderiv hf y]
  have h2 : ‖fderiv ℝ (fderiv ℝ f) y‖ = ‖iteratedFDeriv ℝ 2 f y‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hj : ∀ j : Fin 3, |fderiv ℝ (fderiv ℝ f) y (coordinateVector j) (coordinateVector j)| ≤
      ‖iteratedFDeriv ℝ 2 f y‖ := by
    intro j
    rw [← Real.norm_eq_abs, ← h2]
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ f) y (coordinateVector j)‖ * ‖coordinateVector j‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) y‖ * ‖coordinateVector j‖ * ‖coordinateVector j‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [norm_coordinateVector]; ring
  calc ∑ j : Fin 3, |fderiv ℝ (fderiv ℝ f) y (coordinateVector j) (coordinateVector j)|
      ≤ ∑ _j : Fin 3, ‖iteratedFDeriv ℝ 2 f y‖ := Finset.sum_le_sum fun j _ => hj j
    _ = 3 * ‖iteratedFDeriv ℝ 2 f y‖ := by simp

/-! ### The heat flow of a weak-Laplacian pair -/

theorem contDiff_kernel {θ : ℝ} (hθ : 0 < θ) : ContDiff ℝ ∞ (kernel θ) := by
  simpa using (decayKernel_gaussKernel (m := 0) hθ le_rfl).smooth

/-- **`Δ e^{θΔ}w = e^{θΔ}L`** at every point, for `θ > 0`, if `L = Δw` weakly and both fields are
admissible (`(1 + |y|)^{-m}`-integrable for some `m`). -/
theorem vlap_average_eq [CompleteSpace E] {w L : Space → E} (hWL : IsWeakLaplacian w L) (hw : HeatAdmissible w)
    (hL : HeatAdmissible L) {θ : ℝ} (hθ : 0 < θ) (x : Space) :
    vlap (average θ w) x = average θ L x := by
  obtain ⟨hwm, mw, hmw⟩ := hw
  obtain ⟨hLm, mL, hmL⟩ := hL
  set m : ℕ := max mw mL
  have hw' := integrable_weight_mono hwm (le_max_left mw mL) hmw
  have hL' := integrable_weight_mono hLm (le_max_right mw mL) hmL
  have hK := contDiff_kernel hθ
  set ψ : Space → ℝ := fun z => kernel θ (x - z) with hψ
  have hψs : ContDiff ℝ ∞ ψ := hK.comp (contDiff_const.sub contDiff_id)
  -- decay of `G_θ` and its first two derivatives
  have hm0 : (0 : ℝ) ≤ m := by positivity
  obtain ⟨C0, hC0, h0⟩ := norm_iteratedFDeriv_gaussKernel_le_weight 3 0 hθ hm0
  obtain ⟨C1, hC1, h1⟩ := norm_iteratedFDeriv_gaussKernel_le_weight 3 1 hθ hm0
  obtain ⟨C2, hC2, h2⟩ := norm_iteratedFDeriv_gaussKernel_le_weight 3 2 hθ hm0
  have hG : ∀ _n : ℕ, Gaussian.gaussKernel 3 θ = kernel θ := fun _ =>
    congrFun Gaussian.gaussKernel_three_eq θ
  set Cx : ℝ := (1 + ‖x‖) ^ (m : ℝ) * (3 * (C0 + C1 + C2)) with hCx
  have htr : ∀ z : Space, (1 + ‖x - z‖) ^ (-(m : ℝ)) ≤ (1 + ‖x‖) ^ (m : ℝ) * (1 + ‖z‖) ^ (-(m : ℝ)) :=
    fun z => one_add_norm_sub_rpow_neg_le hm0 x z
  have hxpos : 0 ≤ (1 + ‖x‖) ^ (m : ℝ) := by positivity
  have hwz : ∀ z : Space, 0 ≤ (1 + ‖z‖) ^ (-(m : ℝ)) := fun z => (weight_pos _ z).le
  have hfin : ∀ (c : ℝ) (z : Space), 0 ≤ c → c ≤ 3 * (C0 + C1 + C2) →
      c * (1 + ‖x - z‖) ^ (-(m : ℝ)) ≤ Cx * (1 + ‖z‖) ^ (-(m : ℝ)) := by
    intro c z hc hc'
    calc c * (1 + ‖x - z‖) ^ (-(m : ℝ)) ≤ c * ((1 + ‖x‖) ^ (m : ℝ) * (1 + ‖z‖) ^ (-(m : ℝ))) :=
          mul_le_mul_of_nonneg_left (htr z) hc
      _ ≤ 3 * (C0 + C1 + C2) * ((1 + ‖x‖) ^ (m : ℝ) * (1 + ‖z‖) ^ (-(m : ℝ))) :=
          mul_le_mul_of_nonneg_right hc' (mul_nonneg hxpos (hwz z))
      _ = Cx * (1 + ‖z‖) ^ (-(m : ℝ)) := by rw [hCx]; ring
  have hb0 : ∀ z, |ψ z| ≤ Cx * (1 + ‖z‖) ^ (-(m : ℝ)) := by
    intro z
    have := h0 (x - z)
    rw [norm_iteratedFDeriv_zero, hG 0, Real.norm_eq_abs] at this
    exact (this.trans (le_refl _)).trans (hfin C0 z hC0.le (by linarith))
  have hb1 : ∀ j z, |sd j ψ z| ≤ Cx * (1 + ‖z‖) ^ (-(m : ℝ)) := by
    intro j z
    rw [hψ, sd_comp_sub_left (hK.differentiable (by simp)) x j, abs_neg]
    have := h1 (x - z)
    rw [hG 1] at this
    exact ((abs_sd_le _ j _).trans this).trans (hfin C1 z hC1.le (by linarith))
  have hb2 : ∀ z, |laplacian ψ z| ≤ Cx * (1 + ‖z‖) ^ (-(m : ℝ)) := by
    intro z
    rw [hψ, laplacian_comp_sub_left hK x z]
    have := h2 (x - z)
    rw [hG 2] at this
    refine (abs_laplacian_le (hK.of_le (by simp)) _).trans ?_
    calc 3 * ‖iteratedFDeriv ℝ 2 (kernel θ) (x - z)‖ ≤ 3 * (C2 * (1 + ‖x - z‖) ^ (-(m : ℝ))) := by
          gcongr
      _ = (3 * C2) * (1 + ‖x - z‖) ^ (-(m : ℝ)) := by ring
      _ ≤ _ := hfin (3 * C2) z (by positivity) (by linarith)
  have hext := hWL.extend hwm hLm hw' hL' hψs hb0 hb1 hb2
  -- assemble
  rw [← integral_laplacian_kernel_eq ⟨hwm, mw, hmw⟩ hθ x]
  have e1 : ∫ y, laplacian (kernel θ) y • w (x - y) = ∫ z, laplacian ψ z • w z := by
    rw [← integral_sub_left_eq_self (fun z => laplacian ψ z • w z) volume x]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hψ, laplacian_comp_sub_left hK x (x - y), sub_sub_cancel]
  have e2 : ∫ z, ψ z • L z = average θ L x := by
    simp only [average]
    rw [← integral_sub_left_eq_self (fun y => kernel θ y • L (x - y)) volume x]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hψ, sub_sub_cancel]
  rw [e1, hext, e2]

end UnforcedLeray.Heat
