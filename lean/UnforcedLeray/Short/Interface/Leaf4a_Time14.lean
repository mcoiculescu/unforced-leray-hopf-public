import UnforcedLeray.Short.Interface.WindowSteps2
import UnforcedLeray.Units.B0424.Tests
import UnforcedLeray.Units.B0424.Chart
import UnforcedLeray.Units.B0005.Bridge.Unfold

/-!
# Interface: step W1b, the time change `θ = e^t` (`eq:free-stress-14`)

Task `Interface:I13`. Source of record: `the November 2 reference manuscript`
(the window argument of `paper/main.tex` lines 7493-7499 for the time change).

`WindowChartTimeChange` (`Short/Interface/WindowSteps2.lean`) is proved from the chart equation
`ChartEquationHolds` (step W1a). For a heat test `Ψ` on `PS 3` put `Ξ = timeTest χ Ψ`, so
`Ξ(t, x) = χ(t) Ψ(e^t, x)`. The change of variables `θ = e^t` is `integral_expChart`
(`Units/B0424/Chart.lean`), and the chain rule for `Ξ` is `tD_timeTest`, `sLap_timeTest`
(`Units/B0424/Tests.lean`). The chart pieces are integrable by the phase unfolding
`IsY2.pairTerm_unfold` (`Units/B0005/Bridge/Unfold.lean`), transported through the dilation
`dilChart` and the shift in `t` (`integrable_dilChart_iff`, `integrable_shift_iff`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Parabolic UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

/-! ## Helpers: bounds, the chart homeomorphism, and integrability -/

/-- A compactly supported function on `ℝ × ℝ³` vanishes for large `|t|`. -/
theorem exists_time_bound {φ : ℝ × Space → ℝ} (hφc : HasCompactSupport φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t y, M < |t| → φ (t, y) = 0 := by
  obtain ⟨M, hM⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)
  refine ⟨max M 0, le_max_right _ _, fun t y ht => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have h1 := hM h
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : |t| ≤ ‖((t, y) : ℝ × Space)‖ := by
    simpa [Real.norm_eq_abs] using norm_fst_le ((t, y) : ℝ × Space)
  linarith [le_max_left M 0]

/-- Derivatives of a smooth test are smooth with compact support: `sLap` version. -/
theorem isSTTest_sLap' {f : PS 3 → ℝ} (hf : IsSTTest f) : IsSTTest (sLap f) := by
  have h : sLap f = sD2 0 0 f + sD2 1 1 f + sD2 2 2 f := by
    funext X
    simp [sLap, Fin.sum_univ_three]
  rw [h]
  exact ((hf.sD2 0 0).add (hf.sD2 1 1)).add (hf.sD2 2 2)

/-- Integrability of `T · w_i` on `ℝ × ℝ³` for a smooth compactly supported `T`. This is the
phase unfolding `IsY2.pairTerm_unfold` applied to the vector test `T e_i`. -/
theorem integrable_mul_coord {P : ℝ} (hP : 0 < P) {w : ℝ → SpatialField}
    (hw : B0005.IsY2 P w) (i : Fin 3) {T : ℝ × Space → ℝ} (hT : ContDiff ℝ ∞ T)
    (hTc : HasCompactSupport T) :
    Integrable (fun z : ℝ × Space => T z * (w z.1 z.2) i) := by
  haveI : Fact (0 < P) := ⟨hP⟩
  obtain ⟨M, hM0, hM⟩ := exists_time_bound hTc
  obtain ⟨R, -, hR⟩ := B0424.exists_bound_space hTc
  let ψ : ℝ × Space → Space := fun z => T z • EuclideanSpace.single i (1 : ℝ)
  have hψs : ContDiff ℝ ∞ ψ := hT.smul contDiff_const
  have hψ0 : IsPhaseTest 0 ψ :=
    ⟨hψs, fun τ y => by simp [ψ], R, fun τ y hy => by simp [ψ, hR τ y hy]⟩
  have hψT : TimeSupp (-M) M ψ := by
    intro τ y hτ
    have hlt : M < |τ| := by
      by_contra hc
      push_neg at hc
      exact hτ (abs_le.mp hc)
    simp [ψ, hM τ y hlt]
  have hint := (hw.pairTerm_unfold hψ0 (by linarith : -M ≤ M) hψT).1
  refine hint.congr (Eventually.of_forall fun z => ?_)
  simp [ψ, UnforcedLeray.Blueprint.pairTerm, real_inner_smul_right,
    EuclideanSpace.inner_single_right]

/-- The chart map `(t, x) ↦ (t - τ₀, e^{(t - τ₀)/2} x)` as a homeomorphism of `ℝ × ℝ³`. -/
def shiftDil (τ₀ : ℝ) : (ℝ × Space) ≃ₜ (ℝ × Space) where
  toFun s := (s.1 - τ₀, Real.exp ((s.1 - τ₀) / 2) • s.2)
  invFun p := (p.1 + τ₀, Real.exp (-(p.1 / 2)) • p.2)
  left_inv s := by
    refine Prod.ext ?_ ?_
    · simp
    · simp [smul_smul, ← Real.exp_add]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp
    · simp [smul_smul, ← Real.exp_add]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The chart field at the dilated point: `v(t, e^{t/2} y) = e^{-t/2} w(τ₀ + t, y)`. -/
theorem chartField_dil (τ₀ : ℝ) (w : ℝ → SpatialField) (t : ℝ) (y : Space) (i : Fin 3) :
    chartField τ₀ w t (Real.exp (t / 2) • y) i = Real.exp (-(t / 2)) * w (τ₀ + t) y i := by
  unfold chartField
  simp only [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul,
    PiLp.smul_apply, smul_eq_mul]

/-- Integrability of `v_i · g` for a smooth compactly supported `g` on `ℝ × ℝ³`, where
`v_i = chartField τ₀ w`. Transport by `integrable_dilChart_iff` and `integrable_shift_iff`
to `integrable_mul_coord`. -/
theorem integrable_chart_mul {P : ℝ} (hP : 0 < P) {w : ℝ → SpatialField}
    (hw : B0005.IsY2 P w) (τ₀ : ℝ) (i : Fin 3) {g : ℝ × Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    Integrable (fun p : ℝ × Space => chartField τ₀ w p.1 p.2 i * g p) := by
  have hgΘ : HasCompactSupport
      (fun s : ℝ × Space => g (s.1 - τ₀, Real.exp ((s.1 - τ₀) / 2) • s.2)) :=
    hgc.comp_homeomorph (shiftDil τ₀)
  have hΘs : ContDiff ℝ ∞ (fun s : ℝ × Space => (s.1 - τ₀, Real.exp ((s.1 - τ₀) / 2) • s.2)) := by
    fun_prop
  have hgΘs : ContDiff ℝ ∞
      (fun s : ℝ × Space => g (s.1 - τ₀, Real.exp ((s.1 - τ₀) / 2) • s.2)) :=
    hg.comp hΘs
  have hT : ContDiff ℝ ∞ (fun s : ℝ × Space =>
      Real.exp (s.1 - τ₀) * g (s.1 - τ₀, Real.exp ((s.1 - τ₀) / 2) • s.2)) := by
    have he : ContDiff ℝ ∞ (fun s : ℝ × Space => Real.exp (s.1 - τ₀)) := by fun_prop
    exact he.mul hgΘs
  have hTc : HasCompactSupport (fun s : ℝ × Space =>
      Real.exp (s.1 - τ₀) * g (s.1 - τ₀, Real.exp ((s.1 - τ₀) / 2) • s.2)) :=
    HasCompactSupport.mul_left (f := fun s : ℝ × Space => Real.exp (s.1 - τ₀)) hgΘ
  have hK := integrable_mul_coord hP hw i hT hTc
  have hK' := (B0424.integrable_shift_iff τ₀ (fun z : ℝ × Space =>
      Real.exp (z.1 - τ₀) * g (z.1 - τ₀, Real.exp ((z.1 - τ₀) / 2) • z.2) * (w z.1 z.2) i)).mpr hK
  rw [B0424.integrable_dilChart_iff]
  refine hK'.congr (Eventually.of_forall fun p => ?_)
  simp only [B0424.dilChart, add_sub_cancel_left, chartField_dil, smul_eq_mul]
  have e : Real.exp (3 * p.1 / 2) * Real.exp (-(p.1 / 2)) = Real.exp p.1 := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← e]
  ring

/-! ## The time change -/

/-- **Step W1b** (`eq:free-stress-14`): the chart equation gives the heat equation for
`u = χ v` with right-hand side `F = θ⁻¹(χ g + χ' v)`. -/
theorem windowChartTimeChange : WindowChartTimeChange := by
  unfold WindowChartTimeChange
  intro h μ P w f χ τ₀ i hh hP hw hf hχ hCE
  unfold B0423.IsWeakHeatSol
  intro Ψ hΨ
  have hχs : ContDiff ℝ ∞ χ := hχ.smooth
  have hχ's : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ.smooth).2
  have hχ'c : HasCompactSupport (deriv χ) := hχ.compact.deriv
  have hΞ : IsSTTest (B0424.timeTest χ Ψ) := B0424.isSTTest_timeTest hχs hχ.compact hΨ
  have hΦ : IsSTTest (B0424.timeTest (deriv χ) Ψ) := B0424.isSTTest_timeTest hχ's hχ'c hΨ
  have hΞtD : ∀ p : ℝ × Space, tD (B0424.timeTest χ Ψ) p =
      deriv χ p.1 * Ψ (Real.exp p.1, p.2) + χ p.1 * (Real.exp p.1 * tD Ψ (Real.exp p.1, p.2)) :=
    fun p => B0424.tD_timeTest hχs hΨ.1 p
  have hΞsL : ∀ p : ℝ × Space,
      sLap (B0424.timeTest χ Ψ) p = χ p.1 * sLap Ψ (Real.exp p.1, p.2) :=
    fun p => B0424.sLap_timeTest hχs hΨ.1 p
  have hΞval : ∀ p : ℝ × Space, B0424.timeTest χ Ψ p = χ p.1 * Ψ (Real.exp p.1, p.2) :=
    fun p => B0424.timeTest_apply χ Ψ p
  have hΦval : ∀ p : ℝ × Space,
      B0424.timeTest (deriv χ) Ψ p = deriv χ p.1 * Ψ (Real.exp p.1, p.2) :=
    fun p => B0424.timeTest_apply (deriv χ) Ψ p
  -- integrability of the three chart pieces
  have hBint : Integrable (fun p : ℝ × Space =>
      chartField τ₀ w p.1 p.2 i * B0424.timeTest (deriv χ) Ψ p) :=
    integrable_chart_mul hP hw τ₀ i hΦ.1 hΦ.2
  have hCint : Integrable (fun p : ℝ × Space =>
      (-(chartField τ₀ f p.1 p.2 i + μ * chartField τ₀ w p.1 p.2 i)) *
        B0424.timeTest χ Ψ p) := by
    have h1 := integrable_chart_mul hP hf τ₀ i hΞ.1 hΞ.2
    have h2 := integrable_chart_mul hP hw τ₀ i hΞ.1 hΞ.2
    refine ((h1.neg).sub (h2.const_mul μ)).congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  have hAint : Integrable (fun p : ℝ × Space =>
      chartField τ₀ w p.1 p.2 i *
        (-(tD (B0424.timeTest χ Ψ) p) - h * Real.exp p.1 * sLap (B0424.timeTest χ Ψ) p)) := by
    have h1 := integrable_chart_mul hP hw τ₀ i (hΞ.dirD tdir).1 (hΞ.dirD tdir).2
    have hsL : IsSTTest (sLap (B0424.timeTest χ Ψ)) := isSTTest_sLap' hΞ
    have hg2s : ContDiff ℝ ∞ (fun p : ℝ × Space => Real.exp p.1 * sLap (B0424.timeTest χ Ψ) p) :=
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × Space => Real.exp p.1)).mul hsL.1
    have hg2c : HasCompactSupport
        (fun p : ℝ × Space => Real.exp p.1 * sLap (B0424.timeTest χ Ψ) p) :=
      HasCompactSupport.mul_left (f := fun p : ℝ × Space => Real.exp p.1) hsL.2
    have h2 := integrable_chart_mul hP hw τ₀ i hg2s hg2c
    refine ((h1.neg).sub (h2.const_mul h)).congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  -- the left side: change of variables `θ = e^t` and the chain rule for `Ξ`
  have hLpw : ∫ X : PS 3, windowU χ τ₀ w i X * (-tD Ψ X - h * sLap Ψ X) =
      ∫ p : ℝ × Space,
        (chartField τ₀ w p.1 p.2 i *
            (-(tD (B0424.timeTest χ Ψ) p) - h * Real.exp p.1 * sLap (B0424.timeTest χ Ψ) p) +
          chartField τ₀ w p.1 p.2 i * B0424.timeTest (deriv χ) Ψ p) := by
    have hzero : ∀ X : PS 3, X ∉ Ioi (0 : ℝ) ×ˢ (univ : Set Space) →
        windowU χ τ₀ w i X * (-tD Ψ X - h * sLap Ψ X) = 0 := by
      intro X hX
      have hX1 : ¬ (0 < X.1) := fun h' => hX ⟨h', mem_univ _⟩
      simp [windowU, hX1]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, B0424.integral_expChart]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [B0424.expChart]
    have hlog : windowU χ τ₀ w i (Real.exp p.1, p.2) = χ p.1 * chartField τ₀ w p.1 p.2 i := by
      simp [windowU, Real.exp_pos]
    rw [hlog, hΞtD, hΞsL, hΦval]
    simp only [smul_eq_mul]
    ring
  -- the right side: the same substitution, with `windowF` and the test `Ξ`
  have hRpw : ∫ X : PS 3, windowF χ μ τ₀ w f i X * Ψ X =
      ∫ p : ℝ × Space,
        ((-(chartField τ₀ f p.1 p.2 i + μ * chartField τ₀ w p.1 p.2 i)) *
            B0424.timeTest χ Ψ p +
          chartField τ₀ w p.1 p.2 i * B0424.timeTest (deriv χ) Ψ p) := by
    have hzero : ∀ X : PS 3, X ∉ Ioi (0 : ℝ) ×ˢ (univ : Set Space) →
        windowF χ μ τ₀ w f i X * Ψ X = 0 := by
      intro X hX
      have hX1 : ¬ (0 < X.1) := fun h' => hX ⟨h', mem_univ _⟩
      simp [windowF, hX1]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, B0424.integral_expChart]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [B0424.expChart]
    have hF : windowF χ μ τ₀ w f i (Real.exp p.1, p.2) =
        (Real.exp p.1)⁻¹ * (χ p.1 * (-(chartField τ₀ f p.1 p.2 i + μ * chartField τ₀ w p.1 p.2 i)) +
          deriv χ p.1 * chartField τ₀ w p.1 p.2 i) := by
      simp [windowF, Real.exp_pos]
    have hne : Real.exp p.1 ≠ 0 := (Real.exp_pos _).ne'
    rw [hF, hΞval, hΦval]
    simp only [smul_eq_mul]
    field_simp
  -- the chart equation with the test `Ξ`
  have hAC : ∫ p : ℝ × Space,
      chartField τ₀ w p.1 p.2 i *
        (-(tD (B0424.timeTest χ Ψ) p) - h * Real.exp p.1 * sLap (B0424.timeTest χ Ψ) p) =
      ∫ p : ℝ × Space,
        (-(chartField τ₀ f p.1 p.2 i + μ * chartField τ₀ w p.1 p.2 i)) *
          B0424.timeTest χ Ψ p :=
    hCE (B0424.timeTest χ Ψ) hΞ
  rw [hLpw, hRpw, integral_add hAint hBint, integral_add hCint hBint, hAC]

end UnforcedLeray.Short.Interface
