import UnforcedLeray.Short.PartIIa.Sub.N02_4_5.Gen

/-!
# Part II-a, task `PartII-a:N02/4/5` (`NzConvDecay`): exponential decay of the Green convolution

Source of record: `the November 2 reference manuscript`, lines 1713-1722 (the one-mode
potentials are convolutions with the Green kernel `G_k(t) = -e^{-|k||t|}/(2|k|)`, so they decay like
`e^{-|k||η|}`).

Conditional theorem `nzConvDecay_of`: from the domination hypotheses `NzConvGenHyp`, the `m`-th
derivative of `nzConv k h` at `x` is the integral over `t` of `G_k(t) • iteratedFDeriv ℝ m h (x - (0, t))`.
Let `tsupport h ⊆ closedBall 0 R`. The integrand vanishes unless `|x.2 - t| ≤ R`, and on that set
`|G_k(t)| ≤ e^{|k|R} e^{-|k||x.2|}/(2|k|)` while the `m`-th derivative of `h` is bounded by `M`.
So the integrand is dominated by a constant times the indicator of `[x.2 - R, x.2 + R]`, whose integral
is `2R` times the constant. One uniform estimate, no case split on `|η|`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Shifting the second coordinate: `(x.1, x.2 - t) = x - (0, t)`. -/
theorem nzcd_shift (t : ℝ) (x : ℝ × ℝ) : (x.1, x.2 - t) = x - ((0 : ℝ), t) := by
  ext <;> simp

/-- The natural number `j` lies below `∞`. -/
theorem nzcd_le (j : ℕ) : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- The `j`-th derivative of `x ↦ G_k(t) h(x.1, x.2 - t)` at `p` is
`G_k(t) • (iteratedFDeriv ℝ j h)(p - (0, t))`. -/
theorem nzcd_iter (k : ℝ) (h : ℝ × ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (j : ℕ) (t : ℝ) (p : ℝ × ℝ) :
    iteratedFDeriv ℝ j (fun x : ℝ × ℝ => (nzGreen k t : ℂ) * h (x.1, x.2 - t)) p
      = (nzGreen k t : ℂ) • iteratedFDeriv ℝ j h (p - ((0 : ℝ), t)) := by
  have hfun : (fun x : ℝ × ℝ => (nzGreen k t : ℂ) * h (x.1, x.2 - t))
      = fun x : ℝ × ℝ => (nzGreen k t : ℂ) • h (x - ((0 : ℝ), t)) := by
    funext x
    rw [nzcd_shift t x, smul_eq_mul]
  have hsub : ContDiff ℝ ∞ (fun z : ℝ × ℝ => z - ((0 : ℝ), t)) :=
    contDiff_id.sub contDiff_const
  have hcd : ContDiffAt ℝ j (fun z : ℝ × ℝ => h (z - ((0 : ℝ), t))) p :=
    ((hh.comp hsub).of_le (nzcd_le j)).contDiffAt
  rw [hfun, iteratedFDeriv_const_smul_apply' hcd, iteratedFDeriv_comp_sub]

/-- The norm of the Green constant: `‖G_k(t)‖ = e^{-|k||t|}/(2|k|)` for `k ≠ 0`. -/
theorem nzcd_norm_green (k t : ℝ) (hk : k ≠ 0) :
    ‖(nzGreen k t : ℂ)‖ = Real.exp (-|k| * |t|) / (2 * |k|) := by
  have hκ : 0 < |k| := abs_pos.mpr hk
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold nzGreen
  rw [abs_div, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos (mul_pos two_pos hκ)]

/-- Every derivative of `h` vanishes outside a closed ball containing `tsupport h`. -/
theorem nzcd_iter_zero (h : ℝ × ℝ → ℂ) (R : ℝ) (hR : tsupport h ⊆ Metric.closedBall 0 R)
    (m : ℕ) (y : ℝ × ℝ) (hy : R < ‖y‖) :
    iteratedFDeriv ℝ m h y = 0 := by
  by_contra hne
  have hsub : Function.support (iteratedFDeriv ℝ m h) ⊆ tsupport h :=
    support_iteratedFDeriv_subset m
  have hmem : y ∈ Function.support (iteratedFDeriv ℝ m h) := hne
  have hts : y ∈ tsupport h := hsub hmem
  have hball := hR hts
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  linarith

/-- **`NzConvDecay` from `NzConvGenHyp`: exponential decay of the Green convolution and its
derivatives.** Conditional theorem; one uniform estimate with the constant `2R M e^{|k|R}/(2|k|)`. -/
theorem nzConvDecay_of (hG : NzConvGenHyp) : NzConvDecay := by
  intro k hk h hh hcs m
  have hGH := hG k hk h hh hcs
  have hκ : 0 < |k| := abs_pos.mpr hk
  -- a radius `R ≥ 0` with `tsupport h ⊆ closedBall 0 R`
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ tsupport h ⊆ Metric.closedBall 0 R := by
    obtain ⟨R0, hR0⟩ := (hcs.isCompact.isBounded).subset_closedBall (0 : ℝ × ℝ)
    exact ⟨max R0 0, le_max_right _ _,
      hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  -- a uniform bound on the `m`-th derivative of `h`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ m h y‖ ≤ M :=
    (hh.continuous_iteratedFDeriv (nzcd_le m)).bounded_above_of_compact_support
      (hcs.iteratedFDeriv m)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  refine ⟨2 * R * (M * Real.exp (|k| * R) / (2 * |k|)), ?_⟩
  intro x
  -- differentiation under the integral sign
  have key : iteratedFDeriv ℝ m (nzConv k h) x
      = ∫ t : ℝ, iteratedFDeriv ℝ m (fun y : ℝ × ℝ => (nzGreen k t : ℂ) * h (y.1, y.2 - t)) x
          ∂volume :=
    ParamIntegralSmoothAux.pm_deriv_formula m ℂ ℝ volume
      (fun (t : ℝ) (y : ℝ × ℝ) => (nzGreen k t : ℂ) * h (y.1, y.2 - t)) hGH x
  -- the pointwise majorant
  have hpt : ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun y : ℝ × ℝ => (nzGreen k t : ℂ) * h (y.1, y.2 - t)) x‖
        ≤ (Set.Icc (x.2 - R) (x.2 + R)).indicator
            (fun _ : ℝ => M * Real.exp (|k| * R) / (2 * |k|) * Real.exp (-|k| * |x.2|)) t := by
    intro t
    rw [nzcd_iter k h hh, norm_smul]
    by_cases ht : t ∈ Set.Icc (x.2 - R) (x.2 + R)
    · rw [Set.indicator_of_mem ht]
      have hnz := nzcd_norm_green k t hk
      have hit := hM (x - ((0 : ℝ), t))
      have hexp : Real.exp (-|k| * |t|) ≤ Real.exp (|k| * R) * Real.exp (-|k| * |x.2|) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h1 : |x.2| ≤ |t| + |x.2 - t| := by
          have := abs_add_le t (x.2 - t)
          rwa [show t + (x.2 - t) = x.2 by ring] at this
        have h2 : |x.2 - t| ≤ R := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
        have hx : |x.2| ≤ |t| + R := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hx hκ.le]
      calc ‖(nzGreen k t : ℂ)‖ * ‖iteratedFDeriv ℝ m h (x - ((0 : ℝ), t))‖
          ≤ ‖(nzGreen k t : ℂ)‖ * M := mul_le_mul_of_nonneg_left hit (norm_nonneg _)
        _ = Real.exp (-|k| * |t|) / (2 * |k|) * M := by rw [hnz]
        _ ≤ (Real.exp (|k| * R) * Real.exp (-|k| * |x.2|)) / (2 * |k|) * M :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hexp (by positivity)) hM0
        _ = M * Real.exp (|k| * R) / (2 * |k|) * Real.exp (-|k| * |x.2|) := by ring
    · rw [Set.indicator_of_notMem ht, nzcd_iter_zero h R hR m _ ?_]
      · simp
      · have h2 : R < |x.2 - t| := by
          by_contra hc
          obtain ⟨h1, h1'⟩ := abs_le.mp (not_lt.mp hc)
          exact ht ⟨by linarith, by linarith⟩
        have h3 := norm_snd_le (x - ((0 : ℝ), t))
        have h4 : (x - ((0 : ℝ), t)).2 = x.2 - t := by simp
        rw [h4, Real.norm_eq_abs] at h3
        linarith
  -- the majorant is integrable
  have hint : Integrable
      ((Set.Icc (x.2 - R) (x.2 + R)).indicator
        (fun _ : ℝ => M * Real.exp (|k| * R) / (2 * |k|) * Real.exp (-|k| * |x.2|))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc
  rw [key]
  calc ‖∫ t : ℝ, iteratedFDeriv ℝ m (fun y : ℝ × ℝ => (nzGreen k t : ℂ) * h (y.1, y.2 - t)) x
          ∂volume‖
      ≤ ∫ t : ℝ, (Set.Icc (x.2 - R) (x.2 + R)).indicator
          (fun _ : ℝ => M * Real.exp (|k| * R) / (2 * |k|) * Real.exp (-|k| * |x.2|)) t ∂volume :=
        norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)
    _ = volume.real (Set.Icc (x.2 - R) (x.2 + R))
          • (M * Real.exp (|k| * R) / (2 * |k|) * Real.exp (-|k| * |x.2|)) :=
        integral_indicator_const _ measurableSet_Icc
    _ = 2 * R * (M * Real.exp (|k| * R) / (2 * |k|)) * Real.exp (-|k| * |x.2|) := by
        rw [Real.volume_real_Icc_of_le (show x.2 - R ≤ x.2 + R by linarith), smul_eq_mul]
        ring

end UnforcedLeray.Short.PartIIa
