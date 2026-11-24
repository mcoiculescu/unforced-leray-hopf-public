import UnforcedLeray.Short.PartIIb.Sub.T15_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1975-1979
(weak product rule in the `H_2` measure; logarithmic chart `s = e^t`).

From a `LogTest c Φ` build the original test
`φ(s, y) = s^{1/4} Φ(log s, y)` for `s > 0` and `φ(s, y) = 0` for `s ≤ 0`.
It is smooth, `c`-periodic, vanishes for `s < e^{-T}`, `s > e^{T}` and `|η| > L`,
satisfies `φ(e^t, y) = e^{t/4} Φ(t, y)`, and
`e^t ∂_s φ(e^t, y) = e^{t/4} (Φ/4 + ∂_t Φ)(t, y)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The transported test `φ(s, y) = s^{1/4} Φ(log s, y)` for `s > 0`, and `0` for `s ≤ 0`. -/
def origTestOfLogFn (Φ : Coord → ℝ) (x : Coord) : ℝ :=
  if 0 < x.1 then x.1 ^ (1 / 4 : ℝ) * Φ (Real.log x.1, x.2) else 0

/-- Derivative along the first coordinate line through `(p, y)`: `v ↦ F(v, y)` at `v = p`. -/
theorem origTest_hasDerivAt_fst {F : Coord → ℝ} {p : ℝ} {y : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F (p, y)) :
    HasDerivAt (fun v : ℝ => F (v, y)) (cpd 0 F (p, y)) p := by
  have hline : HasDerivAt (fun v : ℝ => ((v, y) : Coord)) (cdir 0) p := by
    have h1 : HasDerivAt (fun v : ℝ => v) 1 p := hasDerivAt_id' p
    have h2 : HasDerivAt (fun _ : ℝ => y) 0 p := hasDerivAt_const _ _
    have h3 := h1.prodMk h2
    rw [show cdir 0 = (1, 0) by simp [cdir]]
    exact h3
  exact hF.hasFDerivAt.comp_hasDerivAt_of_eq p hline (by simp)

theorem origTest_rpow_quarter (t : ℝ) : Real.exp t ^ (1 / 4 : ℝ) = Real.exp (t / 4) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
  congr 1
  ring

/-- Vanishing for `s < e^{-T}` (then `log s < -T`). -/
theorem origTest_zero_of_lt {Φ : Coord → ℝ} {T L : ℝ}
    (hΦc : ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → Φ x = 0)
    {x : Coord} (hx : x.1 < Real.exp (-T)) : origTestOfLogFn Φ x = 0 := by
  by_cases h : 0 < x.1
  · have hlog : Real.log x.1 < -T := by
      have h' := Real.log_lt_log h hx
      rwa [Real.log_exp] at h'
    have h1 : T < |Real.log x.1| := lt_of_lt_of_le (by linarith) (neg_le_abs _)
    simp [origTestOfLogFn, h, hΦc (Real.log x.1, x.2) (Or.inl h1)]
  · simp [origTestOfLogFn, h]

/-- Vanishing for `s > e^{T}` (then `log s > T`). -/
theorem origTest_zero_of_gt {Φ : Coord → ℝ} {T L : ℝ}
    (hΦc : ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → Φ x = 0)
    {x : Coord} (hx : Real.exp T < x.1) : origTestOfLogFn Φ x = 0 := by
  have h : 0 < x.1 := lt_trans (Real.exp_pos T) hx
  have hlog : T < Real.log x.1 := by
    have h' := Real.log_lt_log (Real.exp_pos T) hx
    rwa [Real.log_exp] at h'
  have h1 : T < |Real.log x.1| := lt_of_lt_of_le hlog (le_abs_self _)
  simp [origTestOfLogFn, h, hΦc (Real.log x.1, x.2) (Or.inl h1)]

/-- Vanishing for `|η| > L`. -/
theorem origTest_zero_of_L {Φ : Coord → ℝ} {T L : ℝ}
    (hΦc : ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → Φ x = 0)
    {x : Coord} (hx : L < |x.2.2|) : origTestOfLogFn Φ x = 0 := by
  by_cases h : 0 < x.1
  · simp [origTestOfLogFn, h, hΦc (Real.log x.1, x.2) (Or.inr hx)]
  · simp [origTestOfLogFn, h]

/-- Smoothness of the transported test on all of `Coord`. -/
theorem origTest_contDiff {c : ℝ} {Φ : Coord → ℝ} (hΦ : LogTest c Φ) :
    ContDiff ℝ ∞ (origTestOfLogFn Φ) := by
  obtain ⟨T, L, hc⟩ := hΦ.compact
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x.1
  · have hne : x.1 ≠ 0 := hx.ne'
    have h1 : ContDiffAt ℝ ∞ (fun y : Coord => y.1 ^ (1 / 4 : ℝ)) x :=
      (Real.contDiffAt_rpow_const_of_ne (n := ∞) (p := 1 / 4) hne).comp x contDiffAt_fst
    have hm : ContDiffAt ℝ ∞ (fun y : Coord => (Real.log y.1, y.2)) x :=
      ((Real.contDiffAt_log.2 hne).comp x contDiffAt_fst).prodMk contDiffAt_snd
    have h2 : ContDiffAt ℝ ∞ (fun y : Coord => Φ (Real.log y.1, y.2)) x :=
      hΦ.smooth.contDiffAt.comp x hm
    have hopen : IsOpen {y : Coord | 0 < y.1} := isOpen_lt continuous_const continuous_fst
    have hev : origTestOfLogFn Φ =ᶠ[𝓝 x]
        (fun y : Coord => y.1 ^ (1 / 4 : ℝ) * Φ (Real.log y.1, y.2)) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      have hy' : (0 : ℝ) < y.1 := hy
      simp [origTestOfLogFn, hy']
    exact (h1.mul h2).congr_of_eventuallyEq hev
  · have hlt : x.1 < Real.exp (-T) := lt_of_le_of_lt (not_lt.1 hx) (Real.exp_pos _)
    have hopen : IsOpen {y : Coord | y.1 < Real.exp (-T)} := isOpen_lt continuous_fst continuous_const
    have hev : origTestOfLogFn Φ =ᶠ[𝓝 x] (fun _ : Coord => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hlt] with y hy
      exact origTest_zero_of_lt hc hy
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- Periodicity: `qShift` does not change `s`, `log s`, `η`, and `Φ` is periodic. -/
theorem origTest_periodic {c : ℝ} {Φ : Coord → ℝ} (hΦ : LogTest c Φ) :
    ∀ x : Coord, origTestOfLogFn Φ (qShift c x) = origTestOfLogFn Φ x := by
  intro x
  have h := hΦ.periodic (Real.log x.1, x.2)
  simp only [qShift] at h
  simp only [origTestOfLogFn, qShift]
  by_cases hx : 0 < x.1
  · simp [hx, h]
  · simp [hx]

/-- Support: vanishing for `s < e^{-T}`, `s > e^{T}` and `|η| > L`. -/
theorem origTest_support {c : ℝ} {Φ : Coord → ℝ} (hΦ : LogTest c Φ) :
    ∃ σ H L : ℝ, 0 < σ ∧
      ∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → origTestOfLogFn Φ x = 0 := by
  obtain ⟨T, L, hc⟩ := hΦ.compact
  refine ⟨Real.exp (-T), Real.exp T, L, Real.exp_pos _, ?_⟩
  rintro x (h | h | h)
  · exact origTest_zero_of_lt hc h
  · exact origTest_zero_of_gt hc h
  · exact origTest_zero_of_L hc h

/-- The identity `φ(e^t, y) = e^{t/4} Φ(t, y)`. -/
theorem origTest_exp {Φ : Coord → ℝ} (x : Coord) :
    origTestOfLogFn Φ (Real.exp x.1, x.2) = Real.exp (x.1 / 4) * Φ x := by
  have hs : (0 : ℝ) < Real.exp x.1 := Real.exp_pos _
  simp only [origTestOfLogFn, hs, ↓reduceIte, Real.log_exp, origTest_rpow_quarter]

/-- The derivative identity `e^t ∂_s φ(e^t, y) = e^{t/4} (Φ/4 + ∂_t Φ)(t, y)`. -/
theorem origTest_deriv {c : ℝ} {Φ : Coord → ℝ} (hΦ : LogTest c Φ) (x : Coord) :
    Real.exp x.1 * cpd 0 (origTestOfLogFn Φ) (Real.exp x.1, x.2) =
      Real.exp (x.1 / 4) * (Φ x / 4 + cpd 0 Φ x) := by
  have hs : (0 : ℝ) < Real.exp x.1 := Real.exp_pos _
  have hφd : DifferentiableAt ℝ (origTestOfLogFn Φ) (Real.exp x.1, x.2) :=
    ((origTest_contDiff hΦ).differentiable (by simp)).differentiableAt
  have hl := origTest_hasDerivAt_fst (p := Real.exp x.1) (y := x.2) hφd
  have hΦd : DifferentiableAt ℝ Φ (Real.log (Real.exp x.1), x.2) :=
    (hΦ.smooth.differentiable (by simp)).differentiableAt
  have hlΦ : HasDerivAt (fun u : ℝ => Φ (u, x.2)) (cpd 0 Φ (Real.log (Real.exp x.1), x.2))
      (Real.log (Real.exp x.1)) :=
    origTest_hasDerivAt_fst (p := Real.log (Real.exp x.1)) (y := x.2) hΦd
  have hlog : HasDerivAt Real.log (Real.exp x.1)⁻¹ (Real.exp x.1) :=
    Real.hasDerivAt_log hs.ne'
  have hB : HasDerivAt (fun v : ℝ => Φ (Real.log v, x.2))
      (cpd 0 Φ (Real.log (Real.exp x.1), x.2) * (Real.exp x.1)⁻¹) (Real.exp x.1) :=
    HasDerivAt.comp (Real.exp x.1) hlΦ hlog
  have hA : HasDerivAt (fun v : ℝ => v ^ (1 / 4 : ℝ))
      ((1 / 4 : ℝ) * Real.exp x.1 ^ ((1 / 4 : ℝ) - 1)) (Real.exp x.1) :=
    Real.hasDerivAt_rpow_const (Or.inl hs.ne')
  have hG := hA.mul hB
  have hev : (fun v : ℝ => origTestOfLogFn Φ (v, x.2)) =ᶠ[𝓝 (Real.exp x.1)]
      (fun v : ℝ => v ^ (1 / 4 : ℝ) * Φ (Real.log v, x.2)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hs] with v hv
    have hv' : (0 : ℝ) < v := hv
    simp [origTestOfLogFn, hv']
  have hcpd := hl.unique (hG.congr_of_eventuallyEq hev)
  rw [hcpd]
  simp only [Real.log_exp, Prod.mk.eta]
  rw [Real.rpow_sub_one hs.ne', origTest_rpow_quarter]
  have hs' : Real.exp x.1 ≠ 0 := hs.ne'
  field_simp

/-- **Leaf `PartII-b:T15/2/4`**: from a logarithmic test `Φ`, the transported function
`φ(s, y) = s^{1/4} Φ(log s, y)` (`s > 0`), `0` (`s ≤ 0`), is an original periodic test with the
stated identities. -/
theorem origTestOfLog : UnforcedLeray.Short.IIb.OrigTestOfLog := by
  intro c Φ hΦ
  exact ⟨origTestOfLogFn Φ, origTest_contDiff hΦ, origTest_periodic hΦ, origTest_support hΦ,
    fun x => origTest_exp x, fun x => origTest_deriv hΦ x⟩

end UnforcedLeray.Short.IIb
