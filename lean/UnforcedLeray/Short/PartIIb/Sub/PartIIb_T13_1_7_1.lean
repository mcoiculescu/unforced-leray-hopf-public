import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_7

/-!
# Part II-b, task `PartII-b:T13/1/7/1` (`wbdData`): decomposition

Source: `the November 2 reference manuscript` lines 1928-1933.

`WbdData` splits as: periodicity (proved here, `wbdd_per`), a.e. strong measurability of the
window data (`WbdDMeas`), the two weighted bounds (`WbdDBound`, given the measurability), and
the finiteness statements, which follow from the bounds (proved here).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-- **Measurability of the window data.** `u = χ_a b_i`, `f = windowSource a μ G b i` are
`AEStronglyMeasurable` for `volume`. Reason: `b, G ∈ H_r` are strongly measurable for
`hMeas c r = ageμ c (r/2-5/2)` (a measure on `s > 0` equivalent to `volume` there); by
`exists_periodic_rep` (`Tasks/FlatCausal/DuhamelMeasurable/Periodic.lean`) each equals a
`q`-periodic strongly measurable representative a.e. on `s > 0`. `winCut a s = 0` for
`s < a/2` and `deriv (winCut a) s = 0` there (`tsupport (winCut a) ⊆ Icc (a/2) (4a)`), so `u, f`
vanish for `s ≤ a/2` and agree a.e. with the corresponding functions of the representatives
(`winCut a x.1 / x.1` is continuous on `s > 0`, `deriv (winCut a)` is continuous). -/
def WbdDMeas : Prop :=
  ∀ M : ℝ, 0 ≤ M → WinCutBd M → ∀ (c r : ℝ), 0 < c → 1 < r → r < 3 →
    ∀ (μ : ℂ) (G b : CProf), InHr c r G → InHr c r b → ∀ a : ℝ, 0 < a → ∀ i : Fin 2,
      AEStronglyMeasurable (fun x => windowProfile a b x i) volume ∧
      AEStronglyMeasurable (fun x => windowSource a μ G b x i) volume

/-- **The two weighted bounds** (SP 1931-1933), given measurability. Pointwise
`|winCut a x.1| ≤ 1`, `|winCut a x.1 / x.1| ≤ 2/a` (it vanishes for `x.1 < a/2`),
`|deriv (winCut a) x.1| ≤ M/a = (2/a)(M/2)`, and both `u, f` vanish outside `winSet2 a`;
so `‖u i x‖ ≤ ‖b x‖ 1_{winSet2 a}` and
`‖f i x‖ ≤ (2/a)(‖G x‖ + (‖μ‖ + M/2) ‖b x‖) 1_{winSet2 a}`. Hence
`eLpNorm _ (cylMeas c) = eLpNorm _ ((cylMeas c).restrict (winSet2 a))`
(`eLpNorm_restrict_eq_of_support_subset`), then apply the SECOND inequality of
`WindowWeightCompare` (it needs `volume`-measurable `b`, `G`: replace them by the periodic
representatives of `exists_periodic_rep`, which agree with them `hMeas`-a.e., so the `hNormOn`
and the windowed functions are unchanged a.e.; with `A = winSet2 a`, the function `b`, resp. `G`, `b`; the sum/scalar
multiples via `eLpNorm_add_le`, `eLpNorm_const_smul`, `eLpNorm_mono_ae`; component bound
`‖v i‖ ≤ ‖v‖`). -/
def WbdDBound : Prop :=
  ∀ M : ℝ, 0 ≤ M → WinCutBd M → WindowWeightCompare → ∀ (c r : ℝ), 0 < c → 1 < r → r < 3 →
    ∀ (μ : ℂ) (G b : CProf), InHr c r G → InHr c r b → ∀ a : ℝ, 0 < a → ∀ i : Fin 2,
      AEStronglyMeasurable (fun x => windowProfile a b x i) volume →
      AEStronglyMeasurable (fun x => windowSource a μ G b x i) volume →
      ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm (fun x => windowProfile a b x i) (ENNReal.ofReal r) (cylMeas c) ≤
        16 * hNormOn c r (winSet2 a) b ∧
      ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm (fun x => windowSource a μ G b x i) (ENNReal.ofReal r) (cylMeas c) ≤
        ENNReal.ofReal (32 / a) * (hNormOn c r (winSet2 a) G +
          ENNReal.ofReal (‖μ‖ + M / 2) * hNormOn c r (winSet2 a) b)

theorem wbdd_per (c : ℝ) (μ : ℂ) (G b : CProf) (a : ℝ) (i : Fin 2) (ha : 0 < a)
    (hG : QPeriodic c G) (hb : QPeriodic c b) :
    QPeriodicS c (fun x => windowProfile a b x i) ∧
      QPeriodicS c (fun x => windowSource a μ G b x i) := by
  -- `QPeriodic` holds on `s > 0` only; there `χ_a` and `χ_a'` vanish for `s ≤ 0` (`a > 0`)
  have hcut0 : ∀ t : ℝ, t < a / 2 → winCut a t = 0 := by
    intro t ht
    unfold winCut winCut1
    have h1 : 2 * (t / a) - 1 ≤ 0 := by
      have : t / a < 1 / 2 := by rw [div_lt_iff₀ ha]; linarith
      linarith
    rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]
  have hd0 : ∀ t : ℝ, t ≤ 0 → deriv (winCut a) t = 0 := by
    intro t ht
    have hev : winCut a =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (show t < a / 2 by linarith)] with u hu
      exact hcut0 u hu
    rw [hev.deriv_eq, deriv_const]
  constructor
  · filter_upwards [QPerHalf.ae_imp hb] with x hx
    have e : (qShift c x).1 = x.1 := rfl
    by_cases hx0 : 0 < x.1
    · simp only [windowProfile, e, hx hx0]
    · have hx1 : x.1 < a / 2 := by linarith [not_lt.1 hx0]
      simp [windowProfile, e, hcut0 x.1 hx1]
  · filter_upwards [QPerHalf.ae_imp hG, QPerHalf.ae_imp hb] with x hxG hxb
    by_cases hx0 : 0 < x.1
    · have h1 : G (qShift c x) = G x := hxG hx0
      have h2 : b (qShift c x) = b x := hxb hx0
      simp only [windowSource, qShift] at h1 h2 ⊢
      rw [h1, h2]
    · have hx1 : x.1 < a / 2 := by linarith [not_lt.1 hx0]
      simp [windowSource, qShift, hcut0 x.1 hx1, hd0 x.1 (not_lt.1 hx0)]

/-- Finiteness from a bound `w * N ≤ K < ⊤`, `w ≠ 0`. -/
theorem wbdd_fin {w N K : ℝ≥0∞} (hw : w ≠ 0) (hK : K < ⊤) (h : w * N ≤ K) : N < ⊤ := by
  by_contra hN
  rw [not_lt, top_le_iff] at hN
  rw [hN, ENNReal.mul_top hw] at h
  exact absurd (lt_of_le_of_lt h hK) (lt_irrefl _)

theorem wbdData_of (hM : WbdDMeas) (hB : WbdDBound) : WbdData := by
  intro M hM0 hcut hW c r hc h1 h3 μ G b hG hb a ha i
  obtain ⟨hum, hfm⟩ := hM M hM0 hcut c r hc h1 h3 μ G b hG hb a ha i
  obtain ⟨h7, h8⟩ := hB M hM0 hcut hW c r hc h1 h3 μ G b hG hb a ha i hum hfm
  obtain ⟨hp1, hp2⟩ := wbdd_per c μ G b a i ha hG.periodic hb.periodic
  have hw : ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos ha _)).ne'
  have hNb : hNormOn c r (winSet2 a) b < ⊤ :=
    lt_of_le_of_lt (eLpNorm_mono_measure _ Measure.restrict_le_self) hb.finite
  have hNG : hNormOn c r (winSet2 a) G < ⊤ :=
    lt_of_le_of_lt (eLpNorm_mono_measure _ Measure.restrict_le_self) hG.finite
  refine ⟨hp1, hp2, hum, hfm, ?_, ?_, h7, h8⟩
  · exact wbdd_fin hw (ENNReal.mul_lt_top (by simp) hNb) h7
  · exact wbdd_fin hw (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.mpr ⟨hNG, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hNb⟩)) h8

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.wbdData_of
