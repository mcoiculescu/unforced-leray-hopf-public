import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_7

/-!
# `PartII-b:T13/1/7/4` the scalar window estimate

Source: `the November 2 reference manuscript` lines 1928-1933. Proves `WbdScalar`
from the cut-off properties, the window heat equation, the cylinder estimates, the interpolation,
the window data, the transfer of weak derivatives and the window norms.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-- Multiplication by the `s`-coordinate preserves `q`-periodicity. -/
theorem wbds_qper_mul {c : ℝ} {Dt : Coord → ℂ} (h : QPeriodicS c Dt) :
    QPeriodicS c (fun x => (x.1 : ℂ) * Dt x) := by
  unfold QPeriodicS at h ⊢
  filter_upwards [h] with x hx
  show ((x.1 : ℝ) : ℂ) * Dt (qShift c x) = ((x.1 : ℝ) : ℂ) * Dt x
  rw [hx]

/-- Multiplication by the `s`-coordinate preserves measurability. -/
theorem wbds_meas_mul {Dt : Coord → ℂ} (h : AEStronglyMeasurable Dt volume) :
    AEStronglyMeasurable (fun x : Coord => (x.1 : ℂ) * Dt x) volume :=
  ((Complex.measurable_ofReal.comp measurable_fst).aestronglyMeasurable).mul h

/-- A nonzero complex constant multiple of a function with finite `L^p` norm has finite norm. -/
theorem wbds_lt_top_of_const_mul {ν : ℝ} (hν : 0 < ν) {g : Coord → ℂ} {p : ℝ≥0∞}
    {μ : Measure Coord} (h : eLpNorm (fun x => (ν : ℂ) * g x) p μ < ⊤) :
    eLpNorm g p μ < ⊤ := by
  have e : (fun x => (ν : ℂ) * g x) = (ν : ℂ) • g := by
    funext x
    simp [smul_eq_mul]
  rw [e, eLpNorm_const_smul] at h
  have hne : ‖(ν : ℂ)‖ₑ ≠ 0 := by
    rw [enorm_ne_zero]
    exact_mod_cast hν.ne'
  rcases ENNReal.mul_lt_top_iff.mp h with h1 | h1 | h1
  · exact h1.2
  · exact absurd h1 hne
  · rw [h1]
    exact ENNReal.zero_lt_top

theorem wbdScalar_of (h1 : UnforcedLeray.Short.IIb.WinCutProps) (h2 : UnforcedLeray.Short.IIb.WindowHeatEq) (h3 : UnforcedLeray.Short.IIb.CylHeatMaxReg) (h4 : UnforcedLeray.Short.IIb.CylGradInterp) (h5 : UnforcedLeray.Short.IIb.WindowWeightCompare) (hD : UnforcedLeray.Short.IIb.WbdData) (hT : UnforcedLeray.Short.IIb.WbdTransfer) (hN : UnforcedLeray.Short.IIb.WbdNorms) : UnforcedLeray.Short.IIb.WbdScalar := by
  intro r h1r h3r μ
  obtain ⟨M, hM0, hM⟩ := h1
  obtain ⟨C, hC, hCp⟩ := h3 r h1r
  obtain ⟨Ci, hCi, hCip⟩ := h4 r h1r
  obtain ⟨K0, hK0, hKp⟩ := hN r M h1r h3r hM0 μ C Ci hC hCi
  refine ⟨K0, hK0, ?_⟩
  intro ν c hν hc G b hG hb hF a ha i
  have hD' := hD M hM0 hM h5 c r hc h1r h3r μ G b hG hb a ha i
  obtain ⟨huP, hfP, huM, hfM, huF, hfF, huB, hfB⟩ := hD'
  have heat := h2 c r ν μ hc h1r hν G b hG hb hF a ha i
  obtain ⟨Dt, D2, ⟨hDtP, hDtM⟩, hD2P, hDtφ, hD2φ, hDtN, hD2N⟩ :=
    hCp ν c hν hc _ _ huP hfP huM hfM huF hfF heat
  have hD2F : ∀ i j, eLpNorm (D2 i j) (ENNReal.ofReal r) (cylMeas c) < ⊤ := fun i j =>
    wbds_lt_top_of_const_mul hν (lt_of_le_of_lt (hD2N i j)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfF))
  have hDtF : eLpNorm Dt (ENNReal.ofReal r) (cylMeas c) < ⊤ :=
    lt_of_le_of_lt hDtN (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfF)
  obtain ⟨D1, hD1P, hD1φ, hD1N⟩ := hCip c hc _ D2 huP huM huF
    (fun i j => ⟨(hD2P i j).1, (hD2P i j).2, hD2F i j⟩) hD2φ
  have hD1F : ∀ j, eLpNorm (D1 j) (ENNReal.ofReal r) (cylMeas c) < ⊤ := by
    intro j
    refine lt_of_le_of_lt (hD1N j 1 one_pos) ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top huF,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_⟩
    exact ENNReal.sum_lt_top.2 fun k _ => ENNReal.sum_lt_top.2 fun l _ => hD2F k l
  have hT' := hT M hM c r hc h1r μ G b hG hb a ha i Dt D1
    ⟨hDtP, hDtM, hDtF⟩ (fun j => ⟨(hD1P j).1, (hD1P j).2, hD1F j⟩) hDtφ hD1φ
  have hK := hKp ν c a hν hc ha G b (fun x => windowProfile a b x i)
    (fun x => windowSource a μ G b x i) Dt D2 D1 hDtM (fun j => (hD1P j).2) huB hfB hDtN
    (fun i j => hD2N i j) hD1N h5
  refine ⟨fun x => (x.1 : ℂ) * Dt x, D1 0, D1 1, hT'.1, hT'.2.1, hT'.2.2,
    ⟨wbds_qper_mul hDtP, wbds_meas_mul hDtM⟩, ⟨(hD1P 0).1, (hD1P 0).2⟩,
    ⟨(hD1P 1).1, (hD1P 1).2⟩, hK.1, hK.2 0, hK.2 1⟩

end UnforcedLeray.Short.IIb
