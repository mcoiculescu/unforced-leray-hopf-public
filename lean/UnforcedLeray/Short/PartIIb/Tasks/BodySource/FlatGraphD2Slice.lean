import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound
import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8.FlatPoly
import UnforcedLeray.Short.PartIIb.Org.QPeriodicHalfSpace.Basic

/-!
# Part II-b, task `PartII-b:F5/1`: global second-order free graph slice bound (`FlatGraphD2Slice`)

Source of record: `the November 2 reference manuscript` (SP), lines 2224-2227 and
1923-1938:
  `‖b_0‖_{H_p} + ‖√(νs) Db_0‖_{H_p} + ‖νs D²b_0‖_{H_p} ≤ C ‖F‖_{H_p}`
at `r = bgp = 11/4`, `μ = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-! ## Local second-order weak derivative transfer on a dyadic window -/

/-- Directional vector field `vQ0` (`j = 0`) or `vEta` (`j = 1`). -/
def vDir : Fin 2 → Coord → Fin 3 → ℝ
  | ⟨0, _⟩ => vQ0
  | ⟨1, _⟩ => vEta

theorem vDir_smooth (j : Fin 2) : ∀ k, ContDiff ℝ ∞ (fun x : Coord => vDir j x k) := by
  fin_cases j
  · exact fw_vQ0_smooth
  · exact fw_vEta_smooth

theorem wb_ct_vDir (j : Fin 2) (φ : Coord → ℝ) (x : Coord) :
    coordTranspose (vDir j) dZero φ x = -cpd j.succ φ x := by
  fin_cases j
  · exact wb_ct_Q φ x
  · exact wb_ct_E φ x

theorem wb_cpd_stTest (k : Fin 3) {φ : Coord → ℝ} (hφ : IsSTTestCoord φ) :
    IsSTTestCoord (cpd k φ) := by
  refine ⟨?_, (wb_cpd_prop k φ hφ).2.1⟩
  unfold cpd
  exact (hφ.smooth.fderiv_right (by simp)).clm_apply contDiff_const

/-- Transfer the second-order cylinder heat identity to a local first-order weak derivative
identity `HasWeakFOOn (winOpen a) (vDir j) dZero (D1 i) (D2 i j)` on the window. -/
theorem wbdTransfer_D2 {c r a : ℝ} (hc : 0 < c) (hr : 1 < r) {u : Coord → ℂ}
    {D1 : Fin 2 → Coord → ℂ} {D2 : Fin 2 → Fin 2 → Coord → ℂ}
    (hD1 : ∀ i, QPeriodicS c (D1 i) ∧ AEStronglyMeasurable (D1 i) volume ∧
      eLpNorm (D1 i) (ENNReal.ofReal r) (cylMeas c) < ⊤)
    (hD2 : ∀ i j, QPeriodicS c (D2 i j) ∧ AEStronglyMeasurable (D2 i j) volume ∧
      eLpNorm (D2 i j) (ENNReal.ofReal r) (cylMeas c) < ⊤)
    (hD1φ : ∀ (i : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
      ∫ x, u x * (cpd i.succ φ x : ℂ) = -∫ x, D1 i x * (φ x : ℂ))
    (hD2φ : ∀ (i j : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
      ∫ x, u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, D2 i j x * (φ x : ℂ))
    (i j : Fin 2) :
    HasWeakFOOn (winOpen a) (vDir j) dZero (D1 i) (D2 i j) := by
  have hloc1 : LocallyIntegrable (D1 i) volume :=
    mollLoc_proof c r hc hr (D1 i) (hD1 i).1 (hD1 i).2.1 (hD1 i).2.2
  have hloc2 : LocallyIntegrable (D2 i j) volume :=
    mollLoc_proof c r hc hr (D2 i j) (hD2 i j).1 (hD2 i j).2.1 (hD2 i j).2.2
  intro φ hφ _hsub
  have hφ_st : IsSTTestCoord φ := ⟨hφ.smooth, hφ.compact⟩
  obtain ⟨hc1, hc2, _⟩ := wb_cpd_prop j.succ φ hφ_st
  have hTeq : coordTranspose (vDir j) dZero φ = fun x => -cpd j.succ φ x :=
    funext (wb_ct_vDir j φ)
  refine ⟨?_, ?_, ?_⟩
  · rw [hTeq]
    exact wb_int_loc (D1 i) hloc1 (fun x => -cpd j.succ φ x) hc1.neg hc2.neg
  · exact wb_int_loc (D2 i j) hloc2 φ hφ.smooth.continuous hφ.compact
  · have h1 := hD1φ i (fun y => cpd j.succ φ y) (wb_cpd_stTest j.succ hφ_st)
    have h2 := hD2φ i j φ hφ_st
    rw [h2] at h1
    rw [h1]
    simp_rw [wb_ct_vDir j φ, Complex.ofReal_neg, mul_neg, integral_neg]

/-! ## Scalar and vector window bounds including `ν s D² b` -/

theorem wbdScalar_with_D2 (r : ℝ) (h1r : 1 < r) (h3r : r < 3) :
    ∃ M C Ci : ℝ, 0 ≤ M ∧ 0 < C ∧ 0 < Ci ∧
      ∀ (μ : ℂ) (ν c : ℝ), 0 < ν → 0 < c →
      ∀ G b : CProf, InHr c r G → InHr c r b → FullFlatEq ν μ G b → ∀ a : ℝ, 0 < a →
      ∀ m : Fin 2, ∃ (T P Q : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ),
        HasWeakFOOn (winOpen a) vS dZero (fun x => b x m) T ∧
        HasWeakFOOn (winOpen a) vQ0 dZero (fun x => b x m) P ∧
        HasWeakFOOn (winOpen a) vEta dZero (fun x => b x m) Q ∧
        (∀ j, HasWeakFOOn (winOpen a) (vDir j) dZero P (D2 0 j)) ∧
        (∀ j, HasWeakFOOn (winOpen a) (vDir j) dZero Q (D2 1 j)) ∧
        (QPeriodicS c T ∧ AEStronglyMeasurable T volume) ∧
        (QPeriodicS c P ∧ AEStronglyMeasurable P volume) ∧
        (QPeriodicS c Q ∧ AEStronglyMeasurable Q volume) ∧
        (∀ i j, QPeriodicS c (D2 i j) ∧ AEStronglyMeasurable (D2 i j) volume) ∧
        eLpNorm T (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
          ENNReal.ofReal (flatK0Fn M C Ci μ) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
        ENNReal.ofReal (Real.sqrt ν) *
            eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * P x) (ENNReal.ofReal r)
              ((hMeas c r).restrict (winOpen a)) ≤
          ENNReal.ofReal (flatK0Fn M C Ci μ) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
        ENNReal.ofReal (Real.sqrt ν) *
            eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * Q x) (ENNReal.ofReal r)
              ((hMeas c r).restrict (winOpen a)) ≤
          ENNReal.ofReal (flatK0Fn M C Ci μ) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
        (∀ i j, ENNReal.ofReal ν *
            eLpNorm (fun x => (x.1 : ℂ) * D2 i j x) (ENNReal.ofReal r)
              ((hMeas c r).restrict (winOpen a)) ≤
          ENNReal.ofReal (flatK0Fn M C Ci μ) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b)) := by
  obtain ⟨M, hM0, hM⟩ := winCutProps
  obtain ⟨C, hC, hCp⟩ := cylHeatMaxReg r h1r
  obtain ⟨Ci, hCi, hCip⟩ := cylGradInterp r h1r
  refine ⟨M, C, Ci, hM0, hC, hCi, fun μ ν c hν hc G b hG hb hF a ha m => ?_⟩
  have hD' := wbdData M hM0 hM windowWeightCompare c r hc h1r h3r μ G b hG hb a ha m
  obtain ⟨huP, hfP, huM, hfM, huF, hfF, huB, hfB⟩ := hD'
  have heat := (windowHeatEq_of winCutProps) c r ν μ hc h1r hν G b hG hb hF a ha m
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
  have hT' := wbdTransfer M hM c r hc h1r μ G b hG hb a ha m Dt D1
    ⟨hDtP, hDtM, hDtF⟩ (fun j => ⟨(hD1P j).1, (hD1P j).2, hD1F j⟩) hDtφ hD1φ
  have hTD2 : ∀ i j, HasWeakFOOn (winOpen a) (vDir j) dZero (D1 i) (D2 i j) := fun i j =>
    wbdTransfer_D2 hc h1r (fun k => ⟨(hD1P k).1, (hD1P k).2, hD1F k⟩)
      (fun k l => ⟨(hD2P k l).1, (hD2P k l).2, hD2F k l⟩) hD1φ hD2φ i j
  have hQ : 0 ≤ ‖μ‖ + M / 2 := by have := norm_nonneg μ; linarith
  have hR : 0 ≤ 512 * Ci + 4096 * Ci * C * (1 + (‖μ‖ + M / 2)) := by
    have : 0 ≤ 4096 * Ci * C * (1 + (‖μ‖ + M / 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCi.le) hC.le) (by linarith)
    linarith
  have hpos1 : 0 < 1024 * C * (1 + (‖μ‖ + M / 2)) :=
    mul_pos (mul_pos (by norm_num) hC) (by linarith)
  have hK1 : eLpNorm (fun x => (x.1 : ℂ) * Dt x) (ENNReal.ofReal r)
      ((hMeas c r).restrict (winOpen a)) ≤
      ENNReal.ofReal (flatK0Fn M C Ci μ) *
        (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := by
    refine (wbdn_part1 windowWeightCompare hc h1r h3r ha hC.le hQ G b hDtM hfB hDtN).trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by unfold flatK0Fn; linarith)) _
  have hK2 : ∀ j : Fin 2, ENNReal.ofReal (Real.sqrt ν) *
      eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * D1 j x) (ENNReal.ofReal r)
        ((hMeas c r).restrict (winOpen a)) ≤
      ENNReal.ofReal (flatK0Fn M C Ci μ) *
        (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := by
    intro j
    refine (wbdn_part2 hc h1r h3r ha hν hCi.le hC.le hQ windowWeightCompare G b
      (hD1P j).2 huB hfB hD2N (hD1N j)).trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by unfold flatK0Fn; linarith)) _
  have hKD2 : ∀ i j : Fin 2, ENNReal.ofReal ν *
      eLpNorm (fun x => (x.1 : ℂ) * D2 i j x) (ENNReal.ofReal r)
        ((hMeas c r).restrict (winOpen a)) ≤
      ENNReal.ofReal (flatK0Fn M C Ci μ) *
        (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := by
    intro i j
    rw [← wbdn_nu_mul hν.le]
    have heq : (fun x : Coord => (ν : ℂ) * ((x.1 : ℂ) * D2 i j x)) =
        (fun x : Coord => (x.1 : ℂ) * ((ν : ℂ) * D2 i j x)) := by
      funext x; ring
    rw [heq]
    have hmν : AEStronglyMeasurable (fun x : Coord => (ν : ℂ) * D2 i j x) volume :=
      (hD2P i j).2.const_mul (ν : ℂ)
    refine (wbdn_part1 windowWeightCompare hc h1r h3r ha hC.le hQ G b hmν hfB (hD2N i j)).trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by unfold flatK0Fn; linarith)) _
  exact ⟨fun x => (x.1 : ℂ) * Dt x, D1 0, D1 1, D2, hT'.1, hT'.2.1, hT'.2.2,
    fun j => hTD2 0 j, fun j => hTD2 1 j,
    ⟨wbds_qper_mul hDtP, wbds_meas_mul hDtM⟩, ⟨(hD1P 0).1, (hD1P 0).2⟩,
    ⟨(hD1P 1).1, (hD1P 1).2⟩, hD2P, hK1, hK2 0, hK2 1, hKD2⟩

theorem windowBound_with_D2 (r : ℝ) (h1 : 1 < r) (h3 : r < 3) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ν c : ℝ), 0 < ν → 0 < c →
      ∀ G b : CProf, InHr c r G → InHr c r b → FullFlatEq ν 0 G b →
      ∃ (S Q E : ℝ → CProf) (D2w : ℝ → Fin 2 → Fin 2 → CProf), ∀ a : ℝ, 0 < a →
        HasWeakVecOn (winOpen a) vS dZero b (S a) ∧
        HasWeakVecOn (winOpen a) vQ0 dZero b (Q a) ∧
        HasWeakVecOn (winOpen a) vEta dZero b (E a) ∧
        (∀ j, HasWeakVecOn (winOpen a) (vDir j) dZero (Q a) (D2w a 0 j)) ∧
        (∀ j, HasWeakVecOn (winOpen a) (vDir j) dZero (E a) (D2w a 1 j)) ∧
        (QPeriodic c (S a) ∧ AEStronglyMeasurable (S a) volume) ∧
        (QPeriodic c (Q a) ∧ AEStronglyMeasurable (Q a) volume) ∧
        (QPeriodic c (E a) ∧ AEStronglyMeasurable (E a) volume) ∧
        (∀ i j, QPeriodic c (D2w a i j) ∧ AEStronglyMeasurable (D2w a i j) volume) ∧
        hNormOn c r (winOpen a) (S a) ≤
          ENNReal.ofReal K * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
        ENNReal.ofReal (Real.sqrt ν) * hNormOn c r (winOpen a) (sqrtS (Q a)) ≤
          ENNReal.ofReal K * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
        ENNReal.ofReal (Real.sqrt ν) * hNormOn c r (winOpen a) (sqrtS (E a)) ≤
          ENNReal.ofReal K * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
        (∀ i j, ENNReal.ofReal ν * hNormOn c r (winOpen a) (mulS (D2w a i j)) ≤
          ENNReal.ofReal K * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b)) := by
  classical
  obtain ⟨M, C, Ci, hM, hC, hCi, hK⟩ := wbdScalar_with_D2 r h1 h3
  set K0 := flatK0Fn M C Ci 0
  have hK0 : 0 < K0 := flatK0Fn_pos hM hC hCi 0
  refine ⟨2 * K0, mul_pos (by norm_num) hK0, fun ν c hν hc G b hG hb hF => ?_⟩
  have H : ∀ (a : ℝ) (m : Fin 2),
      ∃ (T P Q : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ), 0 < a →
      (HasWeakFOOn (winOpen a) vS dZero (fun x => b x m) T ∧
      HasWeakFOOn (winOpen a) vQ0 dZero (fun x => b x m) P ∧
      HasWeakFOOn (winOpen a) vEta dZero (fun x => b x m) Q ∧
      (∀ j, HasWeakFOOn (winOpen a) (vDir j) dZero P (D2 0 j)) ∧
      (∀ j, HasWeakFOOn (winOpen a) (vDir j) dZero Q (D2 1 j)) ∧
      (QPeriodicS c T ∧ AEStronglyMeasurable T volume) ∧
      (QPeriodicS c P ∧ AEStronglyMeasurable P volume) ∧
      (QPeriodicS c Q ∧ AEStronglyMeasurable Q volume) ∧
      (∀ i j, QPeriodicS c (D2 i j) ∧ AEStronglyMeasurable (D2 i j) volume) ∧
      eLpNorm T (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      ENNReal.ofReal (Real.sqrt ν) *
          eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * P x) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      ENNReal.ofReal (Real.sqrt ν) *
          eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * Q x) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      (∀ i j, ENNReal.ofReal ν *
          eLpNorm (fun x => (x.1 : ℂ) * D2 i j x) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b))) := by
    intro a m
    by_cases ha : 0 < a
    · obtain ⟨T, P, Q, D2, hh⟩ := hK 0 ν c hν hc G b hG hb hF a ha m
      exact ⟨T, P, Q, D2, fun _ => hh⟩
    · exact ⟨0, 0, 0, 0, fun h => absurd h ha⟩
  choose T P Q D2 hTPQ using H
  refine ⟨fun a => wbdVec (fun m => T a m), fun a => wbdVec (fun m => P a m),
    fun a => wbdVec (fun m => Q a m), fun a i j => wbdVec (fun m => D2 a m i j),
    fun a ha => ?_⟩
  have hh : ∀ m, _ := fun m => hTPQ a m ha
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1.le
  set RHS := hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b
  have hmeas : ∀ (F : Fin 2 → Coord → ℂ), (∀ m, AEStronglyMeasurable (F m) volume) →
      ∀ m, AEStronglyMeasurable (F m) ((hMeas c r).restrict (winOpen a)) := fun F hF m =>
    (hF m).mono_ac ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
      (ageμ_ac_volume c (r / 2 - 5 / 2)))
  have two : ENNReal.ofReal (2 * K0) = ENNReal.ofReal K0 + ENNReal.ofReal K0 := by
    rw [two_mul, ENNReal.ofReal_add hK0.le hK0.le]
  have key : ∀ (F : Fin 2 → Coord → ℂ) (w : ℝ≥0∞), (∀ m, AEStronglyMeasurable (F m) volume) →
      (∀ m, w * eLpNorm (F m) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * RHS) →
      w * eLpNorm (wbdVec F) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal (2 * K0) * RHS := by
    intro F w hF hb
    calc w * eLpNorm (wbdVec F) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a))
        ≤ w * (eLpNorm (F 0) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) +
            eLpNorm (F 1) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a))) :=
          by gcongr; exact wbdVec_eLpNorm_le hp1 (hmeas F hF)
      _ = w * eLpNorm (F 0) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) +
            w * eLpNorm (F 1) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) := mul_add _ _ _
      _ ≤ ENNReal.ofReal K0 * RHS + ENNReal.ofReal K0 * RHS := add_le_add (hb 0) (hb 1)
      _ = ENNReal.ofReal (2 * K0) * RHS := by rw [two, add_mul]
  have hsq : ∀ (F : Fin 2 → Coord → ℂ), sqrtS (wbdVec F) =
      wbdVec (fun m x => (Real.sqrt x.1 : ℂ) * F m x) := by
    intro F; funext x; ext m; simp [sqrtS, wbdVec]
  have hmul : ∀ (F : Fin 2 → Coord → ℂ), mulS (wbdVec F) =
      wbdVec (fun m x => (x.1 : ℂ) * F m x) := by
    intro F; funext x; ext m; simp [mulS, wbdVec]
  have hsqm : ∀ (F : Fin 2 → Coord → ℂ), (∀ m, AEStronglyMeasurable (F m) volume) →
      ∀ m, AEStronglyMeasurable (fun x : Coord => (Real.sqrt x.1 : ℂ) * F m x) volume := by
    intro F hF m
    exact (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_fst)
      ).aestronglyMeasurable.mul (hF m)
  have hmulm : ∀ (F : Fin 2 → Coord → ℂ), (∀ m, AEStronglyMeasurable (F m) volume) →
      ∀ m, AEStronglyMeasurable (fun x : Coord => (x.1 : ℂ) * F m x) volume := by
    intro F hF m
    exact (Complex.measurable_ofReal.comp measurable_fst).aestronglyMeasurable.mul (hF m)
  refine ⟨fun m => (hh m).1, fun m => (hh m).2.1, fun m => (hh m).2.2.1,
    fun j m => (hh m).2.2.2.1 j, fun j m => (hh m).2.2.2.2.1 j,
    ⟨wbdVec_per (fun m => (hh m).2.2.2.2.2.1.1), wbdVec_aesm (fun m => (hh m).2.2.2.2.2.1.2)⟩,
    ⟨wbdVec_per (fun m => (hh m).2.2.2.2.2.2.1.1), wbdVec_aesm (fun m => (hh m).2.2.2.2.2.2.1.2)⟩,
    ⟨wbdVec_per (fun m => (hh m).2.2.2.2.2.2.2.1.1),
      wbdVec_aesm (fun m => (hh m).2.2.2.2.2.2.2.1.2)⟩,
    fun i j => ⟨wbdVec_per (fun m => ((hh m).2.2.2.2.2.2.2.2.1 i j).1),
      wbdVec_aesm (fun m => ((hh m).2.2.2.2.2.2.2.2.1 i j).2)⟩,
    ?_, ?_, ?_, ?_⟩
  · have := key (fun m => T a m) 1 (fun m => (hh m).2.2.2.2.2.1.2) (fun m => by
      simpa using (hh m).2.2.2.2.2.2.2.2.2.1)
    simpa [hNormOn] using this
  · have := key (fun m x => (Real.sqrt x.1 : ℂ) * P a m x) (ENNReal.ofReal (Real.sqrt ν))
      (hsqm _ (fun m => (hh m).2.2.2.2.2.2.1.2)) (fun m => (hh m).2.2.2.2.2.2.2.2.2.2.1)
    rw [hNormOn, hsq]; exact this
  · have := key (fun m x => (Real.sqrt x.1 : ℂ) * Q a m x) (ENNReal.ofReal (Real.sqrt ν))
      (hsqm _ (fun m => (hh m).2.2.2.2.2.2.2.1.2)) (fun m => (hh m).2.2.2.2.2.2.2.2.2.2.2.1)
    rw [hNormOn, hsq]; exact this
  · intro i j
    have := key (fun m x => (x.1 : ℂ) * D2 a m i j x) (ENNReal.ofReal ν)
      (hmulm _ (fun m => ((hh m).2.2.2.2.2.2.2.2.1 i j).2))
      (fun m => (hh m).2.2.2.2.2.2.2.2.2.2.2.2 i j)
    rw [hNormOn, hmul]; exact this

/-! ## Helpers for `mulS`, congruence of local/global weak derivatives, and slice norms -/

theorem qPeriodic_mulS {c : ℝ} {g : CProf} (h : QPeriodic c g) : QPeriodic c (mulS g) := by
  filter_upwards [h] with x hx
  simp only [mulS, qShift] at hx ⊢
  rw [hx]

theorem aestronglyMeasurable_mulS {m : Measure Coord} {g : CProf}
    (h : AEStronglyMeasurable g m) : AEStronglyMeasurable (mulS g) m := by
  have hs : AEStronglyMeasurable (fun x : Coord => (x.1 : ℂ)) m :=
    (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable
  exact hs.smul h

theorem fw_mulS_ae {a : ℝ} {f g : CProf}
    (h : ∀ᵐ x ∂(volume : Measure Coord), x ∈ winOpen a → f x = g x) :
    ∀ᵐ x ∂(volume : Measure Coord), x ∈ winOpen a → mulS f x = mulS g x := by
  filter_upwards [h] with x hx hmem
  simp only [mulS, hx hmem]

/-- `HasWeakVecOn` depends on the base profile only through its values a.e. on the window. -/
theorem hasWeakVecOn_congr_left {a : ℝ} ( j : Fin 2 ) {u u' g : CProf}
    (hu : ∀ᵐ x ∂(volume : Measure Coord), x ∈ winOpen a → u' x = u x)
    (hw : HasWeakVecOn (winOpen a) (vDir j) dZero u g) :
    HasWeakVecOn (winOpen a) (vDir j) dZero u' g := by
  intro m φ hφ hsub
  obtain ⟨hi1, hi2, heq⟩ := hw m φ hφ hsub
  have hae : (fun x => u' x m * (coordTranspose (vDir j) dZero φ x : ℂ)) =ᵐ[volume]
      (fun x => u x m * (coordTranspose (vDir j) dZero φ x : ℂ)) := by
    filter_upwards [hu] with x hx
    by_cases hts : x ∈ tsupport φ
    · rw [hx (hsub hts)]
    · rw [wb_ct_vDir j φ x, wb_cpd_zero j.succ φ x hts]
      simp
  exact ⟨hi1.congr hae.symm, hi2, heq.trans (integral_congr_ae hae.symm)⟩

/-- `HasWeakVec` depends on both arguments only through their `volume`-a.e. values on `s > 0`. -/
theorem hasWeakVec_congr {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u u' g g' : CProf}
    (hu : ∀ᵐ x : Coord, 0 < x.1 → u' x = u x)
    (hg : ∀ᵐ x : Coord, 0 < x.1 → g' x = g x)
    (hw : HasWeakVec v d u g) : HasWeakVec v d u' g' := by
  have hw1 : HasWeakVec v d u' g := fun m =>
    CongrHelp.hasWeakFO_congr (by filter_upwards [hu] with x hx hp; rw [hx hp]) (hw m)
  intro m
  refine ⟨fun φ hφ => ⟨((hw1 m).1 φ hφ).1, ?_⟩, fun φ hφ => ?_⟩
  · refine (((hw1 m).1 φ hφ).2).congr ?_
    filter_upwards [hg] with x hx
    by_cases hp : 0 < x.1
    · simp [hx hp]
    · have hxt : x ∉ tsupport φ := fun h => hp (hφ.supp h).1
      simp [image_eq_zero_of_notMem_tsupport hxt]
  · rw [← (hw1 m).2 φ hφ]
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    by_cases hp : 0 < x.1
    · simp [hx hp]
    · have hxt : x ∉ tsupport φ := fun h => hp (hφ.supp h).1
      simp [image_eq_zero_of_notMem_tsupport hxt]

/-- Upgrading an `AEStronglyMeasurable _ volume`, `QPeriodic` profile to a `StronglyMeasurable`
representative that agrees with it `volume`-a.e. everywhere. -/
theorem exists_sm_rep_vol {c : ℝ} {g : CProf} (hp : QPeriodic c g)
    (hm : AEStronglyMeasurable g volume) :
    ∃ g' : CProf, StronglyMeasurable g' ∧ QPeriodic c g' ∧ (g' =ᵐ[volume] g) := by
  refine ⟨hm.mk g, hm.stronglyMeasurable_mk, ?_, hm.ae_eq_mk.symm⟩
  have h1 : ∀ᵐ x : Coord, hm.mk g (qShift c x) = g (qShift c x) := by
    rw [CongrHelp.qShift_eq]
    exact (CongrHelp.mp_T c 1).quasiMeasurePreserving.ae hm.ae_eq_mk.symm
  filter_upwards [ae_restrict_of_ae h1, hp, ae_restrict_of_ae hm.ae_eq_mk.symm] with x hx1 hx2 hx3
  exact hx1.trans (hx2.trans hx3.symm)

/-- Upgrading an `InHr c bgp` profile `b0` to a `StronglyMeasurable` representative `b0'` in
`InHr c bgp` that agrees with `b0` `volume`-a.e. on `s > 0`. -/
theorem exists_sm_rep_inHr {c : ℝ} (hc : 0 < c) {b0 : CProf} (hb0 : InHr c bgp b0) :
    ∃ b0' : CProf, StronglyMeasurable b0' ∧ InHr c bgp b0' ∧
      (b0' =ᵐ[hMeas c bgp] b0) ∧ (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) := by
  obtain ⟨b1, hsm1, hae1⟩ := exists_periodic_rep hc hb0.periodic hb0.meas
  set b0' : CProf := fun x => if 0 < x.1 then b1 x else 0
  have hsm : StronglyMeasurable b0' :=
    hsm1.ite (measurableSet_Ioi.preimage measurable_fst) stronglyMeasurable_const
  have hae : ∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x := by
    filter_upwards [hae1] with x hx hp
    simp only [b0', hp, ↓reduceIte, (hx hp).symm]
  have hae_h : b0' =ᵐ[hMeas c bgp] b0 := by
    have h_vol : ∀ᵐ x ∂(hMeas c bgp), 0 < x.1 → b0' x = b0 x :=
      (fw_hMeas_ac c bgp).ae_le hae
    filter_upwards [h_vol, ageμ_ae_pos c (bgp / 2 - 5 / 2)] with x hx hp
    exact hx hp
  have hper : QPeriodic c b0' := by
    have hae_shift : ∀ᵐ x : Coord, 0 < (qShift c x).1 → b0' (qShift c x) = b0 (qShift c x) := by
      rw [CongrHelp.qShift_eq]
      exact (CongrHelp.mp_T c 1).quasiMeasurePreserving.ae hae
    refine QPerHalf.of_ae ?_
    filter_upwards [hae, hae_shift, QPerHalf.ae_imp hb0.periodic] with x hx1 hx2 hxp
    by_cases hp : 0 < x.1
    · have hp' : 0 < (qShift c x).1 := hp
      rw [hx2 hp', hxp hp, hx1 hp]
    · have hp' : ¬ 0 < (qShift c x).1 := hp
      simp [b0', hp, hp']
  refine ⟨b0', hsm, ⟨hper, hsm.aestronglyMeasurable, ?_⟩, hae_h, hae⟩
  rw [hNorm, eLpNorm_congr_ae hae_h]
  exact hb0.finite

/-! ## Slice `L^p` measurability and Bochner `sLpNorm` bounds from `hNorm c bgp` -/

theorem hMeas_bgp_eq_prod (c : ℝ) :
    hMeas c bgp = (sMeas (-9 / 8)).prod (UnforcedLeray.Cyl.avgμ c) := by
  unfold hMeas Axi.ageμ sMeas
  have hexp : bgp / 2 - 5 / 2 = -9 / 8 := by norm_num [bgp]
  rw [hexp]

theorem sliceLpNorm_eq_lintegral (c : ℝ) (u : CProf) (s : ℝ) :
    sliceLpNorm c u s =
      (∫⁻ z, ‖u (s, z)‖ₑ ^ bgp ∂UnforcedLeray.Cyl.avgμ c) ^ (4 / 11 : ℝ) := by
  unfold sliceLpNorm
  have hp0 : ENNReal.ofReal bgp ≠ 0 := by norm_num [bgp]
  have hpt : ENNReal.ofReal bgp ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hto : (ENNReal.ofReal bgp).toReal = bgp :=
    ENNReal.toReal_ofReal (by norm_num [bgp])
  have hinv : 1 / bgp = (4 / 11 : ℝ) := by norm_num [bgp]
  rw [hto, hinv]

theorem measurable_sliceLpNorm (c : ℝ) {u : CProf} (hu : StronglyMeasurable u) :
    Measurable (sliceLpNorm c u) := by
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := sfinite_avgμ c
  have h1 : Measurable (fun x : Coord => ‖u x‖ₑ ^ bgp) :=
    (hu.measurable.enorm).pow_const bgp
  have h2 : Measurable (fun s : ℝ => ∫⁻ z, ‖u (s, z)‖ₑ ^ bgp ∂UnforcedLeray.Cyl.avgμ c) :=
    h1.lintegral_prod_right'
  have h3 : sliceLpNorm c u =
      fun s => (∫⁻ z, ‖u (s, z)‖ₑ ^ bgp ∂UnforcedLeray.Cyl.avgμ c) ^ (4 / 11 : ℝ) :=
    funext (sliceLpNorm_eq_lintegral c u)
  rw [h3]
  exact h2.pow_const (4 / 11 : ℝ)

theorem sLpNorm_sliceLpNorm_le_hNorm (c T : ℝ) {u : CProf} (hu : StronglyMeasurable u) :
    sLpNorm (-9 / 8) T (sliceLpNorm c u) ≤ hNorm c bgp u := by
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := sfinite_avgμ c
  unfold sLpNorm hNorm
  have hp0 : ENNReal.ofReal bgp ≠ 0 := by norm_num [bgp]
  have hpt : ENNReal.ofReal bgp ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hto : (ENNReal.ofReal bgp).toReal = bgp :=
    ENNReal.toReal_ofReal (by norm_num [bgp])
  have hinv : 1 / bgp = (4 / 11 : ℝ) := by norm_num [bgp]
  rw [hto, hinv]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hpow : ∀ s : ℝ,
      sliceLpNorm c u s ^ bgp = ∫⁻ z, ‖u (s, z)‖ₑ ^ bgp ∂UnforcedLeray.Cyl.avgμ c := by
    intro s
    rw [sliceLpNorm_eq_lintegral, ← ENNReal.rpow_mul]
    have hmul : (4 / 11 : ℝ) * bgp = 1 := by norm_num [bgp]
    rw [hmul, ENNReal.rpow_one]
  simp_rw [hpow]
  refine (setLIntegral_le_lintegral _ _).trans ?_
  have hm : Measurable (fun x : Coord => ‖u x‖ₑ ^ bgp) :=
    (hu.measurable.enorm).pow_const bgp
  rw [hMeas_bgp_eq_prod c, lintegral_prod _ hm.aemeasurable]

theorem sliceLpNorm_sqrtS (c : ℝ) (u : CProf) (s : ℝ) :
    sliceLpNorm c (sqrtS u) s = ENNReal.ofReal (Real.sqrt s) * sliceLpNorm c u s := by
  unfold sliceLpNorm sqrtS
  have heq : (fun z : ℝ × ℝ => (Real.sqrt s : ℂ) • u (s, z)) =
      (Real.sqrt s : ℂ) • (fun z : ℝ × ℝ => u (s, z)) := rfl
  rw [heq, eLpNorm_const_smul]
  have hn : ‖(Real.sqrt s : ℂ)‖ₑ = ENNReal.ofReal (Real.sqrt s) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg s)]
  rw [hn]

theorem sliceLpNorm_mulS (c : ℝ) (u : CProf) {s : ℝ} (hs : 0 ≤ s) :
    sliceLpNorm c (mulS u) s = ENNReal.ofReal s * sliceLpNorm c u s := by
  unfold sliceLpNorm mulS
  have heq : (fun z : ℝ × ℝ => (s : ℂ) • u (s, z)) =
      (s : ℂ) • (fun z : ℝ × ℝ => u (s, z)) := rfl
  rw [heq, eLpNorm_const_smul]
  have hn : ‖(s : ℂ)‖ₑ = ENNReal.ofReal s := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hs]
  rw [hn]

theorem sLpNorm_sqrtS_sliceLpNorm_le (c T : ℝ) {u : CProf} (hu : StronglyMeasurable u) :
    sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm c u s) ≤
      hNorm c bgp (sqrtS u) := by
  have heq : (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm c u s) =
      sliceLpNorm c (sqrtS u) := funext fun s => (sliceLpNorm_sqrtS c u s).symm
  rw [heq]
  have hsm : StronglyMeasurable (sqrtS u) :=
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst)).stronglyMeasurable.smul hu
  exact sLpNorm_sliceLpNorm_le_hNorm c T hsm

theorem sLpNorm_mulS_sliceLpNorm_le (c T : ℝ) {u : CProf} (hu : StronglyMeasurable u) :
    sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal s * sliceLpNorm c u s) ≤
      hNorm c bgp (mulS u) := by
  have hcongr : sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal s * sliceLpNorm c u s) =
      sLpNorm (-9 / 8) T (sliceLpNorm c (mulS u)) := by
    unfold sLpNorm
    congr 1
    have hsm_mul : StronglyMeasurable (mulS u) :=
      (Complex.continuous_ofReal.comp continuous_fst).stronglyMeasurable.smul hu
    have hm1 : Measurable (fun s : ℝ => (ENNReal.ofReal s * sliceLpNorm c u s) ^ bgp) := by
      have := measurable_sliceLpNorm c hu; fun_prop
    have hm2 : Measurable (fun s : ℝ => sliceLpNorm c (mulS u) s ^ bgp) := by
      have := measurable_sliceLpNorm c hsm_mul; fun_prop
    rw [hardyL1_sMeas_Ioc (-9 / 8) T _ hm1, hardyL1_sMeas_Ioc (-9 / 8) T _ hm2]
    refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [sliceLpNorm_mulS c u hs.1.le]
  rw [hcongr]
  have hsm_mul : StronglyMeasurable (mulS u) :=
    (Complex.continuous_ofReal.comp continuous_fst).stronglyMeasurable.smul hu
  exact sLpNorm_sliceLpNorm_le_hNorm c T hsm_mul

/-! ## Proof of `FlatGraphD2Slice` (`PartII-b:F5/1`) -/

/-- **Target of `PartII-b:F5/1`**: global second-order free graph slice bound at `r = bgp = 11/4`,
`μ = 0`. -/
theorem flatGraphD2Slice_proof : UnforcedLeray.Short.IIb.FlatGraphD2Slice := by
  obtain ⟨CL, hCL, hL⟩ := flatLerayLiftOfSlice cylinderHelmholtzLr bgp bgp_gt_one bgp_lt_three
  obtain ⟨K, hK, hWK⟩ := windowBound_with_D2 bgp bgp_gt_one bgp_lt_three
  have ha : 0 < (0 : ℂ).re + (3 / bgp - 1) / 2 := bgp_gap_pos
  set A : ℝ := CL / ((0 : ℂ).re + (3 / bgp - 1) / 2) with hA
  set B : ℝ := CL + A with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact div_nonneg hCL.le ha.le
  have hB0 : 0 ≤ B := by rw [hB]; exact add_nonneg hCL.le hA0
  have hK4 : 0 ≤ 4 * K := mul_nonneg (by norm_num) hK.le
  have hKB : 0 ≤ 4 * K * B := mul_nonneg hK4 hB0
  set C_tot : ℝ := A + 4 * K * B + 1
  have hC_tot : 0 < C_tot := by positivity
  refine ⟨C_tot, hC_tot, fun ν c T hν hc _hT F b0 hF hbc0 hb0 => ?_⟩
  obtain ⟨G, hGH, hGn, hGs, hGp⟩ := hL c hc F hF
  have hbm := duhamelMeasurable bgp bgp_gt_one bgp_lt_three 0 ha ν c hν hc G hGH
  have hbn := duhamelBound bgp bgp_gt_one bgp_lt_three 0 ha ν c hν hc G hGH
  have hbper := duhamelPeriodic ν 0 c G hc hGH.periodic
  have hbH : InHr c bgp (flatDuhamel ν 0 G) :=
    ⟨hbper, hbm, lt_of_le_of_lt hbn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGH.finite)⟩
  have hbs := duhamelSolenoidal bgp bgp_gt_one bgp_lt_three 0 ha ν c hν hc G hGH hGs hbH
  have hresp : IsFlatResponse ν 0 F (flatDuhamel ν 0 G) := by
    refine ⟨hbs, fun Ψ hΨ => ?_⟩
    obtain ⟨hi1, hi2, he⟩ := duhamelEquation bgp bgp_gt_one bgp_lt_three 0 ha ν c hν hc G hGH hbH Ψ hΨ
    obtain ⟨hj1, hj2⟩ := hGp Ψ hΨ
    have hsplit := cdot_eq_add_sub F G Ψ
    refine ⟨hi1, ?_, ?_⟩
    · rw [hsplit]; exact hi2.add hj1
    · rw [hsplit, integral_add hi2 hj1, hj2, add_zero]; exact he
  have hfull := duhamelFullEq bgp bgp_gt_one bgp_lt_three 0 ha ν c hν hc G hGH hbH
  set b := flatDuhamel ν 0 G
  have hbF : hNorm c bgp b ≤ ENNReal.ofReal A * hNorm c bgp F := by
    calc hNorm c bgp b ≤ ENNReal.ofReal (1 / ((0 : ℂ).re + (3 / bgp - 1) / 2)) * hNorm c bgp G := hbn
      _ ≤ ENNReal.ofReal (1 / ((0 : ℂ).re + (3 / bgp - 1) / 2)) * (ENNReal.ofReal CL * hNorm c bgp F) := by
          gcongr
      _ = ENNReal.ofReal A * hNorm c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (one_div_pos.mpr ha).le, hA]
          congr 2; ring
  have hP : ENNReal.ofReal (4 * K) * (hNorm c bgp G + hNorm c bgp b) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c bgp F := by
    have hGbF : hNorm c bgp G + hNorm c bgp b ≤ ENNReal.ofReal B * hNorm c bgp F := by
      rw [hB, ENNReal.ofReal_add hCL.le hA0, add_mul]
      exact add_le_add hGn hbF
    calc ENNReal.ofReal (4 * K) * (hNorm c bgp G + hNorm c bgp b)
        ≤ ENNReal.ofReal (4 * K) * (ENNReal.ofReal B * hNorm c bgp F) := by gcongr
      _ = ENNReal.ofReal (4 * K * B) * hNorm c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hK4]
  have hPfin : ENNReal.ofReal (4 * K * B) * hNorm c bgp F < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.finite
  -- Window estimates and glueing of S, Q, E
  obtain ⟨S, Q, E, D2w, hw⟩ := hWK ν c hν hc G b hGH hbH hfull
  obtain ⟨Sb, hSbw, hSbp, hSbm, hSbe⟩ := weakGlue vS fw_vS_smooth c b S
    (fun a ha' => (hw a ha').1) (fun a ha' => (hw a ha').2.2.2.2.2.1)
  obtain ⟨Qb, hQbw, hQbp, hQbm, hQbe⟩ := weakGlue vQ0 fw_vQ0_smooth c b Q
    (fun a ha' => (hw a ha').2.1) (fun a ha' => (hw a ha').2.2.2.2.2.2.1)
  obtain ⟨Eb, hEbw, hEbp, hEbm, hEbe⟩ := weakGlue vEta fw_vEta_smooth c b E
    (fun a ha' => (hw a ha').2.2.1) (fun a ha' => (hw a ha').2.2.2.2.2.2.2.1)
  -- Glueing of second derivatives D2 0 j (from Qb) and D2 1 j (from Eb)
  have hD2_0_on : ∀ j a, 0 < a → HasWeakVecOn (winOpen a) (vDir j) dZero Qb (D2w a 0 j) :=
    fun j a ha' => hasWeakVecOn_congr_left j (hQbe a ha') ((hw a ha').2.2.2.1 j)
  have hD2_1_on : ∀ j a, 0 < a → HasWeakVecOn (winOpen a) (vDir j) dZero Eb (D2w a 1 j) :=
    fun j a ha' => hasWeakVecOn_congr_left j (hEbe a ha') ((hw a ha').2.2.2.2.1 j)
  have hD2_glue : ∀ i j : Fin 2, ∃ Gl : CProf,
      HasWeakVec (vDir j) dZero (if i = 0 then Qb else Eb) Gl ∧
      QPeriodic c Gl ∧ AEStronglyMeasurable Gl volume ∧
      ∀ a : ℝ, 0 < a → ∀ᵐ x ∂(volume : Measure Coord), x ∈ winOpen a → Gl x = D2w a i j x := by
    intro i j
    fin_cases i
    · simpa using weakGlue (vDir j) (vDir_smooth j) c Qb (fun a => D2w a 0 j)
        (hD2_0_on j) (fun a ha' => (hw a ha').2.2.2.2.2.2.2.2.1 0 j)
    · simpa using weakGlue (vDir j) (vDir_smooth j) c Eb (fun a => D2w a 1 j)
        (hD2_1_on j) (fun a ha' => (hw a ha').2.2.2.2.2.2.2.2.1 1 j)
  choose D2g hD2gw hD2gp hD2gm hD2ge using hD2_glue
  -- Dyadic summation for Sb, Qb, Eb, D2g i j
  have hpos : ∀ k : ℤ, (0 : ℝ) < (2 : ℝ) ^ k := fun k => zpow_pos (by norm_num) k
  have hSk : ∀ k : ℤ, ENNReal.ofReal 1 * hNormOn c bgp (winOpen ((2 : ℝ) ^ k)) Sb ≤
      ENNReal.ofReal K * (hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [ENNReal.ofReal_one, one_mul, fw_hNormOn_congr (hSbe _ (hpos k))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2.2.1
  have hSn : hNorm c bgp Sb ≤ ENNReal.ofReal (4 * K * B) * hNorm c bgp F := by
    have h := dyadicSummation bgp c bgp_gt_one.le hc Sb G b 1 K zero_le_one hK.le
      (hSbm.mono_ac (fw_hMeas_ac c bgp)) hGH.meas hbH.meas hSk
    rw [ENNReal.ofReal_one, one_mul] at h
    exact h.trans hP
  have hQk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c bgp (winOpen ((2 : ℝ) ^ k)) (sqrtS Qb) ≤
      ENNReal.ofReal K * (hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hQbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2.2.2.1
  have hQn : ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS Qb) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c bgp F :=
    (dyadicSummation bgp c bgp_gt_one.le hc (sqrtS Qb) G b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c bgp))) hGH.meas hbH.meas
      hQk).trans hP
  have hEk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c bgp (winOpen ((2 : ℝ) ^ k)) (sqrtS Eb) ≤
      ENNReal.ofReal K * (hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hEbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2.2.2.2.1
  have hEn : ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS Eb) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c bgp F :=
    (dyadicSummation bgp c bgp_gt_one.le hc (sqrtS Eb) G b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c bgp))) hGH.meas hbH.meas
      hEk).trans hP
  have hD2k : ∀ i j : Fin 2, ∀ k : ℤ, ENNReal.ofReal ν *
      hNormOn c bgp (winOpen ((2 : ℝ) ^ k)) (mulS (D2g i j)) ≤
      ENNReal.ofReal K * (hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro i j k
    rw [fw_hNormOn_congr (fw_mulS_ae (hD2ge i j _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2.2.2.2.2 i j
  have hD2n : ∀ i j : Fin 2, ENNReal.ofReal ν * hNorm c bgp (mulS (D2g i j)) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c bgp F := fun i j =>
    (dyadicSummation bgp c bgp_gt_one.le hc (mulS (D2g i j)) G b ν K hν.le hK.le
      (aestronglyMeasurable_mulS ((hD2gm i j).mono_ac (fw_hMeas_ac c bgp))) hGH.meas hbH.meas
      (hD2k i j)).trans hP
  -- Finiteness and flat-uniqueness transfer from b to b0
  have hsq0 : ENNReal.ofReal (Real.sqrt ν) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hν)).ne'
  have hν0 : ENNReal.ofReal ν ≠ 0 := (ENNReal.ofReal_pos.2 hν).ne'
  have hQfin : hNorm c bgp (sqrtS Qb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hQn hPfin).ne hsq0
  have hEfin : hNorm c bgp (sqrtS Eb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hEn hPfin).ne hsq0
  have hD2fin : ∀ i j, hNorm c bgp (mulS (D2g i j)) < ⊤ := fun i j =>
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt (hD2n i j) hPfin).ne hν0
  have hbc : InFlatClass c bgp b :=
    ⟨hbH, Sb, Qb, Eb, hSbw, hQbw, hEbw,
      ⟨hSbp, hSbm.mono_ac (fw_hMeas_ac c bgp), lt_of_le_of_lt hSn hPfin⟩,
      ⟨qPeriodic_sqrtS hQbp, aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c bgp)), hQfin⟩,
      ⟨qPeriodic_sqrtS hEbp, aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c bgp)), hEfin⟩⟩
  have h0 : b0 - b =ᵐ[hMeas c bgp] 0 :=
    flat_unique hc hν bgp_gt_one bgp_lt_three ha (b0 - b) (flatClassSub c bgp b0 b hbc0 hbc)
      (flatResponseSub ν 0 F b0 b hb0 hresp)
  have hbb0 : b0 =ᵐ[hMeas c bgp] b := by
    filter_upwards [h0] with x hx
    exact sub_eq_zero.mp hx
  have hae_b0_b : ∀ᵐ x : Coord, 0 < x.1 → b0 x = b x :=
    CongrHelp.ae_volume_of_ageμ hc hbc0.inHr.periodic hbc.inHr.periodic hbb0
  -- Strongly measurable representatives b0', b0q, b0η, D2 i j
  obtain ⟨b0', hsm0, hb0'H, hae_b0'_h, hae_b0'⟩ := exists_sm_rep_inHr hc hbc0.inHr
  obtain ⟨b0q, hsmq, hqpq, hae_q⟩ := exists_sm_rep_vol hQbp hQbm
  obtain ⟨b0η, hsmη, hqpη, hae_η⟩ := exists_sm_rep_vol hEbp hEbm
  have hD2_sm : ∀ i j : Fin 2, ∃ d : CProf,
      StronglyMeasurable d ∧ QPeriodic c d ∧ (d =ᵐ[volume] D2g i j) :=
    fun i j => exists_sm_rep_vol (hD2gp i j) (hD2gm i j)
  choose D2 hsmD2 hqpD2 hae_D2 using hD2_sm
  have hae_qh : sqrtS b0q =ᵐ[hMeas c bgp] sqrtS Qb := by
    filter_upwards [(fw_hMeas_ac c bgp).ae_eq hae_q] with x hx
    simp [sqrtS, hx]
  have hae_ηh : sqrtS b0η =ᵐ[hMeas c bgp] sqrtS Eb := by
    filter_upwards [(fw_hMeas_ac c bgp).ae_eq hae_η] with x hx
    simp [sqrtS, hx]
  have hae_D2h : ∀ i j, mulS (D2 i j) =ᵐ[hMeas c bgp] mulS (D2g i j) := by
    intro i j
    filter_upwards [(fw_hMeas_ac c bgp).ae_eq (hae_D2 i j)] with x hx
    simp [mulS, hx]
  have hbqH : InHr c bgp (sqrtS b0q) :=
    ⟨qPeriodic_sqrtS hqpq, aestronglyMeasurable_sqrtS (hsmq.aestronglyMeasurable),
      by rw [hNorm, eLpNorm_congr_ae hae_qh]; exact hQfin⟩
  have hbηH : InHr c bgp (sqrtS b0η) :=
    ⟨qPeriodic_sqrtS hqpη, aestronglyMeasurable_sqrtS (hsmη.aestronglyMeasurable),
      by rw [hNorm, eLpNorm_congr_ae hae_ηh]; exact hEfin⟩
  have hD2H : ∀ i j, InHr c bgp (mulS (D2 i j)) := fun i j =>
    ⟨qPeriodic_mulS (hqpD2 i j), aestronglyMeasurable_mulS ((hsmD2 i j).aestronglyMeasurable),
      by rw [hNorm, eLpNorm_congr_ae (hae_D2h i j)]; exact hD2fin i j⟩
  -- Weak derivative identities for b0, b0q, b0η, D2
  have hwq : HasWeakVec vQ0 dZero b0 b0q :=
    hasWeakVec_congr hae_b0_b (by filter_upwards [hae_q] with x hx _; exact hx) hQbw
  have hwη : HasWeakVec vEta dZero b0 b0η :=
    hasWeakVec_congr hae_b0_b (by filter_upwards [hae_η] with x hx _; exact hx) hEbw
  have hw00 : HasWeakVec vQ0 dZero b0q (D2 0 0) :=
    hasWeakVec_congr (by filter_upwards [hae_q] with x hx _; exact hx)
      (by filter_upwards [hae_D2 0 0] with x hx _; exact hx) (hD2gw 0 0)
  have hw01 : HasWeakVec vEta dZero b0q (D2 0 1) :=
    hasWeakVec_congr (by filter_upwards [hae_q] with x hx _; exact hx)
      (by filter_upwards [hae_D2 0 1] with x hx _; exact hx) (hD2gw 0 1)
  have hw10 : HasWeakVec vQ0 dZero b0η (D2 1 0) :=
    hasWeakVec_congr (by filter_upwards [hae_η] with x hx _; exact hx)
      (by filter_upwards [hae_D2 1 0] with x hx _; exact hx) (hD2gw 1 0)
  have hw11 : HasWeakVec vEta dZero b0η (D2 1 1) :=
    hasWeakVec_congr (by filter_upwards [hae_η] with x hx _; exact hx)
      (by filter_upwards [hae_D2 1 1] with x hx _; exact hx) (hD2gw 1 1)
  -- Norm inequalities
  have hA_le : ENNReal.ofReal A ≤ ENNReal.ofReal C_tot :=
    ENNReal.ofReal_le_ofReal (by dsimp [C_tot]; linarith)
  have hKB_le : ENNReal.ofReal (4 * K * B) ≤ ENNReal.ofReal C_tot :=
    ENNReal.ofReal_le_ofReal (by dsimp [C_tot]; linarith)
  refine ⟨b0', b0q, b0η, D2, hae_b0', hb0'H, hbqH, hbηH, hD2H,
    hsm0, hsmq, hsmη, hsmD2, hwq, hwη, hw00, hw01, hw10, hw11,
    measurable_sliceLpNorm c hsm0, measurable_sliceLpNorm c hsmq,
    measurable_sliceLpNorm c hsmη, fun i j => measurable_sliceLpNorm c (hsmD2 i j),
    ?_, ?_, ?_, ?_⟩
  · calc sLpNorm (-9 / 8) T (sliceLpNorm c b0')
        ≤ hNorm c bgp b0' := sLpNorm_sliceLpNorm_le_hNorm c T hsm0
      _ = hNorm c bgp b := eLpNorm_congr_ae (hae_b0'_h.trans hbb0)
      _ ≤ ENNReal.ofReal A * hNorm c bgp F := hbF
      _ ≤ ENNReal.ofReal C_tot * hNorm c bgp F := by gcongr
  · calc ENNReal.ofReal (Real.sqrt ν) *
          sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm c b0q s)
        ≤ ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0q) := by
          gcongr; exact sLpNorm_sqrtS_sliceLpNorm_le c T hsmq
      _ = ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS Qb) := by
          rw [hNorm, hNorm, eLpNorm_congr_ae hae_qh]
      _ ≤ ENNReal.ofReal (4 * K * B) * hNorm c bgp F := hQn
      _ ≤ ENNReal.ofReal C_tot * hNorm c bgp F := by gcongr
  · calc ENNReal.ofReal (Real.sqrt ν) *
          sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (Real.sqrt s) * sliceLpNorm c b0η s)
        ≤ ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0η) := by
          gcongr; exact sLpNorm_sqrtS_sliceLpNorm_le c T hsmη
      _ = ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS Eb) := by
          rw [hNorm, hNorm, eLpNorm_congr_ae hae_ηh]
      _ ≤ ENNReal.ofReal (4 * K * B) * hNorm c bgp F := hEn
      _ ≤ ENNReal.ofReal C_tot * hNorm c bgp F := by gcongr
  · intro i j
    calc ENNReal.ofReal ν *
          sLpNorm (-9 / 8) T (fun s => ENNReal.ofReal s * sliceLpNorm c (D2 i j) s)
        ≤ ENNReal.ofReal ν * hNorm c bgp (mulS (D2 i j)) := by
          gcongr; exact sLpNorm_mulS_sliceLpNorm_le c T (hsmD2 i j)
      _ = ENNReal.ofReal ν * hNorm c bgp (mulS (D2g i j)) := by
          rw [hNorm, hNorm, eLpNorm_congr_ae (hae_D2h i j)]
      _ ≤ ENNReal.ofReal (4 * K * B) * hNorm c bgp F := hD2n i j
      _ ≤ ENNReal.ofReal C_tot * hNorm c bgp F := by gcongr

end UnforcedLeray.Short.IIb

end
