import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound

/-!
# Flat profile graph bound with polynomial dependence on `Γ`

Source of record: `the November 2 reference manuscript`, lines 1921-1938 and
1992-1996. Refines `flatGraphExists` / `flat_graph_bound` (`Tasks/FlatWindows.lean`) to expose
the explicit `O(Γ²)` dependence on `‖μ‖ ≤ Γ` and `(Re μ + (3/r - 1)/2)⁻¹ ≤ Γ`, together with
the `hMeas c r`-measurability of `Sb`, `√s Qb`, `√s Eb`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

def flatK0Fn (M C Ci : ℝ) (μ : ℂ) : ℝ :=
  1024 * C * (1 + (‖μ‖ + M / 2)) + (512 * Ci + 4096 * Ci * C * (1 + (‖μ‖ + M / 2)))

theorem flatK0Fn_pos {M C Ci : ℝ} (hM : 0 ≤ M) (hC : 0 < C) (hCi : 0 < Ci) (μ : ℂ) :
    0 < flatK0Fn M C Ci μ := by
  unfold flatK0Fn
  have hQ : 0 ≤ ‖μ‖ + M / 2 := by have := norm_nonneg μ; linarith
  have h1 : 0 < 1024 * C * (1 + (‖μ‖ + M / 2)) :=
    mul_pos (mul_pos (by norm_num) hC) (by linarith)
  have h2 : 0 ≤ 512 * Ci + 4096 * Ci * C * (1 + (‖μ‖ + M / 2)) := by
    have : 0 ≤ 4096 * Ci * C * (1 + (‖μ‖ + M / 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCi.le) hC.le) (by linarith)
    linarith
  linarith

theorem wbdScalar_explicit (r : ℝ) (h1r : 1 < r) (h3r : r < 3) :
    ∃ M C Ci : ℝ, 0 ≤ M ∧ 0 < C ∧ 0 < Ci ∧
      ∀ (μ : ℂ) (ν c : ℝ), 0 < ν → 0 < c →
      ∀ G b : CProf, InHr c r G → InHr c r b → FullFlatEq ν μ G b → ∀ a : ℝ, 0 < a →
      ∀ i : Fin 2, ∃ T P Q : Coord → ℂ,
        HasWeakFOOn (winOpen a) vS dZero (fun x => b x i) T ∧
        HasWeakFOOn (winOpen a) vQ0 dZero (fun x => b x i) P ∧
        HasWeakFOOn (winOpen a) vEta dZero (fun x => b x i) Q ∧
        (QPeriodicS c T ∧ AEStronglyMeasurable T volume) ∧
        (QPeriodicS c P ∧ AEStronglyMeasurable P volume) ∧
        (QPeriodicS c Q ∧ AEStronglyMeasurable Q volume) ∧
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
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := by
  obtain ⟨M, hM0, hM⟩ := winCutProps
  obtain ⟨C, hC, hCp⟩ := cylHeatMaxReg r h1r
  obtain ⟨Ci, hCi, hCip⟩ := cylGradInterp r h1r
  refine ⟨M, C, Ci, hM0, hC, hCi, fun μ ν c hν hc G b hG hb hF a ha i => ?_⟩
  have hD' := wbdData M hM0 hM windowWeightCompare c r hc h1r h3r μ G b hG hb a ha i
  obtain ⟨huP, hfP, huM, hfM, huF, hfF, huB, hfB⟩ := hD'
  have heat := (windowHeatEq_of winCutProps) c r ν μ hc h1r hν G b hG hb hF a ha i
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
  have hT' := wbdTransfer M hM c r hc h1r μ G b hG hb a ha i Dt D1
    ⟨hDtP, hDtM, hDtF⟩ (fun j => ⟨(hD1P j).1, (hD1P j).2, hD1F j⟩) hDtφ hD1φ
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
  exact ⟨fun x => (x.1 : ℂ) * Dt x, D1 0, D1 1, hT'.1, hT'.2.1, hT'.2.2,
    ⟨wbds_qper_mul hDtP, wbds_meas_mul hDtM⟩, ⟨(hD1P 0).1, (hD1P 0).2⟩,
    ⟨(hD1P 1).1, (hD1P 1).2⟩, hK1, hK2 0, hK2 1⟩

theorem windowBound_explicit (r : ℝ) (h1 : 1 < r) (h3 : r < 3) :
    ∃ M C Ci : ℝ, 0 ≤ M ∧ 0 < C ∧ 0 < Ci ∧
      ∀ (μ : ℂ) (ν c : ℝ), 0 < ν → 0 < c →
      ∀ G b : CProf, InHr c r G → InHr c r b → FullFlatEq ν μ G b →
      ∃ S Q E : ℝ → CProf, ∀ a : ℝ, 0 < a →
        HasWeakVecOn (winOpen a) vS dZero b (S a) ∧
        HasWeakVecOn (winOpen a) vQ0 dZero b (Q a) ∧
        HasWeakVecOn (winOpen a) vEta dZero b (E a) ∧
        (QPeriodic c (S a) ∧ AEStronglyMeasurable (S a) volume) ∧
        (QPeriodic c (Q a) ∧ AEStronglyMeasurable (Q a) volume) ∧
        (QPeriodic c (E a) ∧ AEStronglyMeasurable (E a) volume) ∧
        hNormOn c r (winOpen a) (S a) ≤
          ENNReal.ofReal (2 * flatK0Fn M C Ci μ) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
        ENNReal.ofReal (Real.sqrt ν) * hNormOn c r (winOpen a) (sqrtS (Q a)) ≤
          ENNReal.ofReal (2 * flatK0Fn M C Ci μ) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
        ENNReal.ofReal (Real.sqrt ν) * hNormOn c r (winOpen a) (sqrtS (E a)) ≤
          ENNReal.ofReal (2 * flatK0Fn M C Ci μ) *
            (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) := by
  classical
  obtain ⟨M, C, Ci, hM, hC, hCi, hK⟩ := wbdScalar_explicit r h1 h3
  refine ⟨M, C, Ci, hM, hC, hCi, fun μ ν c hν hc G b hG hb hF => ?_⟩
  set K0 := flatK0Fn M C Ci μ
  have hK0 : 0 < K0 := flatK0Fn_pos hM hC hCi μ
  have H : ∀ (a : ℝ) (i : Fin 2), ∃ T P Q : Coord → ℂ, 0 < a →
      (HasWeakFOOn (winOpen a) vS dZero (fun x => b x i) T ∧
      HasWeakFOOn (winOpen a) vQ0 dZero (fun x => b x i) P ∧
      HasWeakFOOn (winOpen a) vEta dZero (fun x => b x i) Q ∧
      (QPeriodicS c T ∧ AEStronglyMeasurable T volume) ∧
      (QPeriodicS c P ∧ AEStronglyMeasurable P volume) ∧
      (QPeriodicS c Q ∧ AEStronglyMeasurable Q volume) ∧
      eLpNorm T (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      ENNReal.ofReal (Real.sqrt ν) *
          eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * P x) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      ENNReal.ofReal (Real.sqrt ν) *
          eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * Q x) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b)) := by
    intro a i
    by_cases ha : 0 < a
    · obtain ⟨T, P, Q, hh⟩ := hK μ ν c hν hc G b hG hb hF a ha i
      exact ⟨T, P, Q, fun _ => hh⟩
    · exact ⟨0, 0, 0, fun h => absurd h ha⟩
  choose T P Q hTPQ using H
  refine ⟨fun a => wbdVec (fun i => T a i), fun a => wbdVec (fun i => P a i),
    fun a => wbdVec (fun i => Q a i), fun a ha => ?_⟩
  have hh : ∀ i, _ := fun i => hTPQ a i ha
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1.le
  set RHS := hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b with hRHS
  have hmeas : ∀ (F : Fin 2 → Coord → ℂ), (∀ i, AEStronglyMeasurable (F i) volume) →
      ∀ i, AEStronglyMeasurable (F i) ((hMeas c r).restrict (winOpen a)) := fun F hF i =>
    (hF i).mono_ac ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
      (ageμ_ac_volume c (r / 2 - 5 / 2)))
  have two : ENNReal.ofReal (2 * K0) = ENNReal.ofReal K0 + ENNReal.ofReal K0 := by
    rw [two_mul, ENNReal.ofReal_add hK0.le hK0.le]
  have key : ∀ (F : Fin 2 → Coord → ℂ) (w : ℝ≥0∞), (∀ i, AEStronglyMeasurable (F i) volume) →
      (∀ i, w * eLpNorm (F i) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
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
      wbdVec (fun i x => (Real.sqrt x.1 : ℂ) * F i x) := by
    intro F; funext x; ext j; simp [sqrtS, wbdVec]
  have hsqm : ∀ (F : Fin 2 → Coord → ℂ), (∀ i, AEStronglyMeasurable (F i) volume) →
      ∀ i, AEStronglyMeasurable (fun x : Coord => (Real.sqrt x.1 : ℂ) * F i x) volume := by
    intro F hF i
    exact (Complex.measurable_ofReal.comp ((Real.continuous_sqrt.measurable.comp measurable_fst))
      ).aestronglyMeasurable.mul (hF i)
  refine ⟨fun i => (hh i).1, fun i => (hh i).2.1, fun i => (hh i).2.2.1,
    ⟨wbdVec_per (fun i => (hh i).2.2.2.1.1), wbdVec_aesm (fun i => (hh i).2.2.2.1.2)⟩,
    ⟨wbdVec_per (fun i => (hh i).2.2.2.2.1.1), wbdVec_aesm (fun i => (hh i).2.2.2.2.1.2)⟩,
    ⟨wbdVec_per (fun i => (hh i).2.2.2.2.2.1.1), wbdVec_aesm (fun i => (hh i).2.2.2.2.2.1.2)⟩,
    ?_, ?_, ?_⟩
  · have := key (fun i => T a i) 1 (fun i => (hh i).2.2.2.1.2) (fun i => by
      simpa using (hh i).2.2.2.2.2.2.1)
    simpa [hNormOn] using this
  · have := key (fun i x => (Real.sqrt x.1 : ℂ) * P a i x) (ENNReal.ofReal (Real.sqrt ν))
      (hsqm _ (fun i => (hh i).2.2.2.2.1.2)) (fun i => (hh i).2.2.2.2.2.2.2.1)
    rw [hNormOn, hsq]; exact this
  · have := key (fun i x => (Real.sqrt x.1 : ℂ) * Q a i x) (ENNReal.ofReal (Real.sqrt ν))
      (hsqm _ (fun i => (hh i).2.2.2.2.2.1.2)) (fun i => (hh i).2.2.2.2.2.2.2.2)
    rw [hNormOn, hsq]; exact this

theorem flat_graph_poly (r : ℝ) (hr1 : 1 < r) (hr3 : r < 3) :
    ∃ C_flat : ℝ, 0 < C_flat ∧
      ∀ (Γ ν c : ℝ) (μ : ℂ), 1 ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + (3 / r - 1) / 2 →
        0 < ν → 0 < c →
      ∀ F b : CProf, InHr c r F → IsFlatResponse ν μ F b → InFlatClass c r b →
        ∃ Sb Qb Eb : CProf,
          HasWeakVec vS dZero b Sb ∧ HasWeakVec vQ0 dZero b Qb ∧
          HasWeakVec vEta dZero b Eb ∧
          AEStronglyMeasurable Sb (hMeas c r) ∧
          AEStronglyMeasurable (sqrtS Qb) (hMeas c r) ∧
          AEStronglyMeasurable (sqrtS Eb) (hMeas c r) ∧
          hNorm c r b + hNorm c r Sb +
              ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb)) ≤
            ENNReal.ofReal (C_flat * Γ ^ 2) * hNorm c r F := by
  obtain ⟨CL, hCL, hL⟩ := flatLerayLiftOfSlice cylinderHelmholtzLr r hr1 hr3
  obtain ⟨M, C, Ci, hM, hC, hCi, hWK⟩ := windowBound_explicit r hr1 hr3
  set K_base : ℝ := 2 * (1024 * C * (2 + M / 2) + (512 * Ci + 4096 * Ci * C * (2 + M / 2)))
  have hK_base_pos : 0 < K_base := by
    dsimp [K_base]
    have : 0 < 1024 * C * (2 + M / 2) := mul_pos (mul_pos (by norm_num) hC) (by linarith)
    have : 0 ≤ 512 * Ci + 4096 * Ci * C * (2 + M / 2) := by
      have : 0 ≤ 4096 * Ci * C * (2 + M / 2) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCi.le) hC.le) (by linarith)
      linarith
    linarith
  refine ⟨CL + 24 * K_base * CL + 1, by positivity, ?_⟩
  intro Γ ν c μ hΓ1 hμΓ hgap hν hc F b0 hF hb0 hbc0
  have hΓ0 : 0 < Γ := lt_of_lt_of_le one_pos hΓ1
  have ha : 0 < μ.re + (3 / r - 1) / 2 := lt_of_lt_of_le (inv_pos.mpr hΓ0) hgap
  set K := 2 * flatK0Fn M C Ci μ
  have hK : 0 < K := mul_pos (by norm_num) (flatK0Fn_pos hM hC hCi μ)
  set A : ℝ := CL / (μ.re + (3 / r - 1) / 2) with hA
  set B : ℝ := CL + A with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact div_nonneg hCL.le ha.le
  have hB0 : 0 ≤ B := by rw [hB]; exact add_nonneg hCL.le hA0
  have hK4 : 0 ≤ 4 * K := mul_nonneg (by norm_num) hK.le
  have hKB : 0 ≤ 4 * K * B := mul_nonneg hK4 hB0
  obtain ⟨G, hGH, hGn, hGs, hGp⟩ := hL c hc F hF
  have hbm := duhamelMeasurable r hr1 hr3 μ ha ν c hν hc G hGH
  have hbn := duhamelBound r hr1 hr3 μ ha ν c hν hc G hGH
  have hbper := duhamelPeriodic ν μ c G hc hGH.periodic
  have hbH : InHr c r (flatDuhamel ν μ G) :=
    ⟨hbper, hbm, lt_of_le_of_lt hbn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGH.finite)⟩
  have hbs := duhamelSolenoidal r hr1 hr3 μ ha ν c hν hc G hGH hGs hbH
  have hresp : IsFlatResponse ν μ F (flatDuhamel ν μ G) := by
    refine ⟨hbs, fun Ψ hΨ => ?_⟩
    obtain ⟨hi1, hi2, he⟩ := duhamelEquation r hr1 hr3 μ ha ν c hν hc G hGH hbH Ψ hΨ
    obtain ⟨hj1, hj2⟩ := hGp Ψ hΨ
    have hsplit := cdot_eq_add_sub F G Ψ
    refine ⟨hi1, ?_, ?_⟩
    · rw [hsplit]
      exact hi2.add hj1
    · rw [hsplit, integral_add hi2 hj1, hj2, add_zero]
      exact he
  have hfull := duhamelFullEq r hr1 hr3 μ ha ν c hν hc G hGH hbH
  set b := flatDuhamel ν μ G
  have hbF : hNorm c r b ≤ ENNReal.ofReal A * hNorm c r F := by
    calc hNorm c r b ≤ ENNReal.ofReal (1 / (μ.re + (3 / r - 1) / 2)) * hNorm c r G := hbn
      _ ≤ ENNReal.ofReal (1 / (μ.re + (3 / r - 1) / 2)) * (ENNReal.ofReal CL * hNorm c r F) := by
          gcongr
      _ = ENNReal.ofReal A * hNorm c r F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (one_div_pos.mpr ha).le, hA]
          congr 2
          ring
  have hP : ENNReal.ofReal (4 * K) * (hNorm c r G + hNorm c r b) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c r F := by
    have hGbF : hNorm c r G + hNorm c r b ≤ ENNReal.ofReal B * hNorm c r F := by
      rw [hB, ENNReal.ofReal_add hCL.le hA0, add_mul]
      exact add_le_add hGn hbF
    calc ENNReal.ofReal (4 * K) * (hNorm c r G + hNorm c r b)
        ≤ ENNReal.ofReal (4 * K) * (ENNReal.ofReal B * hNorm c r F) := by gcongr
      _ = ENNReal.ofReal (4 * K * B) * hNorm c r F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hK4]
  have hPfin : ENNReal.ofReal (4 * K * B) * hNorm c r F < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.finite
  obtain ⟨S, Q, E, hw⟩ := hWK μ ν c hν hc G b hGH hbH hfull
  obtain ⟨Sb, hSbw, hSbp, hSbm, hSbe⟩ := weakGlue vS fw_vS_smooth c b S
    (fun a ha => (hw a ha).1) (fun a ha => (hw a ha).2.2.2.1)
  obtain ⟨Qb, hQbw, hQbp, hQbm, hQbe⟩ := weakGlue vQ0 fw_vQ0_smooth c b Q
    (fun a ha => (hw a ha).2.1) (fun a ha => (hw a ha).2.2.2.2.1)
  obtain ⟨Eb, hEbw, hEbp, hEbm, hEbe⟩ := weakGlue vEta fw_vEta_smooth c b E
    (fun a ha => (hw a ha).2.2.1) (fun a ha => (hw a ha).2.2.2.2.2.1)
  have hpos : ∀ k : ℤ, (0 : ℝ) < (2 : ℝ) ^ k := fun k => zpow_pos (by norm_num) k
  have hSk : ∀ k : ℤ, ENNReal.ofReal 1 * hNormOn c r (winOpen ((2 : ℝ) ^ k)) Sb ≤
      ENNReal.ofReal K * (hNormOn c r (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c r (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [ENNReal.ofReal_one, one_mul, fw_hNormOn_congr (hSbe _ (hpos k))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.1
  have hSn : hNorm c r Sb ≤ ENNReal.ofReal (4 * K * B) * hNorm c r F := by
    have h := dyadicSummation r c hr1.le hc Sb G b 1 K zero_le_one hK.le
      (hSbm.mono_ac (fw_hMeas_ac c r)) hGH.meas hbH.meas hSk
    rw [ENNReal.ofReal_one, one_mul] at h
    exact h.trans hP
  have hQk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c r (winOpen ((2 : ℝ) ^ k)) (sqrtS Qb) ≤
      ENNReal.ofReal K * (hNormOn c r (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c r (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hQbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.1
  have hQn : ENNReal.ofReal (Real.sqrt ν) * hNorm c r (sqrtS Qb) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c r F :=
    (dyadicSummation r c hr1.le hc (sqrtS Qb) G b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c r))) hGH.meas hbH.meas
      hQk).trans hP
  have hEk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c r (winOpen ((2 : ℝ) ^ k)) (sqrtS Eb) ≤
      ENNReal.ofReal K * (hNormOn c r (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c r (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hEbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2
  have hEn : ENNReal.ofReal (Real.sqrt ν) * hNorm c r (sqrtS Eb) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c r F :=
    (dyadicSummation r c hr1.le hc (sqrtS Eb) G b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c r))) hGH.meas hbH.meas
      hEk).trans hP
  have hsq0 : ENNReal.ofReal (Real.sqrt ν) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hν)).ne'
  have hQfin : hNorm c r (sqrtS Qb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hQn hPfin).ne hsq0
  have hEfin : hNorm c r (sqrtS Eb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hEn hPfin).ne hsq0
  have hbc : InFlatClass c r b :=
    ⟨hbH, Sb, Qb, Eb, hSbw, hQbw, hEbw,
      ⟨hSbp, hSbm.mono_ac (fw_hMeas_ac c r), lt_of_le_of_lt hSn hPfin⟩,
      ⟨qPeriodic_sqrtS hQbp, aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c r)), hQfin⟩,
      ⟨qPeriodic_sqrtS hEbp, aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c r)), hEfin⟩⟩
  have h0 : b0 - b =ᵐ[hMeas c r] 0 :=
    flat_unique hc hν hr1 hr3 ha (b0 - b) (flatClassSub c r b0 b hbc0 hbc)
      (flatResponseSub ν μ F b0 b hb0 hresp)
  have hbb0 : b0 =ᵐ[hMeas c r] b := by
    filter_upwards [h0] with x hx
    exact sub_eq_zero.mp hx
  have hae : ∀ᵐ x : Coord, 0 < x.1 → b0 x = b x :=
    CongrHelp.ae_volume_of_ageμ hc hbc0.inHr.periodic hbc.inHr.periodic hbb0
  refine ⟨Sb, Qb, Eb,
    fun i => CongrHelp.hasWeakFO_congr (by filter_upwards [hae] with x hx hp; rw [hx hp]) (hSbw i),
    fun i => CongrHelp.hasWeakFO_congr (by filter_upwards [hae] with x hx hp; rw [hx hp]) (hQbw i),
    fun i => CongrHelp.hasWeakFO_congr (by filter_upwards [hae] with x hx hp; rw [hx hp]) (hEbw i),
    hSbm.mono_ac (fw_hMeas_ac c r),
    aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c r)),
    aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c r)), ?_⟩
  have hnb0 : hNorm c r b0 = hNorm c r b := eLpNorm_congr_ae hbb0
  rw [hnb0]
  have hbd_AB : hNorm c r b + hNorm c r Sb +
      ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb)) ≤
      ENNReal.ofReal (A + 3 * (4 * K * B)) * hNorm c r F := by
    calc hNorm c r b + hNorm c r Sb +
          ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb))
        = hNorm c r b + hNorm c r Sb +
          (ENNReal.ofReal (Real.sqrt ν) * hNorm c r (sqrtS Qb) +
            ENNReal.ofReal (Real.sqrt ν) * hNorm c r (sqrtS Eb)) := by rw [mul_add]
      _ ≤ ENNReal.ofReal A * hNorm c r F + ENNReal.ofReal (4 * K * B) * hNorm c r F +
          (ENNReal.ofReal (4 * K * B) * hNorm c r F +
            ENNReal.ofReal (4 * K * B) * hNorm c r F) :=
          add_le_add (add_le_add hbF hSn) (add_le_add hQn hEn)
      _ = ENNReal.ofReal (A + 3 * (4 * K * B)) * hNorm c r F := by
          rw [ENNReal.ofReal_add hA0 (mul_nonneg (by norm_num) hKB),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
          simp only [ENNReal.ofReal_ofNat]
          ring
  refine hbd_AB.trans ?_
  gcongr
  have hinv_le : (μ.re + (3 / r - 1) / 2)⁻¹ ≤ Γ := by
    have := inv_anti₀ (inv_pos.mpr hΓ0) hgap
    rwa [inv_inv] at this
  have hA_le : A ≤ CL * Γ := by
    rw [hA, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv_le hCL.le
  have hB_le : B ≤ 2 * CL * Γ := by
    rw [hB]
    nlinarith [hCL.le, hΓ1]
  have hK_le : K ≤ K_base * Γ := by
    dsimp [K, flatK0Fn, K_base]
    have h1 : 1 + (‖μ‖ + M / 2) ≤ (2 + M / 2) * Γ := by nlinarith [hM, hΓ1, hμΓ]
    have h1024 : 0 ≤ 1024 * C := by linarith [hC.le]
    have h4096 : 0 ≤ 4096 * Ci * C := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h1024, mul_le_mul_of_nonneg_left h1 h4096, hCi.le, hΓ1]
  have hKB_le : K * B ≤ K_base * (2 * CL) * Γ ^ 2 := by
    calc K * B ≤ (K_base * Γ) * (2 * CL * Γ) :=
          mul_le_mul hK_le hB_le hB0 (mul_nonneg hK_base_pos.le hΓ0.le)
      _ = K_base * (2 * CL) * Γ ^ 2 := by ring
  have h1Γ2 : Γ ≤ Γ ^ 2 := by nlinarith [hΓ1]
  nlinarith [hCL.le, hK_base_pos.le]

end UnforcedLeray.Short.IIb

end
