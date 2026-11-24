import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayRhoMass
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayRhoTail
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact

/-!
# Approximate identity (`RegApproxId`)

Source `the November 2 reference manuscript` 1676 (approximate identity of the
regularised cylinder density `rho_eps`).  Let `g = ∂_i h`.  `g` is continuous, vanishes for
`|η| > L`, hence is bounded by `Mb` on the cell.  Given `η0 > 0`, continuity at `0` gives a radius
`r` with `|g y - g 0| < η0/2` on `‖y‖ < r`; the tail `cell ∩ {r ≤ ‖y‖}` carries mass `≤ C ε`
(`rhoTail`), and `∫_cell ρ_ε = 1` (`rhoMass`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem regApproxId : RegApproxId := by
  intro c hc h hh i
  unfold IsCylTest2 at hh
  obtain ⟨hsm, -, L, hL⟩ := hh
  -- continuity of `g = ∂_i h`
  have hgc : Continuous (pd2 i h) := by
    unfold pd2
    exact (hsm.continuous_fderiv (by simp)).clm_apply continuous_const
  -- `g` vanishes where `|η| > L`
  have hg0 : ∀ y : ℝ × ℝ, L < |y.2| → pd2 i h y = 0 := by
    intro y hy
    have hopen : IsOpen {z : ℝ × ℝ | L < |z.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
    have hev : h =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      exact hL z hz
    have hder : fderiv ℝ h y = 0 := by
      rw [hev.fderiv_eq]
      simp
    unfold pd2
    rw [hder]
    simp
  -- uniform bound of `g` on the cell
  obtain ⟨Mb, hMb0, hbd⟩ : ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ y ∈ cellC c, ‖pd2 i h y‖ ≤ Mb := by
    have hKc : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L) :=
      (isCompact_Icc).prod (isCompact_Icc)
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hgc.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun y hy => ?_⟩
    rcases le_or_gt |y.2| L with hyL | hyL
    · have hy' : y.1 ∈ Ioc (-(c / 2)) (c / 2) := by
        simpa [cellC] using hy
      have hyK : y ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L :=
        ⟨Ioc_subset_Icc_self hy', abs_le.mp hyL⟩
      exact (hM y hyK).trans (le_max_left _ _)
    · rw [hg0 y hyL, norm_zero]
      exact le_max_right _ _
  have h0cell : (0 : ℝ × ℝ) ∈ cellC c :=
    ⟨⟨by show -(c / 2) < 0; linarith, by show (0 : ℝ) ≤ c / 2; linarith⟩, Set.mem_univ _⟩
  have hcellm : MeasurableSet (cellC c) :=
    MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ
  -- the approximate identity
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η0 hη0
  obtain ⟨r, hr, hrg⟩ := Metric.continuousAt_iff.mp (hgc.continuousAt (x := (0 : ℝ × ℝ)))
    (η0 / 2) (by linarith)
  obtain ⟨C, hC⟩ := rhoTail c r hc hr
  have hden : 0 < 4 * (Mb * |C| + 1) := by
    have := mul_nonneg hMb0 (abs_nonneg C)
    linarith
  refine ⟨η0 / (4 * (Mb * |C| + 1)), div_pos hη0 hden, fun ε hε hεd => ?_⟩
  have hε0 : 0 < ε := Set.mem_Ioi.mp hε
  rw [Real.dist_eq, sub_zero, abs_of_pos hε0] at hεd
  obtain ⟨hnn, hint, hmass⟩ := rhoMass c ε hc hε0
  have hae : ∀ᵐ y ∂(volume.restrict (cellC c)), ‖pd2 i h y‖ ≤ Mb :=
    ae_restrict_of_forall_mem hcellm (fun y hy => hbd y hy)
  have hprod : IntegrableOn (fun y => cylRho c ε y * pd2 i h y) (cellC c) :=
    hint.mul_bdd hgc.aestronglyMeasurable hae
  have h2 : IntegrableOn (fun y => cylRho c ε y * pd2 i h 0) (cellC c) :=
    hint.mul_const _
  -- subtract the constant `g 0` using the mass one
  have hsplit : (∫ y in cellC c, cylRho c ε y * pd2 i h y) - pd2 i h 0
      = ∫ y in cellC c, cylRho c ε y * (pd2 i h y - pd2 i h 0) := by
    simp_rw [mul_sub]
    rw [integral_sub hprod h2, integral_mul_const, hmass]
    ring
  -- the majorant
  set B : Set (ℝ × ℝ) := {y : ℝ × ℝ | r ≤ ‖y‖} with hB
  have hBm : MeasurableSet B := (isClosed_le continuous_const continuous_norm).measurableSet
  have hGint_ble : IntegrableOn (fun y => (η0 / 2) * cylRho c ε y +
      Set.indicator B (fun y => 2 * Mb * cylRho c ε y) y) (cellC c) :=
    (hint.const_mul (η0 / 2)).add ((hint.const_mul (2 * Mb)).indicator hBm)
  have hbound : ‖∫ y in cellC c, cylRho c ε y * (pd2 i h y - pd2 i h 0)‖ ≤
      ∫ y in cellC c, ((η0 / 2) * cylRho c ε y +
        Set.indicator B (fun y => 2 * Mb * cylRho c ε y) y) := by
    apply norm_integral_le_of_norm_le hGint_ble
    refine ae_restrict_of_forall_mem hcellm (fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn y)]
    by_cases hyB : r ≤ ‖y‖
    · rw [Set.indicator_of_mem (show y ∈ B from hyB)]
      have h1 : |pd2 i h y - pd2 i h 0| ≤ 2 * Mb := by
        rw [← Real.norm_eq_abs]
        exact (norm_sub_le _ _).trans (by linarith [hbd y hy, hbd 0 h0cell])
      have h3 := mul_le_mul_of_nonneg_left h1 (hnn y)
      nlinarith [mul_nonneg (hnn y) hη0.le]
    · rw [Set.indicator_of_notMem (show y ∉ B from hyB), add_zero]
      have hlt : ‖y‖ < r := lt_of_not_ge hyB
      have hd : dist y 0 < r := by rw [dist_zero_right]; exact hlt
      have hg := hrg hd
      rw [Real.dist_eq] at hg
      have := mul_le_mul_of_nonneg_left hg.le (hnn y)
      linarith
  have hGval : ∫ y in cellC c, ((η0 / 2) * cylRho c ε y +
        Set.indicator B (fun y => 2 * Mb * cylRho c ε y) y)
      = η0 / 2 + 2 * Mb * ∫ y in cellC c ∩ B, cylRho c ε y := by
    rw [integral_add (hint.const_mul _) (((hint.const_mul (2 * Mb))).indicator hBm)]
    rw [integral_const_mul, hmass, setIntegral_indicator hBm, integral_const_mul, mul_one]
  have htail : ∫ y in cellC c ∩ B, cylRho c ε y ≤ C * ε := hC ε hε0
  have hfin1 : 2 * Mb * ∫ y in cellC c ∩ B, cylRho c ε y ≤ 2 * Mb * (C * ε) :=
    mul_le_mul_of_nonneg_left htail (by linarith)
  have hεK : ε * (4 * (Mb * |C| + 1)) < η0 := (lt_div_iff₀ hden).mp hεd
  have hCabs : 2 * Mb * (C * ε) ≤ 2 * Mb * (|C| * ε) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) hε0.le) (by linarith)
  rw [Real.dist_eq, hsplit, ← Real.norm_eq_abs]
  calc ‖∫ y in cellC c, cylRho c ε y * (pd2 i h y - pd2 i h 0)‖
      ≤ ∫ y in cellC c, ((η0 / 2) * cylRho c ε y +
        Set.indicator B (fun y => 2 * Mb * cylRho c ε y) y) := hbound
    _ = η0 / 2 + 2 * Mb * ∫ y in cellC c ∩ B, cylRho c ε y := hGval
    _ ≤ η0 / 2 + 2 * Mb * (C * ε) := by linarith
    _ < η0 := by nlinarith [hCabs, hεK, hε0, abs_nonneg C]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
