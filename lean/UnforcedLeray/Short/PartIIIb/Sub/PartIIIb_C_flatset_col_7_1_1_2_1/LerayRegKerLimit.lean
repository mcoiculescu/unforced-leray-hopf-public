import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayKerWindow
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayRegKerCalc
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Removal of the regularisation (`RegKerLimit`)

Source `the November 2 reference manuscript` 1676 (removing the regularisation).
`K_i^ε = a (sin aq, sinh aη)_i / (4π (D + ε))` and `K_i = a (sin aq, sinh aη)_i / (4π D)`.
Dominated convergence along `𝓝[>] 0`: the majorant `|K_i| · M · 1_{window}` is integrable by
`CylKerWindow` (with `t = 0`), since `lap2 h` vanishes for `|y.2| > L` and is bounded on the box.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The numerator vanishes where the denominator vanishes. -/
lemma rkl_num_of_den_zero (c : ℝ) (y : ℝ × ℝ) (hD : cylDen c y = 0) :
    cylNum c 0 y = 0 ∧ cylNum c 1 y = 0 := by
  unfold cylDen at hD
  have h1 := Real.one_le_cosh (cylFreq c * y.2)
  have h2 := Real.cos_le_one (cylFreq c * y.1)
  have hcosh : Real.cosh (cylFreq c * y.2) = 1 := by linarith
  have hcos : Real.cos (cylFreq c * y.1) = 1 := by linarith
  have hs : Real.sinh (cylFreq c * y.2) = 0 := by
    have hsq := Real.cosh_sq (cylFreq c * y.2)
    rw [hcosh, one_pow] at hsq
    have h3 : Real.sinh (cylFreq c * y.2) ^ 2 = 0 := by linarith
    exact (pow_eq_zero_iff two_ne_zero).1 h3
  have hsn : Real.sin (cylFreq c * y.1) = 0 := by
    have hsq := Real.sin_sq_add_cos_sq (cylFreq c * y.1)
    rw [hcos, one_pow] at hsq
    have h3 : Real.sin (cylFreq c * y.1) ^ 2 = 0 := by linarith
    exact (pow_eq_zero_iff two_ne_zero).1 h3
  exact ⟨by simp [cylNum, hsn], by simp [cylNum, hs]⟩

lemma rkl_den_nonneg (c : ℝ) (y : ℝ × ℝ) : 0 ≤ cylDen c y := by
  unfold cylDen
  have h1 := Real.one_le_cosh (cylFreq c * y.2)
  have h2 := Real.cos_le_one (cylFreq c * y.1)
  linarith

/-- The regularised kernel is dominated by the kernel. -/
lemma rkl_abs_reg_le (c ε : ℝ) (hε : 0 < ε) (i : Fin 2) (y : ℝ × ℝ) :
    |cylKerReg c ε i y| ≤ |cylKer c i y| := by
  have hD0 := rkl_den_nonneg c y
  rcases hD0.lt_or_eq with hDpos | hD0'
  · have hDe : 0 < cylDen c y + ε := by linarith
    unfold cylKerReg cylKer
    rw [abs_div, abs_div, abs_of_pos hDe, abs_of_pos hDpos]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hDpos (by linarith)
  · obtain ⟨h0, h1⟩ := rkl_num_of_den_zero c y hD0'.symm
    have hnum : cylNum c i y = 0 := by
      fin_cases i
      · exact h0
      · exact h1
    simp [cylKerReg, cylKer, hnum]

/-- Pointwise convergence of the regularised kernel. -/
lemma rkl_tendsto_reg (c : ℝ) (i : Fin 2) (y : ℝ × ℝ) :
    Tendsto (fun ε => cylKerReg c ε i y) (𝓝[>] 0) (𝓝 (cylKer c i y)) := by
  have hD0 := rkl_den_nonneg c y
  rcases hD0.lt_or_eq with hDpos | hD0'
  · have hc : ContinuousAt
        (fun ε : ℝ => cylFreq c / (4 * Real.pi) * cylNum c i y / (cylDen c y + ε)) 0 := by
      apply ContinuousAt.div continuousAt_const (continuousAt_const.add continuousAt_id)
      show cylDen c y + 0 ≠ 0
      rw [add_zero]
      exact hDpos.ne'
    have h2 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [add_zero] at h2
    exact h2
  · obtain ⟨h0, h1⟩ := rkl_num_of_den_zero c y hD0'.symm
    have hnum : cylNum c i y = 0 := by
      fin_cases i
      · exact h0
      · exact h1
    have hfun : (fun ε => cylKerReg c ε i y) = fun _ => (0 : ℝ) := by
      funext ε
      simp [cylKerReg, hnum]
    have hK : cylKer c i y = 0 := by simp [cylKer, hnum]
    rw [hfun, hK]
    exact tendsto_const_nhds

lemma rkl_pd2_eventually_zero (g : ℝ × ℝ → ℝ) (y : ℝ × ℝ) (hg : ∀ᶠ z in 𝓝 y, g z = 0)
    (k : Fin 2) : pd2 k g y = 0 := by
  have hE : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := hg
  unfold pd2
  rw [hE.fderiv_eq]
  simp

lemma rkl_fderiv_zero_of_vanish (h : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hh : ∀ z ∈ U, h z = 0) (z : ℝ × ℝ) (hz : z ∈ U) : fderiv ℝ h z = 0 := by
  have hE : h =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hU.mem_nhds hz] with w hw using hh w hw
  rw [hE.fderiv_eq]
  simp

/-- The Laplacian of a cylinder test vanishes where `|η| > L`. -/
lemma rkl_lap2_zero (h : ℝ × ℝ → ℝ) (L : ℝ)
    (hL : ∀ y : ℝ × ℝ, L < |y.2| → h y = 0) (y : ℝ × ℝ) (hy : L < |y.2|) :
    lap2 h y = 0 := by
  set U : Set (ℝ × ℝ) := {z : ℝ × ℝ | L < |z.2|} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hyU : y ∈ U := hy
  have hhU : ∀ z ∈ U, h z = 0 := fun z hz => hL z hz
  have hp : ∀ j : Fin 2, ∀ z ∈ U, pd2 j h z = 0 := by
    intro j z hz
    unfold pd2
    rw [rkl_fderiv_zero_of_vanish h U hU hhU z hz]
    simp
  have hpe : ∀ j : Fin 2, ∀ᶠ z in 𝓝 y, pd2 j h z = 0 := fun j =>
    Filter.eventually_of_mem (hU.mem_nhds hyU) (fun z hz => hp j z hz)
  have e0 := rkl_pd2_eventually_zero (pd2 0 h) y (hpe 0) 0
  have e1 := rkl_pd2_eventually_zero (pd2 1 h) y (hpe 1) 1
  unfold lap2
  simp only [e0, e1, add_zero]

lemma rkl_contDiff_pd2 (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (j : Fin 2) :
    ContDiff ℝ ∞ (pd2 j g) := by
  unfold pd2
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma rkl_measurable_cylNum (c : ℝ) (i : Fin 2) : Measurable (cylNum c i) := by
  fin_cases i
  · have : cylNum c 0 = fun y => Real.sin (cylFreq c * y.1) := by funext y; simp [cylNum]
    show Measurable (cylNum c 0)
    rw [this]; fun_prop
  · have : cylNum c 1 = fun y => Real.sinh (cylFreq c * y.2) := by funext y; simp [cylNum]
    show Measurable (cylNum c 1)
    rw [this]; fun_prop

lemma rkl_measurable_reg (c ε : ℝ) (hε : 0 < ε) (i : Fin 2) :
    Measurable (fun y => cylKerReg c ε i y) := by
  unfold cylKerReg
  have h2 : Measurable (fun y : ℝ × ℝ => cylDen c y + ε) := by
    unfold cylDen; fun_prop
  exact ((rkl_measurable_cylNum c i).const_mul _).div h2

theorem regKerLimit : RegKerLimit := by
  intro c hc h hh i
  unfold IsCylTest2 at hh
  obtain ⟨hsm, -, L, hL⟩ := hh
  -- the Laplacian of `h` is continuous
  have hlapc : Continuous (lap2 h) := by
    unfold lap2
    exact ((rkl_contDiff_pd2 _ (rkl_contDiff_pd2 h hsm 0) 0).continuous.add
      (rkl_contDiff_pd2 _ (rkl_contDiff_pd2 h hsm 1) 1).continuous)
  -- uniform bound of the Laplacian on the window
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∀ y ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L, ‖lap2 h y‖ ≤ M := by
    have hKc : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L) :=
      isCompact_Icc.prod isCompact_Icc
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hlapc.continuousOn
    exact ⟨max M 0, le_max_right _ _, fun y hy => (hM y hy).trans (le_max_left _ _)⟩
  set W0 : Set (ℝ × ℝ) := Ioc (-(c / 2)) (c / 2) ×ˢ Icc (0 - L) (0 + L) with hW0
  have hW0m : MeasurableSet W0 := measurableSet_Ioc.prod measurableSet_Icc
  have hW0K : ∀ y ∈ W0, y ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L := by
    intro y hy
    obtain ⟨ha, hb⟩ := hy.2
    exact ⟨Ioc_subset_Icc_self hy.1, by constructor <;> linarith⟩
  have hcellm : MeasurableSet (cellC c) :=
    MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ
  have hsub : W0 ⊆ cellC c := fun y hy => ⟨hy.1, Set.mem_univ _⟩
  -- integrability of the majorant
  obtain ⟨C, hC⟩ := cylKerWindow c hc L
  have hKW : IntegrableOn (cylKer c i) W0 := (hC i 0).1
  have hbint : Integrable (W0.indicator (fun y => M * |cylKer c i y|))
      (volume.restrict (cellC c)) := by
    rw [integrable_indicator_iff hW0m]
    show Integrable _ ((volume.restrict (cellC c)).restrict W0)
    rw [Measure.restrict_restrict hW0m, inter_eq_left.2 hsub]
    exact hKW.abs.const_mul M
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun ε y => cylKerReg c ε i y * lap2 h y)
    (f := fun y => cylKer c i y * lap2 h y)
    (W0.indicator (fun y => M * |cylKer c i y|)) ?_ ?_ hbint ?_
  · refine eventually_nhdsWithin_of_forall (fun ε hε => ?_)
    exact (((rkl_measurable_reg c ε (Set.mem_Ioi.mp hε) i).mul hlapc.measurable)).aestronglyMeasurable
  · refine eventually_nhdsWithin_of_forall (fun ε hε => ?_)
    have hε' : 0 < ε := Set.mem_Ioi.mp hε
    refine ae_restrict_of_forall_mem hcellm (fun y hy => ?_)
    by_cases hyW : y ∈ W0
    · rw [Set.indicator_of_mem hyW, Real.norm_eq_abs, abs_mul]
      have hl : |lap2 h y| ≤ M := by
        rw [← Real.norm_eq_abs]; exact hM y (hW0K y hyW)
      have hr := rkl_abs_reg_le c ε hε' i y
      have hK0 : 0 ≤ |cylKer c i y| := abs_nonneg _
      calc |cylKerReg c ε i y| * |lap2 h y| ≤ |cylKer c i y| * M :=
            mul_le_mul hr hl (abs_nonneg _) hK0
        _ = M * |cylKer c i y| := mul_comm _ _
    · rw [Set.indicator_of_notMem hyW]
      have hyL : L < |y.2| := by
        by_contra hcon
        push_neg at hcon
        have hyI : y.2 ∈ Icc (0 - L) (0 + L) := by
          obtain ⟨ha, hb⟩ := abs_le.1 hcon
          exact ⟨by linarith, by linarith⟩
        exact hyW ⟨hy.1, hyI⟩
      simp [rkl_lap2_zero h L hL y hyL]
  · refine ae_of_all _ (fun y => ?_)
    exact (rkl_tendsto_reg c i y).mul_const (lap2 h y)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
