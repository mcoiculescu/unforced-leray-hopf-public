import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.CutoffFamily
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.CutoffHolder
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# `CutoffApprox`: radial cutoff approximation (step 2 of `HardyApprox`)

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
`φ n = χ n • v` with the cutoff family `χ n` of `CutoffFamilyExists`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Tail `L²` bound: copy of `holdTail_eLpNorm_tendsto` at exponent `2`. -/
theorem holdTail_eLpNorm_tendsto_two (v : Space → CVec3) (hv : MemLp v 2 volume) :
    Tendsto (fun n : ℕ => eLpNorm ((holdTail n).indicator v) 2 volume) atTop (𝓝 0) := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hfin : (∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ)) ≠ ⊤ := by
    have h := hv.2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2] at h
    exact ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h).ne
  have hlim : Tendsto (fun n : ℕ => ∫⁻ x, ‖(holdTail n).indicator v x‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    have hmeas : ∀ n : ℕ, AEMeasurable (fun x => ‖(holdTail n).indicator v x‖ₑ ^ (2 : ℝ)) volume :=
      fun n => ((hv.1.indicator (holdTail_measurableSet n)).enorm).pow_const (2 : ℝ)
    have hdc := tendsto_lintegral_filter_of_dominated_convergence' (μ := volume) (l := atTop)
      (F := fun n : ℕ => fun x => ‖(holdTail n).indicator v x‖ₑ ^ (2 : ℝ))
      (f := fun _ => (0 : ℝ≥0∞)) (fun x => ‖v x‖ₑ ^ (2 : ℝ))
      (Eventually.of_forall hmeas)
      (Eventually.of_forall fun n => Eventually.of_forall fun x => by
        by_cases hx : x ∈ holdTail n
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos])
      hfin
      (Eventually.of_forall fun x => by
        have hev : ∀ᶠ n : ℕ in atTop, ‖x‖ < (n : ℝ) + 1 := by
          obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
          filter_upwards [eventually_ge_atTop N] with n hn
          have : (N : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        refine (tendsto_const_nhds (x := (0 : ℝ≥0∞))).congr' ?_
        filter_upwards [hev] with n hn
        have hx : x ∉ holdTail n := by
          simp only [holdTail, Set.mem_setOf_eq, not_le]
          exact hn
        simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos])
    simpa using hdc
  have hI := ((ENNReal.continuous_rpow_const (y := (1 / (2 : ℝ)))).tendsto (0 : ℝ≥0∞)).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hI
  refine Tendsto.congr (fun n => ?_) hI
  show (∫⁻ x, ‖(holdTail n).indicator v x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2]

/-- Pointwise cutoff bound: `‖(c y - 1) • w y‖ ≤ ‖1_{tail} w y‖` when `0 ≤ c ≤ 1` and `c = 1`
on the ball of radius `n+1`. -/
theorem cutoffApprox_pt_bound (n : ℕ) (c : Space → ℝ) (w : Space → CVec3)
    (h0 : ∀ y, 0 ≤ c y ∧ c y ≤ 1) (h1 : ∀ y, ‖y‖ ≤ (n : ℝ) + 1 → c y = 1) (y : Space) :
    ‖(c y - 1) • w y‖ ≤ ‖(holdTail n).indicator w y‖ := by
  by_cases hy : ‖y‖ ≤ (n : ℝ) + 1
  · rw [h1 y hy, sub_self, zero_smul, norm_zero]
    exact norm_nonneg _
  · have hT : y ∈ holdTail n := (not_le.1 hy).le
    rw [Set.indicator_of_mem hT, norm_smul, Real.norm_eq_abs]
    have hb : |c y - 1| ≤ 1 := abs_le.2 ⟨by linarith [(h0 y).1], by linarith [(h0 y).2]⟩
    exact mul_le_of_le_one_left (norm_nonneg _) hb

/-- Product rule for the Cartesian derivative of `c • w`. -/
theorem cutoffApprox_pdir_smul (c : Space → ℝ) (w : Space → CVec3) (hc : ContDiff ℝ ∞ c)
    (hw : ContDiff ℝ ∞ w) (j : Fin 3) (y : Space) :
    pdir j (fun z => c z • w z) y
      = c y • pdir j w y + (fderiv ℝ c y (EuclideanSpace.single j (1 : ℝ))) • w y := by
  have hcd : DifferentiableAt ℝ c y := (hc.differentiable (by simp)) y
  have hwd : DifferentiableAt ℝ w y := (hw.differentiable (by simp)) y
  have key : fderiv ℝ (fun z => c z • w z) y
      = c y • fderiv ℝ w y + (fderiv ℝ c y).smulRight (w y) :=
    fderiv_smul hcd hwd
  unfold pdir
  rw [key]
  simp

/-- The cutoff approximation, given the cutoff family and the Hölder estimate on annuli. -/
theorem cutoffApprox_of (h1 : CutoffFamilyExists) (h2 : CutoffHolder) : CutoffApprox := by
  obtain ⟨C, χ, hχ⟩ := h1
  have hsmooth : ∀ n, ContDiff ℝ ∞ (χ n) := fun n => (hχ n).1
  have hin : ∀ (n : ℕ) (y : Space), ‖y‖ < (n : ℝ) + 1 → fderiv ℝ (χ n) y = 0 := by
    intro n y hy
    have hopen : IsOpen {z : Space | ‖z‖ < (n : ℝ) + 1} :=
      isOpen_lt continuous_norm continuous_const
    have hev : χ n =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      have hz' : ‖z‖ < (n : ℝ) + 1 := hz
      exact (hχ n).2.2.2.1 z hz'.le
    rw [hev.fderiv_eq, fderiv_const_apply]
  have hout : ∀ (n : ℕ) (y : Space), ‖y‖ > 2 * ((n : ℝ) + 1) → fderiv ℝ (χ n) y = 0 := by
    intro n y hy
    have hopen : IsOpen {z : Space | 2 * ((n : ℝ) + 1) < ‖z‖} :=
      isOpen_lt continuous_const continuous_norm
    have hev : χ n =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      have hz' : 2 * ((n : ℝ) + 1) < ‖z‖ := hz
      exact (hχ n).2.2.2.2.1 z hz'.le
    rw [hev.fderiv_eq, fderiv_const_apply]
  have hbd : ∀ (n : ℕ) (y : Space), ‖fderiv ℝ (χ n) y‖ ≤ C / ((n : ℝ) + 1) :=
    fun n y => (hχ n).2.2.2.2.2 y
  have hCut := h2 C χ hsmooth hin hout hbd
  intro v hvs hv6 hv2
  refine ⟨fun n y => χ n y • v y, fun n => ⟨(hsmooth n).smul hvs, ?_⟩, ?_, ?_⟩
  · have := (hχ n).2.1.smul_right (f' := v)
    exact this
  · show Tendsto (fun n : ℕ => eLpNorm ((fun y => χ n y • v y) - v) 6 volume) atTop (𝓝 0)
    have hbd6 : ∀ n : ℕ, eLpNorm ((fun y => χ n y • v y) - v) 6 volume
        ≤ eLpNorm ((holdTail n).indicator v) 6 volume := by
      intro n
      calc eLpNorm ((fun y => χ n y • v y) - v) 6 volume
          ≤ eLpNorm (fun y => ‖(holdTail n).indicator v y‖) 6 volume := by
            refine eLpNorm_mono_real (fun y => ?_)
            have e : ((fun y => χ n y • v y) - v) y = (χ n y - 1) • v y := by
              show χ n y • v y - v y = _
              rw [sub_smul, one_smul]
            rw [e]
            exact cutoffApprox_pt_bound n (χ n) v (fun z => (hχ n).2.2.1 z)
              (fun z hz => (hχ n).2.2.2.1 z hz) y
        _ = eLpNorm ((holdTail n).indicator v) 6 volume := eLpNorm_norm _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (holdTail_eLpNorm_tendsto v hv6) (fun n => zero_le) hbd6
  · intro j
    show Tendsto (fun n : ℕ => eLpNorm (pdir j (fun y => χ n y • v y) - pdir j v) 2 volume)
      atTop (𝓝 0)
    have hvc : Continuous v := hvs.continuous
    have hpdc : Continuous (pdir j v) := by
      unfold pdir
      exact (hvs.continuous_fderiv (by simp)).clm_apply continuous_const
    have hA : ∀ n : ℕ, Continuous (fun y => (χ n y - 1) • pdir j v y) := fun n =>
      ((hsmooth n).continuous.sub continuous_const).smul hpdc
    have hB : ∀ n : ℕ,
        Continuous (fun y => (fderiv ℝ (χ n) y (EuclideanSpace.single j (1 : ℝ))) • v y) :=
      fun n => ((hsmooth n).continuous_fderiv (by simp)).clm_apply continuous_const |>.smul hvc
    have hsplit : ∀ n : ℕ, pdir j (fun y => χ n y • v y) - pdir j v
        = (fun y => (χ n y - 1) • pdir j v y)
          + (fun y => (fderiv ℝ (χ n) y (EuclideanSpace.single j (1 : ℝ))) • v y) := by
      intro n
      funext y
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [cutoffApprox_pdir_smul (χ n) v (hsmooth n) hvs j y, sub_smul, one_smul]
      abel
    have hbd2 : ∀ n : ℕ, eLpNorm (pdir j (fun y => χ n y • v y) - pdir j v) 2 volume
        ≤ eLpNorm (fun y => (χ n y - 1) • pdir j v y) 2 volume
          + eLpNorm (fun y => (fderiv ℝ (χ n) y (EuclideanSpace.single j (1 : ℝ))) • v y) 2 volume := by
      intro n
      rw [hsplit n]
      exact eLpNorm_add_le (hA n).aestronglyMeasurable (hB n).aestronglyMeasurable (by norm_num)
    have hT1 : Tendsto (fun n : ℕ => eLpNorm (fun y => (χ n y - 1) • pdir j v y) 2 volume)
        atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (holdTail_eLpNorm_tendsto_two (pdir j v) (hv2 j)) (fun n => zero_le) (fun n => ?_)
      calc eLpNorm (fun y => (χ n y - 1) • pdir j v y) 2 volume
          ≤ eLpNorm (fun y => ‖(holdTail n).indicator (pdir j v) y‖) 2 volume :=
            eLpNorm_mono_real (fun y => cutoffApprox_pt_bound n (χ n) (pdir j v)
              (fun z => (hχ n).2.2.1 z) (fun z hz => (hχ n).2.2.2.1 z hz) y)
        _ = eLpNorm ((holdTail n).indicator (pdir j v)) 2 volume := eLpNorm_norm _
    have hsum0 := hT1.add (hCut v hv6 j)
    rw [add_zero] at hsum0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum0
      (fun n => zero_le) hbd2

theorem cutoffApprox_holds : CutoffApprox :=
  cutoffApprox_of cutoffFamilyExists_holds cutoffHolder_holds

end UnforcedLeray.Short.PartIIIb.Concrete
