import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.Defs

/-!
# `CutoffHolder`: Hölder on annuli for the radial cutoff error

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.

For a cutoff `χₙ` vanishing off the annulus `n+1 ≤ ‖y‖ ≤ 2(n+1)` with `‖∇χₙ‖ ≤ C/(n+1)`,
the error `‖∂ⱼχₙ · v‖₂` is bounded by `2C K^{1/3} ‖v 1_{‖y‖≥n+1}‖₆`, where `K = vol(B₁)`:
the integrand is supported in the ball of radius `2(n+1)`, Hölder with exponents `1/2 = 1/6 + 1/3`
on that ball gives the volume factor `(2(n+1))` times `K^{1/3}`, and the `L⁶` tail tends to zero
by dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Tail set `{y | n+1 ≤ ‖y‖}` (helper for `CutoffHolder`). -/
def holdTail (n : ℕ) : Set Space := {y : Space | (n : ℝ) + 1 ≤ ‖y‖}

/-- Ball set `{y | ‖y‖ ≤ 2(n+1)}` (helper for `CutoffHolder`). -/
def holdBall (n : ℕ) : Set Space := Metric.closedBall 0 (2 * ((n : ℝ) + 1))

theorem holdTail_measurableSet (n : ℕ) : MeasurableSet (holdTail n) :=
  measurableSet_le measurable_const measurable_norm

theorem holdTail_eLpNorm_tendsto (v : Space → CVec3) (hv : MemLp v 6 volume) :
    Tendsto (fun n : ℕ => eLpNorm ((holdTail n).indicator v) 6 volume) atTop (𝓝 0) := by
  have h6 : (6 : ℝ≥0∞).toReal = 6 := by norm_num
  have hfin : (∫⁻ x, ‖v x‖ₑ ^ (6 : ℝ)) ≠ ∞ := by
    have h := hv.2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h6] at h
    exact ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h).ne
  have hlim : Tendsto (fun n : ℕ => ∫⁻ x, ‖(holdTail n).indicator v x‖ₑ ^ (6 : ℝ)) atTop (𝓝 0) := by
    have hmeas : ∀ n : ℕ, AEMeasurable (fun x => ‖(holdTail n).indicator v x‖ₑ ^ (6 : ℝ)) volume :=
      fun n => ((hv.1.indicator (holdTail_measurableSet n)).enorm).pow_const (6 : ℝ)
    have hdc := tendsto_lintegral_filter_of_dominated_convergence' (μ := volume) (l := atTop)
      (F := fun n : ℕ => fun x => ‖(holdTail n).indicator v x‖ₑ ^ (6 : ℝ))
      (f := fun _ => (0 : ℝ≥0∞)) (fun x => ‖v x‖ₑ ^ (6 : ℝ))
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
  have hI := ((ENNReal.continuous_rpow_const (y := (1 / (6 : ℝ)))).tendsto (0 : ℝ≥0∞)).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hI
  refine Tendsto.congr (fun n => ?_) hI
  show (∫⁻ x, ‖(holdTail n).indicator v x‖ₑ ^ (6 : ℝ)) ^ (1 / (6 : ℝ)) = _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h6]

theorem cutoffHolder_holds : CutoffHolder := by
  intro C χ hχ hin hout hbd v hv j
  have hC : 0 ≤ C := by
    have h0 := hbd 0 0
    norm_num at h0
    exact le_trans (norm_nonneg _) h0
  -- pointwise bound: |∂ⱼχₙ| |v| ≤ (C/(n+1)) |1_{ball} 1_{tail} v|
  have hpt : ∀ (n : ℕ) (y : Space),
      ‖(fderiv ℝ (χ n) y (EuclideanSpace.single j (1 : ℝ))) • v y‖ ≤
        ‖(C / ((n : ℝ) + 1)) • (holdBall n).indicator ((holdTail n).indicator v) y‖ := by
    intro n y
    by_cases h1 : ‖y‖ < (n : ℝ) + 1
    · rw [hin n y h1]
      simp
    by_cases h2 : ‖y‖ > 2 * ((n : ℝ) + 1)
    · rw [hout n y h2]
      simp
    push_neg at h1 h2
    have hyT : y ∈ holdTail n := h1
    have hyS : y ∈ holdBall n :=
      Metric.mem_closedBall.2 (by rw [dist_zero_right]; exact h2)
    rw [Set.indicator_of_mem hyS, Set.indicator_of_mem hyT, norm_smul, norm_smul]
    have hc : 0 ≤ C / ((n : ℝ) + 1) := div_nonneg hC (by positivity)
    rw [Real.norm_of_nonneg hc]
    have hle : ‖fderiv ℝ (χ n) y (EuclideanSpace.single j (1 : ℝ))‖ ≤ C / ((n : ℝ) + 1) := by
      have h1' := ContinuousLinearMap.le_opNorm (fderiv ℝ (χ n) y) (EuclideanSpace.single j (1 : ℝ))
      rw [EuclideanSpace.norm_single, norm_one, mul_one] at h1'
      exact h1'.trans (hbd n y)
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  -- volume of the ball of radius 2(n+1)
  have hcube : ∀ a : ℝ, 0 ≤ a → (a ^ 3) ^ (1 / 3 : ℝ) = a := by
    intro a ha
    have h := Real.pow_rpow_inv_natCast ha (n := 3) (by norm_num)
    simpa [one_div] using h
  set K0 : ℝ≥0∞ := volume (Metric.closedBall (0 : Space) 1) with hK0
  have hV : ∀ n : ℕ, volume (holdBall n) = ENNReal.ofReal ((2 * ((n : ℝ) + 1)) ^ 3) * K0 := by
    intro n
    have ha : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by positivity
    unfold holdBall
    rw [Measure.addHaar_closedBall' (μ := volume) (x := 0) (r := 2 * ((n : ℝ) + 1)) ha,
      finrank_euclideanSpace_fin]
  have hK0top : K0 ≠ ∞ := measure_closedBall_lt_top.ne
  set L : ℝ≥0∞ := ENNReal.ofReal (2 * C) * K0 ^ (1 / 3 : ℝ) with hL
  have hLtop : L ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK0top)
  have hbound : ∀ n : ℕ, ‖C / ((n : ℝ) + 1)‖ₑ * (volume (holdBall n)) ^ (1 / 3 : ℝ) ≤ L := by
    intro n
    have hc : 0 ≤ C / ((n : ℝ) + 1) := div_nonneg hC (by positivity)
    have ha : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by positivity
    rw [hV n, Real.enorm_eq_ofReal hc, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), hcube _ ha, hL,
      ← mul_assoc, ← ENNReal.ofReal_mul hc]
    have key : C / ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1)) = 2 * C := by
      field_simp
    rw [key]
  -- pointwise-in-n estimate of the cutoff error
  have hest : ∀ n : ℕ, eLpNorm (fun y => (fderiv ℝ (χ n) y (EuclideanSpace.single j (1 : ℝ))) • v y)
      2 volume ≤ L * eLpNorm ((holdTail n).indicator v) 6 volume := by
    intro n
    have hc : 0 ≤ C / ((n : ℝ) + 1) := div_nonneg hC (by positivity)
    have hHaes : AEStronglyMeasurable ((holdTail n).indicator v) volume :=
      hv.1.indicator (holdTail_measurableSet n)
    have h1 : eLpNorm (fun y => (fderiv ℝ (χ n) y (EuclideanSpace.single j (1 : ℝ))) • v y) 2 volume
        ≤ eLpNorm (fun y => ‖(C / ((n : ℝ) + 1)) • (holdBall n).indicator ((holdTail n).indicator v) y‖)
          2 volume :=
      eLpNorm_mono_real (fun y => hpt n y)
    have h3 : eLpNorm ((holdBall n).indicator ((holdTail n).indicator v)) 2 volume
        ≤ eLpNorm ((holdTail n).indicator v) 6 volume * (volume (holdBall n)) ^ (1 / 3 : ℝ) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict (s := holdBall n) measurableSet_closedBall]
      have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (holdBall n))
        (p := 2) (q := 6) (by norm_num) hHaes.restrict
      rw [Measure.restrict_apply_univ] at hH
      have hexp : (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) = (1 / 3 : ℝ) := by
        norm_num
      rw [hexp] at hH
      calc eLpNorm ((holdTail n).indicator v) 2 (volume.restrict (holdBall n))
          ≤ eLpNorm ((holdTail n).indicator v) 6 (volume.restrict (holdBall n))
              * (volume (holdBall n)) ^ (1 / 3 : ℝ) := hH
        _ ≤ eLpNorm ((holdTail n).indicator v) 6 volume * (volume (holdBall n)) ^ (1 / 3 : ℝ) := by
          gcongr
          exact Measure.restrict_le_self
    calc eLpNorm (fun y => (fderiv ℝ (χ n) y (EuclideanSpace.single j (1 : ℝ))) • v y) 2 volume
        ≤ eLpNorm (fun y => ‖(C / ((n : ℝ) + 1)) • (holdBall n).indicator ((holdTail n).indicator v) y‖)
          2 volume := h1
      _ = eLpNorm ((C / ((n : ℝ) + 1)) • (holdBall n).indicator ((holdTail n).indicator v)) 2 volume :=
          eLpNorm_norm _
      _ ≤ ‖C / ((n : ℝ) + 1)‖ₑ * eLpNorm ((holdBall n).indicator ((holdTail n).indicator v)) 2 volume :=
          eLpNorm_const_smul_le
      _ ≤ ‖C / ((n : ℝ) + 1)‖ₑ * (eLpNorm ((holdTail n).indicator v) 6 volume
            * (volume (holdBall n)) ^ (1 / 3 : ℝ)) := by gcongr
      _ = (‖C / ((n : ℝ) + 1)‖ₑ * (volume (holdBall n)) ^ (1 / 3 : ℝ))
            * eLpNorm ((holdTail n).indicator v) 6 volume := by ring
      _ ≤ L * eLpNorm ((holdTail n).indicator v) 6 volume := by gcongr; exact hbound n
  have hL0 : Tendsto (fun n : ℕ => L * eLpNorm ((holdTail n).indicator v) 6 volume) atTop
      (𝓝 (L * 0)) :=
    ENNReal.Tendsto.const_mul (holdTail_eLpNorm_tendsto v hv) (Or.inr hLtop)
  rw [mul_zero] at hL0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL0
    (fun n => by simp) hest

end UnforcedLeray.Short.PartIIIb.Concrete
