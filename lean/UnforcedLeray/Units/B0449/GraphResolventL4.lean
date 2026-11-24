import UnforcedLeray.Units.B0449.GraphResolventRealBound
import UnforcedLeray.Lib.LerayC.Complex

/-!
# L4 consequences of the bounded graph representative

The sharp graph bound gives an L4 phase path by interpolation with the continuous Lq trace.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.RieszLp

variable {P qR qR' ν : ℝ}
variable [Fact (0 < P)] [Fact (1 ≤ ENNReal.ofReal qR)]
variable (hP1 : P ≤ 1) (hqq' : qR.HolderConjugate qR') (hq : 5 / 2 < qR)
variable (hq4 : qR < 4)
variable (hν : 0 < ν)
variable {w a b : Yq P (ENNReal.ofReal qR)}
variable (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)

local notation "qE" => ENNReal.ofReal qR

/-- A bounded `L^q` function belongs to `L^4` when `q<4`, on any measure space. -/
theorem memLp_four_of_memLp_q_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {f : α → E} {q : ℝ} {M : ℝ}
    (hq0 : 0 < q) (hq4 : q < 4) (hM : 0 ≤ M)
    (hf : MemLp f (ENNReal.ofReal q) μ)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) : MemLp f 4 μ := by
  have hqne : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq0).ne'
  have hqtop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hpowq : MemLp (fun x => ‖f x‖ ^ q) 1 μ := by
    have := hf.norm_rpow hqne hqtop
    simpa [ENNReal.toReal_ofReal hq0.le] using this
  have hfacStrong : AEStronglyMeasurable (fun x => ‖f x‖ ^ (4 - q)) μ := by
    exact (Real.continuous_rpow_const (sub_nonneg.mpr hq4.le)).comp_aestronglyMeasurable hf.1.norm
  have hfac : MemLp (fun x => ‖f x‖ ^ (4 - q)) ∞ μ := by
    apply memLp_top_of_bound hfacStrong (M ^ (4 - q))
    filter_upwards [hbound] with x hx
    have hpow := Real.rpow_le_rpow (norm_nonneg _) hx (sub_nonneg.mpr hq4.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hpow
  have hprod : MemLp ((fun x => ‖f x‖ ^ q) * (fun x => ‖f x‖ ^ (4 - q))) 1 μ :=
    hfac.mul hpowq
  have hpow4 : MemLp (fun x => ‖f x‖ ^ (4 : ℝ)) 1 μ := by
    apply (memLp_congr_ae (μ := μ) (p := (1 : ℝ≥0∞)) ?_).1 hprod
    filter_upwards with x
    calc
      ‖f x‖ ^ q * ‖f x‖ ^ (4 - q) = ‖f x‖ ^ (q + (4 - q)) :=
        (Real.rpow_add' (norm_nonneg _) (by linarith : q + (4 - q) ≠ 0)).symm
      _ = ‖f x‖ ^ (4 : ℝ) := by rw [show q + (4 - q) = 4 by ring]
  have hnorm := hpow4
  have hdiv : (4 : ℝ≥0∞) / 4 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
  have hnorm' : MemLp (fun x => ‖f x‖ ^ (4 : ℝ)) ((4 : ℝ≥0∞) / 4) μ := by
    rw [hdiv]
    exact hnorm
  exact (memLp_norm_rpow_iff (p := (4 : ℝ≥0∞)) (q := (4 : ℝ≥0∞)) hf.1
    (by norm_num) (by norm_num)).1 hnorm'

/-- The interpolated fourth-power estimate on an infinite measure space. -/
theorem eLpNorm_four_pow_le_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {f : α → E} {q : ℝ} {M : ℝ}
    (hq0 : 0 < q) (hq4 : q < 4) (hM : 0 ≤ M)
    (hf : MemLp f (ENNReal.ofReal q) μ)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) :
    eLpNorm f 4 μ ^ (4 : ℝ) ≤ ENNReal.ofReal (M ^ (4 - q)) *
      eLpNorm f (ENNReal.ofReal q) μ ^ q := by
  have hqpow : eLpNorm f (ENNReal.ofReal q) μ ^ q = ∫⁻ x, ‖f x‖ₑ ^ q ∂μ := by
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hq0).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le]
    exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' hq0).symm
  change eLpNorm f (↑(4 : ℝ≥0)) μ ^ (↑(4 : ℝ≥0) : ℝ) ≤
    ENNReal.ofReal (M ^ (4 - q)) * eLpNorm f (ENNReal.ofReal q) μ ^ q
  rw [eLpNorm_nnreal_pow_eq_lintegral (f := f) (p := 4) (by norm_num), hqpow]
  have hmeas : AEMeasurable (fun x => ‖f x‖ₑ ^ q) μ :=
    hf.1.enorm.pow_const q
  calc
    ∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂μ ≤
        ∫⁻ x, ENNReal.ofReal (M ^ (4 - q)) * ‖f x‖ₑ ^ q ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with x hx
      have hz : ‖f x‖ₑ ≤ ENNReal.ofReal M := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hx
      have hpow : ‖f x‖ₑ ^ (4 : ℝ) =
          ‖f x‖ₑ ^ q * ‖f x‖ₑ ^ (4 - q) := by
        rw [← ENNReal.rpow_add_of_nonneg q (4 - q) (le_of_lt hq0) (by linarith)]
        congr 1
        ring
      rw [hpow]
      calc
        ‖f x‖ₑ ^ q * ‖f x‖ₑ ^ (4 - q) ≤
            ‖f x‖ₑ ^ q * (ENNReal.ofReal M) ^ (4 - q) :=
          mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hz (by linarith))
        _ = ENNReal.ofReal (M ^ (4 - q)) * ‖f x‖ₑ ^ q := by
          rw [ENNReal.ofReal_rpow_of_nonneg hM (by linarith)]
          exact mul_comm _ _
    _ = ENNReal.ofReal (M ^ (4 - q)) * ∫⁻ x, ‖f x‖ₑ ^ q ∂μ :=
      lintegral_const_mul'' _ hmeas

/-- Every phase of the global real chart representative has the L4 integrability needed by the
projected weak formulation. -/
theorem globalRealChartRep_memLp_four (hq4 : qR < 4) (τ : ℝ) :
    MemLp (globalRealChartRep hP1 hqq' hq hν hTime hLap τ) 4 volume := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_globalRealChartRep_uniform_bound hP1 hqq' hq hν hTime hLap
  have hqmem : MemLp
      (globalRealChartRep hP1 hqq' hq hν hTime hLap τ) qE volume := by
    let trace := phaseRepC (q := qE) (by exact ENNReal.ofReal_ne_top) hTime
      (τ : AddCircle P)
    have hcomp := reV.coeFn_compLpL (μ := volume) (p := qE) trace
    have hrv (v : CVec3) : reV v = realPartVector v := by
      ext i
      simp [realPartVector, reV_apply]
    have hAE : (fun y => ((reV.compLpL qE volume) trace : Lp Space qE volume) y) =ᵐ[volume]
        globalRealChartRep hP1 hqq' hq hν hTime hLap τ := by
      filter_upwards [hcomp, (globalRealChartRep_ae_phaseRepC
        hP1 hqq' hq hν hTime hLap τ).symm] with y hy hc
      calc
        ((reV.compLpL qE volume) trace : Lp Space qE volume) y = reV (trace y) := hy
        _ = realPartVector (trace y) := hrv _
        _ = globalRealChartRep hP1 hqq' hq hν hTime hLap τ y := hc
    exact (Lp.memLp ((reV.compLpL qE volume) trace)).ae_eq hAE
  exact memLp_four_of_memLp_q_of_bound (by linarith : 0 < qR)
    hq4 hM hqmem (ae_of_all _ fun y => hbound τ y)

end UnforcedLeray.B0449
