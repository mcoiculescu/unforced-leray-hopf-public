import UnforcedLeray.Units.B0449.GraphResolventL4

/-!
# Continuous L4 phase path of the graph representative
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

local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

theorem globalRealChartRep_memLp_q (τ : ℝ) :
    MemLp (globalRealChartRep hP1 hqq' hq hν hTime hLap τ) qE volume := by
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

/-- The Lq-valued trace after taking real parts. -/
def globalRealChartRepLqPath : ℝ → Lp Space qE (volume : Measure Space) :=
  fun τ => (reV.compLpL qE volume) (phaseRep (q := qE) (by exact ENNReal.ofReal_ne_top) hTime τ)

/-- The L4 class of the globally continuous real graph representative. -/
def globalRealChartRepL4Path : ℝ → Lp Space 4 (volume : Measure Space) :=
  fun τ => (globalRealChartRep_memLp_four hP1 hqq' hq hν hTime hLap hq4 τ).toLp _

theorem globalRealChartRepL4Path_eq_toLp (τ : ℝ) :
    globalRealChartRepL4Path hP1 hqq' hq hq4 hν hTime hLap τ =
      (globalRealChartRep_memLp_four hP1 hqq' hq hν hTime hLap hq4 τ).toLp _ := rfl

theorem continuous_globalRealChartRepLqPath :
    Continuous (globalRealChartRepLqPath hTime) := by
  exact (reV.compLpL qE volume).continuous.comp
    (continuous_phaseRep (q := qE) (by exact ENNReal.ofReal_ne_top) hTime)

theorem globalRealChartRepLqPath_eq_toLp (τ : ℝ) :
    globalRealChartRepLqPath hTime τ =
      (globalRealChartRep_memLp_q hP1 hqq' hq hν hTime hLap τ).toLp _ := by
  apply Lp.ext
  filter_upwards [reV.coeFn_compLpL (μ := volume) (p := qE)
      (phaseRep (q := qE) (by exact ENNReal.ofReal_ne_top) hTime τ),
    (globalRealChartRep_ae_phaseRepC hP1 hqq' hq hν hTime hLap τ).symm,
    MemLp.coeFn_toLp (globalRealChartRep_memLp_q hP1 hqq' hq hν hTime hLap τ)] with y hy hc ht
  change ((reV.compLpL qE volume)
      (phaseRep (q := qE) (by exact ENNReal.ofReal_ne_top) hTime τ) : Lp Space qE volume) y = _
  calc
    _ = reV (phaseRep (q := qE) (by exact ENNReal.ofReal_ne_top) hTime τ y) := hy
    _ = realPartVector (phaseRepC (q := qE) (by exact ENNReal.ofReal_ne_top)
        hTime (τ : AddCircle P) y) := by
      rw [phaseRepC_coe]
      ext i
      simp [realPartVector, reV_apply]
    _ = globalRealChartRep hP1 hqq' hq hν hTime hLap τ y := hc
    _ = ((globalRealChartRep_memLp_q hP1 hqq' hq hν hTime hLap τ).toLp _) y := ht.symm

/-- The L4 path distance is controlled by the continuous Lq trace distance. -/
theorem globalRealChartRepL4Path_dist_pow_le (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ τ y, ‖globalRealChartRep hP1 hqq' hq hν hTime hLap τ y‖ ≤ M)
    (τ σ : ℝ) :
    dist (globalRealChartRepL4Path hP1 hqq' hq hq4 hν hTime hLap τ)
      (globalRealChartRepL4Path hP1 hqq' hq hq4 hν hTime hLap σ) ^ (4 : ℝ) ≤
      (2 * M) ^ (4 - qR) *
        dist (globalRealChartRepLqPath hTime τ) (globalRealChartRepLqPath hTime σ) ^ qR := by
  let f : Space → Space := globalRealChartRep hP1 hqq' hq hν hTime hLap τ
  let g : Space → Space := globalRealChartRep hP1 hqq' hq hν hTime hLap σ
  let d : Space → Space := fun y => f y - g y
  have hfq := globalRealChartRep_memLp_q hP1 hqq' hq hν hTime hLap τ
  have hgq := globalRealChartRep_memLp_q hP1 hqq' hq hν hTime hLap σ
  have hf4 := globalRealChartRep_memLp_four hP1 hqq' hq hν hTime hLap hq4 τ
  have hg4 := globalRealChartRep_memLp_four hP1 hqq' hq hν hTime hLap hq4 σ
  have hdq : MemLp d qE volume := hfq.sub hgq
  have hd4 : MemLp d 4 volume := hf4.sub hg4
  have hdbound : ∀ᵐ y ∂volume, ‖d y‖ ≤ 2 * M := by
    apply ae_of_all
    intro y
    dsimp [d, f, g]
    calc
      ‖globalRealChartRep hP1 hqq' hq hν hTime hLap τ y -
          globalRealChartRep hP1 hqq' hq hν hTime hLap σ y‖ ≤
          ‖globalRealChartRep hP1 hqq' hq hν hTime hLap τ y‖ +
            ‖globalRealChartRep hP1 hqq' hq hν hTime hLap σ y‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hbound τ y) (hbound σ y)
      _ = 2 * M := by ring
  have hinterp := eLpNorm_four_pow_le_of_bound (f := d) (q := qR) (M := 2 * M)
    (by linarith) hq4 (by positivity) hdq hdbound
  have hqDiff : globalRealChartRepLqPath hTime τ - globalRealChartRepLqPath hTime σ =
      (hdq.toLp d) := by
    rw [globalRealChartRepLqPath_eq_toLp hP1 hqq' hq hν hTime hLap τ,
      globalRealChartRepLqPath_eq_toLp hP1 hqq' hq hν hTime hLap σ]
    exact (MemLp.toLp_sub hfq hgq).symm
  have h4Diff : globalRealChartRepL4Path hP1 hqq' hq hq4 hν hTime hLap τ -
      globalRealChartRepL4Path hP1 hqq' hq hq4 hν hTime hLap σ = hd4.toLp d := by
    change (hf4.toLp _ - hg4.toLp _) = _
    exact (MemLp.toLp_sub hf4 hg4).symm
  have hqNorm : eLpNorm d qE volume =
      ENNReal.ofReal (dist (globalRealChartRepLqPath hTime τ)
        (globalRealChartRepLqPath hTime σ)) := by
    have hqEdist : edist (globalRealChartRepLqPath hTime τ)
        (globalRealChartRepLqPath hTime σ) = eLpNorm d qE volume := by
      rw [globalRealChartRepLqPath_eq_toLp hP1 hqq' hq hν hTime hLap τ,
        globalRealChartRepLqPath_eq_toLp hP1 hqq' hq hν hTime hLap σ]
      exact Lp.edist_toLp_toLp _ _ hfq hgq
    calc
      eLpNorm d qE volume = edist (globalRealChartRepLqPath hTime τ)
          (globalRealChartRepLqPath hTime σ) := hqEdist.symm
      _ = ENNReal.ofReal (dist (globalRealChartRepLqPath hTime τ)
          (globalRealChartRepLqPath hTime σ)) := Lp.edist_dist _ _
  have h4Dist : dist (globalRealChartRepL4Path hP1 hqq' hq hq4 hν hTime hLap τ)
      (globalRealChartRepL4Path hP1 hqq' hq hq4 hν hTime hLap σ) =
      (eLpNorm d 4 volume).toReal := by
    rw [globalRealChartRepL4Path_eq_toLp hP1 hqq' hq hq4 hν hTime hLap τ,
      globalRealChartRepL4Path_eq_toLp hP1 hqq' hq hq4 hν hTime hLap σ]
    rw [Lp.dist_edist, Lp.edist_toLp_toLp]
    rfl
  have htop : ENNReal.ofReal ((2 * M) ^ (4 - qR)) *
      eLpNorm d qE volume ^ qR < ∞ := by
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) hdq.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop.ne hinterp
  rw [← ENNReal.toReal_rpow] at hreal
  rw [ENNReal.toReal_mul] at hreal
  rw [← ENNReal.toReal_rpow] at hreal
  have hK : 0 ≤ (2 * M) ^ (4 - qR) :=
    Real.rpow_nonneg (by positivity : 0 ≤ 2 * M) (4 - qR)
  rw [ENNReal.toReal_ofReal hK] at hreal
  rw [hqNorm, ENNReal.toReal_ofReal dist_nonneg] at hreal
  simpa only [h4Dist] using hreal

/-- The phase trace's continuous Lq path and uniform pointwise bound give a continuous L4 path. -/
theorem continuous_globalRealChartRepL4Path :
    Continuous (globalRealChartRepL4Path hP1 hqq' hq hq4 hν hTime hLap) := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_globalRealChartRep_uniform_bound hP1 hqq' hq hν hTime hLap
  rw [continuous_iff_continuousAt]
  intro τ₀
  let f4 : ℝ → Lp Space 4 (volume : Measure Space) :=
    globalRealChartRepL4Path hP1 hqq' hq hq4 hν hTime hLap
  let fq : ℝ → Lp Space qE (volume : Measure Space) := globalRealChartRepLqPath hTime
  let Q : ℝ → ℝ := fun τ => dist (fq τ) (fq τ₀)
  let U : ℝ → ℝ := fun τ => (2 * M) ^ (4 - qR) * Q τ ^ qR
  let G : ℝ → ℝ := fun τ => Real.sqrt (Real.sqrt (U τ))
  let V : ℝ → ℝ := fun τ => dist (f4 τ) (f4 τ₀)
  have hQcont : Continuous Q := by
    exact continuous_dist.comp
      ((continuous_globalRealChartRepLqPath hTime).prodMk continuous_const)
  have hQtend : Tendsto Q (𝓝 τ₀) (𝓝 0) := by
    have h := hQcont.tendsto τ₀
    simpa [Q] using h
  have hpowtend : Tendsto (fun τ => Q τ ^ qR) (𝓝 τ₀) (𝓝 0) :=
    hQtend.rpow_const_nhds_zero (by linarith)
  have hUtend : Tendsto U (𝓝 τ₀) (𝓝 0) := by
    simpa [U] using (tendsto_const_nhds.mul hpowtend)
  have hGtend : Tendsto G (𝓝 τ₀) (𝓝 0) := by
    have h := ((Real.continuous_sqrt.comp Real.continuous_sqrt).tendsto 0).comp hUtend
    change Tendsto (fun τ => Real.sqrt (Real.sqrt (U τ))) (𝓝 τ₀) (𝓝 0)
    simpa only [Function.comp_def, Real.sqrt_zero] using h
  have hVG : ∀ τ, V τ ≤ G τ := by
    intro τ
    have hV4 : V τ ^ (4 : ℝ) ≤ U τ := by
      simpa [V, U, Q, f4, fq] using
        globalRealChartRepL4Path_dist_pow_le hP1 hqq' hq hq4 hν hTime hLap
          M hM hbound τ τ₀
    have hU0 : 0 ≤ U τ := by
      dsimp [U, Q]
      positivity
    have hV0 : 0 ≤ V τ := dist_nonneg
    have hG0 : 0 ≤ G τ := Real.sqrt_nonneg _
    have hGsq : (Real.sqrt (Real.sqrt (U τ))) ^ 2 = Real.sqrt (U τ) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    have hUsq : (Real.sqrt (U τ)) ^ 2 = U τ := Real.sq_sqrt hU0
    have hG4 : G τ ^ 4 = U τ := by
      rw [show G τ ^ 4 = (G τ ^ 2) ^ 2 by ring, hGsq, hUsq]
    have hG4rpow : G τ ^ (4 : ℝ) = U τ := by
      calc
        G τ ^ (4 : ℝ) = G τ ^ 4 := Real.rpow_natCast _ _
        _ = U τ := hG4
    by_contra hnot
    have hlt : G τ < V τ := lt_of_not_ge hnot
    have hpow : G τ ^ (4 : ℝ) < V τ ^ (4 : ℝ) :=
      Real.rpow_lt_rpow hG0 hlt (by norm_num)
    rw [hG4rpow] at hpow
    exact (not_lt_of_ge hV4) hpow
  have hVtend : Tendsto V (𝓝 τ₀) (𝓝 0) :=
    Filter.Tendsto.squeeze tendsto_const_nhds hGtend
      (show (fun _ : ℝ => 0) ≤ V from fun τ => dist_nonneg)
      (show V ≤ G from hVG)
  have hpath : Tendsto f4 (𝓝 τ₀) (𝓝 (f4 τ₀)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h := (Metric.tendsto_nhds.1 hVtend) ε hε
    simpa [V, Real.dist_eq, abs_of_nonneg dist_nonneg] using h
  simpa [f4, ContinuousAt] using hpath

end UnforcedLeray.B0449
