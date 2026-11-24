import UnforcedLeray.Units.B0449.GraphResolventPhase
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Every-phase identification for the glued B0449 representative

The locally continuous chart candidates agree with the continuous Banach-valued phase trace at
every phase. This leaf first extracts a full-measure set of good nearby slices from each actual
central-strip identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

variable {P qR qR' ν : ℝ}
variable [Fact (0 < P)] [Fact (1 ≤ ENNReal.ofReal qR)]
variable (hP1 : P ≤ 1) (hqq' : qR.HolderConjugate qR') (hq : 5 / 2 < qR)
variable (hν : 0 < ν)
variable {w a b : Yq P (ENNReal.ofReal qR)}
variable (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)
variable (e : CVec3)

local notation "qE" => ENNReal.ofReal qR

/-- The scalar Lq phase trace obtained by applying the fixed projection `dotL e`. -/
def phaseScalarPath (t : ℝ) : Lp ℂ qE (volume : Measure Space) :=
  (dotL e).compLpL qE (volume : Measure Space)
    (phaseRepC (q := qE) (by exact ENNReal.ofReal_ne_top) hTime (t : AddCircle P))

theorem continuous_phaseScalarPath : Continuous (phaseScalarPath hTime e) := by
  exact ((dotL e).compLpL qE (volume : Measure Space)).continuous.comp
    ((phaseRepC (q := qE) (by exact ENNReal.ofReal_ne_top) hTime).continuous.comp
      (AddCircle.continuous_mk' P))

theorem coeFn_phaseScalarPath (t : ℝ) :
    phaseScalarPath hTime e t =ᵐ[volume]
      (fun y => dotL e (phaseRepC (q := qE) (by exact ENNReal.ofReal_ne_top)
        hTime (t : AddCircle P) y)) := by
  exact (dotL e).coeFn_compLpL
    (phaseRepC (q := qE) (by exact ENNReal.ofReal_ne_top) hTime (t : AddCircle P))

/-- For almost every nearby chart time, the glued scalar slice is the scalar phase trace. -/
theorem ae_globalChartRep_eq_phaseScalar_near_center (τ₀ : ℝ) :
    ∀ᵐ s ∂(volume.restrict (Ioo (-(1 / 8 : ℝ)) (1 / 8))),
      (fun y => globalChartRep hP1 hqq' hq hν hTime hLap e (τ₀ + s) y) =ᵐ[volume]
        (phaseScalarPath hTime e (τ₀ + s) : Space → ℂ) := by
  let f := chosenLocalChart hP1 hqq' hq hν hTime hLap e τ₀
  have hS : MeasurableSet chartCentral := measurableSet_Ioo.prod MeasurableSet.univ
  have hlocal := (ae_restrict_iff' hS).mp
    (chosenLocalChart_ae hP1 hqq' hq hν hTime hLap e τ₀)
  rw [Measure.volume_eq_prod ℝ Space] at hlocal
  have hlocalSlices := Measure.ae_ae_of_ae_prod hlocal
  have hqtop : qE ≠ ⊤ := ENNReal.ofReal_ne_top
  have htraceLine := PhaseTrace.phaseRep_ae_line hqtop hTime
  have htraceShift : ∀ᵐ s : ℝ ∂volume,
      phaseRep hqtop hTime (τ₀ + s) = w ((τ₀ + s : ℝ) : AddCircle P) := by
    have htmp :=
      (measurePreserving_add_right (volume : Measure ℝ) τ₀).quasiMeasurePreserving.ae htraceLine
    filter_upwards [htmp] with s hs
    simpa [add_comm] using hs
  have hcentral : ∀ᵐ s : ℝ ∂volume, s ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8) →
      (fun y => globalChartRep hP1 hqq' hq hν hTime hLap e (τ₀ + s) y) =ᵐ[volume]
        (phaseScalarPath hTime e (τ₀ + s) : Space → ℂ) := by
    filter_upwards [hlocalSlices, htraceShift] with s hs htrace
    intro hsI
    have hslice : ∀ᵐ z ∂volume,
        f (s, z) = dotL e (chartJ w ν τ₀ (s, z)) := by
      filter_upwards [hs] with z hz
      exact hz ⟨hsI, trivial⟩
    have hphaseEq : phaseRepC (q := qE) hqtop hTime
        ((τ₀ + s : ℝ) : AddCircle P) = w ((τ₀ + s : ℝ) : AddCircle P) := by
      rw [phaseRepC_coe]
      exact htrace
    have hphasePoint :
        (fun y => jointRep w (((τ₀ + s : ℝ) : AddCircle P), y)) =ᵐ[volume]
          (fun y => phaseRepC (q := qE) hqtop hTime
            ((τ₀ + s : ℝ) : AddCircle P) y) := by
      have hw := jointRep_slice w ((τ₀ + s : ℝ) : AddCircle P)
      have hphase := Lp.ext_iff.mp hphaseEq
      exact hw.trans hphase.symm
    have hphaseScalar := coeFn_phaseScalarPath hTime e (τ₀ + s)
    have hscale : ∀ᵐ z ∂volume,
        dotL e (chartJ w ν τ₀ (s, z)) =
          phaseScalarPath hTime e (τ₀ + s) (sc ν s • z) := by
      have hpoint := (qmp_smul (sc_pos hν s).ne').ae_eq_comp hphasePoint
      have hpoint' := (qmp_smul (sc_pos hν s).ne').ae_eq_comp hphaseScalar
      filter_upwards [hpoint, hpoint'] with z hz hz'
      exact (congrArg (dotL e) hz).trans hz'.symm
    have hlocalSlice : ∀ᵐ z ∂volume,
        f (s, z) = phaseScalarPath hTime e (τ₀ + s) (sc ν s • z) := by
      filter_upwards [hslice, hscale] with z hz hz'
      exact hz.trans hz'
    have hcancelExp : Real.exp (s / 2) * Real.exp (-s / 2) = 1 := by
      rw [← Real.exp_add]
      have hsarg : s / 2 + -s / 2 = 0 := by ring
      rw [hsarg, Real.exp_zero]
    have hscaleCoord : ∀ z : Space,
        Real.exp (s / 2) • ((Real.sqrt ν)⁻¹ • (sc ν s • z)) = z := by
      intro z
      have hsqrt : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.2 hν).ne'
      have hcoef : Real.exp (s / 2) * (Real.sqrt ν)⁻¹ *
          (Real.exp (-s / 2) * Real.sqrt ν) = 1 := by
        calc
          _ = (Real.exp (s / 2) * Real.exp (-s / 2)) *
              ((Real.sqrt ν)⁻¹ * Real.sqrt ν) := by ring
          _ = 1 := by rw [hcancelExp, inv_mul_cancel₀ hsqrt]; norm_num
      rw [sc, smul_smul, smul_smul, hcoef, one_smul]
    have hglobalComp : ∀ᵐ z ∂volume,
        globalChartRep hP1 hqq' hq hν hTime hLap e (τ₀ + s) (sc ν s • z) =
          phaseScalarPath hTime e (τ₀ + s) (sc ν s • z) := by
      filter_upwards [hlocalSlice] with z hz
      have hpatch := globalChartRep_eq_fixedChartExpression hP1 hqq' hq hν hTime hLap e
        (τ₀ := τ₀) (τ := τ₀ + s) (y := sc ν s • z) (by
          rw [abs_lt]
          constructor <;> linarith [hsI.1, hsI.2])
      have hcoord : (τ₀ + s - τ₀,
          Real.exp ((τ₀ + s - τ₀) / 2) • ((Real.sqrt ν)⁻¹ • (sc ν s • z))) = (s, z) := by
        apply Prod.ext
        · ring
        · simpa using hscaleCoord z
      rw [hpatch]
      change chosenLocalChart hP1 hqq' hq hν hTime hLap e τ₀
          (τ₀ + s - τ₀,
            Real.exp ((τ₀ + s - τ₀) / 2) • ((Real.sqrt ν)⁻¹ • (sc ν s • z))) = _
      rw [hcoord]
      exact hz
    have hb : (sc ν s)⁻¹ ≠ 0 := inv_ne_zero (sc_pos hν s).ne'
    have hback := (qmp_smul hb).ae_eq_comp hglobalComp
    have hinv : sc ν s * (sc ν s)⁻¹ = 1 := mul_inv_cancel₀ (sc_pos hν s).ne'
    filter_upwards [hback] with y hy
    simpa [Function.comp_def, smul_smul, hinv] using hy
  have hcentralRestricted := (ae_restrict_iff' measurableSet_Ioo).mpr hcentral
  exact hcentralRestricted

/-- The glued scalar representative agrees a.e. in space with the phase trace at every time. -/
theorem globalChartRep_ae_phaseScalar (τ : ℝ) :
    (fun y => globalChartRep hP1 hqq' hq hν hTime hLap e τ y) =ᵐ[volume]
      (phaseScalarPath hTime e τ : Space → ℂ) := by
  let good : Set ℝ := {s | s ∉ Ioo (-(1 / 8 : ℝ)) (1 / 8) ∨
    (fun y => globalChartRep hP1 hqq' hq hν hTime hLap e (τ + s) y) =ᵐ[volume]
      (phaseScalarPath hTime e (τ + s) : Space → ℂ)}
  have hnear := ae_globalChartRep_eq_phaseScalar_near_center hP1 hqq' hq hν hTime hLap e τ
  have hgoodAE : ∀ᵐ s : ℝ ∂volume, s ∈ good := by
    have hImp := (ae_restrict_iff' measurableSet_Ioo).mp hnear
    filter_upwards [hImp] with s hs
    by_cases hsI : s ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
    · exact Or.inr (hs hsI)
    · exact Or.inl hsI
  have hdense : Dense good := Measure.dense_of_ae hgoodAE
  obtain ⟨u, huStrict, huMem, huTend⟩ :=
    hdense.exists_seq_strictMono_tendsto_of_lt (by norm_num : -(1 / 8 : ℝ) < 0)
  have huI : ∀ n, u n ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8) := by
    intro n
    rcases huMem n with ⟨hbelow, hgood⟩
    rcases hbelow with ⟨hlo, hhi⟩
    exact ⟨hlo, by linarith⟩
  have hEqSlice : ∀ n,
      (fun y => globalChartRep hP1 hqq' hq hν hTime hLap e (τ + u n) y) =ᵐ[volume]
        (phaseScalarPath hTime e (τ + u n) : Space → ℂ) := by
    intro n
    rcases huMem n with ⟨_, hgood⟩
    rcases hgood with hnot | heq
    · exact (False.elim (hnot (huI n)))
    · exact heq
  have htend : Tendsto (fun n : ℕ => τ + u n) atTop (𝓝 τ) := by
    simpa only [add_zero] using (tendsto_const_nhds.add huTend :
      Tendsto (fun n : ℕ => τ + u n) atTop (𝓝 (τ + 0)))
  have hLp : Tendsto (fun n : ℕ => phaseScalarPath hTime e (τ + u n)) atTop
      (𝓝 (phaseScalarPath hTime e τ)) :=
    (continuous_phaseScalarPath hTime e).continuousAt.tendsto.comp htend
  have hmeasure := MeasureTheory.tendstoInMeasure_of_tendsto_Lp hLp
  obtain ⟨ns, hnsStrict, hnsAE⟩ := hmeasure.exists_seq_tendsto_ae
  have htendSub : Tendsto (fun n : ℕ => τ + u (ns n)) atTop (𝓝 τ) := by
    have hsub : Tendsto (fun n : ℕ => u (ns n)) atTop (𝓝 0) :=
      huTend.comp hnsStrict.tendsto_atTop
    simpa only [add_zero] using (tendsto_const_nhds.add hsub :
      Tendsto (fun n : ℕ => τ + u (ns n)) atTop (𝓝 (τ + 0)))
  have hpatchCont (y : Space) : Continuous (fun t : ℝ =>
      fixedChartExpression hP1 hqq' hq hν hTime hLap e τ (t, y)) := by
    exact (continuous_fixedChartExpression hP1 hqq' hq hν hTime hLap e τ).comp
      (continuous_id.prodMk continuous_const)
  have hFconv (y : Space) : Tendsto
      (fun n : ℕ => globalChartRep hP1 hqq' hq hν hTime hLap e (τ + u (ns n)) y)
      atTop (𝓝 (globalChartRep hP1 hqq' hq hν hTime hLap e τ y)) := by
    have hpatchTend : Tendsto
        (fun n : ℕ => fixedChartExpression hP1 hqq' hq hν hTime hLap e τ
          (τ + u (ns n), y)) atTop
        (𝓝 (fixedChartExpression hP1 hqq' hq hν hTime hLap e τ (τ, y))) :=
      (hpatchCont y).continuousAt.tendsto.comp htendSub
    have hpatchEq : ∀ n, globalChartRep hP1 hqq' hq hν hTime hLap e
        (τ + u (ns n)) y = fixedChartExpression hP1 hqq' hq hν hTime hLap e τ
          (τ + u (ns n), y) := by
      intro n
      apply globalChartRep_eq_fixedChartExpression hP1 hqq' hq hν hTime hLap e
        (τ₀ := τ) (τ := τ + u (ns n)) (y := y)
      rw [abs_lt]
      constructor
      · have h := (huI (ns n)).1
        linarith
      · have h := (huI (ns n)).2
        linarith
    have hpatchAt : globalChartRep hP1 hqq' hq hν hTime hLap e τ y =
        fixedChartExpression hP1 hqq' hq hν hTime hLap e τ (τ, y) :=
      globalChartRep_eq_fixedChartExpression hP1 hqq' hq hν hTime hLap e
        (τ₀ := τ) (τ := τ) (y := y) (by norm_num)
    have hseqEq : (fun n : ℕ =>
        fixedChartExpression hP1 hqq' hq hν hTime hLap e τ (τ + u (ns n), y)) =ᶠ[atTop]
          (fun n => globalChartRep hP1 hqq' hq hν hTime hLap e (τ + u (ns n)) y) :=
      Filter.Eventually.of_forall fun n => (hpatchEq n).symm
    have hconv := Tendsto.congr' hseqEq hpatchTend
    simpa [hpatchAt] using hconv
  have hEqAll : ∀ᵐ y ∂volume, ∀ n,
      globalChartRep hP1 hqq' hq hν hTime hLap e (τ + u (ns n)) y =
        phaseScalarPath hTime e (τ + u (ns n)) y := by
    rw [ae_all_iff]
    intro n
    exact hEqSlice (ns n)
  filter_upwards [hEqAll, hnsAE] with y hy hlim
  have hlimF : Tendsto
      (fun n : ℕ => globalChartRep hP1 hqq' hq hν hTime hLap e (τ + u (ns n)) y)
      atTop (𝓝 (phaseScalarPath hTime e τ y)) := by
    refine Tendsto.congr' ?_ hlim
    exact Eventually.of_forall fun n => (hy n).symm
  exact tendsto_nhds_unique (hFconv y) hlimF

end UnforcedLeray.B0449
