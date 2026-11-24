import UnforcedLeray.Units.B0449.GraphResolventST
import UnforcedLeray.Units.B0449.FixedCutoff
import UnforcedLeray.Lib.HeatR3B.SpaceTime

/-!
# Lq cutoff fields and bounded chart representative

For the small-period regime used by the final construction, the actual B0449 graph fields lie in
space-time Lq after the fixed cutoff.  The ST resolvent identity then feeds the heat resolvent
bound and supplies a continuous bounded representative.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal SchwartzMap

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0448 UnforcedLeray.Heat

/-- A bounded time multiplier supported in the unit strip preserves the restricted Lq norm up to
its uniform bound. -/
theorem eLpNorm_timeMul_unitStrip_le {q : ℝ≥0∞} {g : ℝ × Space → ℂ}
    {κ : ℝ → ℝ} {M : ℝ}
    (hκbound : ∀ t, ‖(κ t : ℂ)‖ ≤ M)
    (hκzero : ∀ t, t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) → κ t = 0) :
    eLpNorm (fun p : ℝ × Space => (κ p.1 : ℂ) * g p) q volume ≤
      ENNReal.ofReal M * eLpNorm g q
        (volume.restrict (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))) := by
  let S : Set (ℝ × Space) := Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space)
  have hS : MeasurableSet S := measurableSet_Ioo.prod MeasurableSet.univ
  have heq : (fun p : ℝ × Space => (κ p.1 : ℂ) * g p) =ᵐ[volume]
      S.indicator (fun p => (κ p.1 : ℂ) * g p) := by
    filter_upwards [] with p
    by_cases hp : p ∈ S
    · simp [Set.indicator_of_mem hp]
    · have ht : p.1 ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
        fun ht => hp ⟨ht, Set.mem_univ _⟩
      simp [Set.indicator_of_notMem hp, hκzero p.1 ht]
  rw [eLpNorm_congr_ae heq, eLpNorm_indicator_eq_eLpNorm_restrict hS]
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (Eventually.of_forall fun p => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hκbound p.1) (norm_nonneg _)) q

/-- Uniform scalar-projection Lq bound for the joint chart on one strip. -/
theorem eLpNorm_dotL_chartJ_unitStrip_le {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤) {ν : ℝ} (hν : 0 < ν)
    (f : Yq P q) (τ₀ : ℝ) (e : CVec3) :
    eLpNorm (fun p : ℝ × Space => dotL e (chartJ f ν τ₀ p)) q
      (volume.restrict (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))) ≤
        ENNReal.ofReal (‖dotL e‖ *
          (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / q.toReal) * ‖f‖) := by
  let μS : Measure (ℝ × Space) := volume.restrict
    (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  have hμS : μS = ((volume : Measure ℝ).restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2))).prod (volume : Measure Space) := by
    dsimp [μS]
    rw [Measure.volume_eq_prod ℝ Space, ← Measure.prod_restrict, Measure.restrict_univ]
  have hchart : eLpNorm (chartJ f ν τ₀) q μS =
      stripNorm q (fun t z => chartJ f ν τ₀ (t, z)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq, hμS]
    rw [lintegral_prod _ ((stronglyMeasurable_chartJ f ν τ₀).enorm.pow_const _).aemeasurable]
    rfl
  have hchart' : eLpNorm (fun p : ℝ × Space => chartJ f ν τ₀ p) q μS =
      stripNorm q (fun t z => chartJ f ν τ₀ (t, z)) := hchart
  have hslice : ∀ t, (fun z => chartJ f ν τ₀ (t, z)) =ᵐ[volume]
      chartPullback f ν τ₀ 0 t := by
    intro t
    exact chartJ_slice hν f τ₀ t
  have hstrip : stripNorm q (fun t z => chartJ f ν τ₀ (t, z)) =
      stripNorm q (chartPullback f ν τ₀ 0) := by
    unfold stripNorm
    congr 1
    apply lintegral_congr_ae
    filter_upwards [] with t
    apply lintegral_congr_ae
    filter_upwards [hslice t] with z hz
    rw [hz]
  have hpull : stripNorm q (chartPullback f ν τ₀ 0) ≤
      ENNReal.ofReal ((2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^
        (1 / q.toReal) * ‖f‖) := by
    simpa using (stripNorm_le hP1 hν hq f τ₀ 0 (fun _ => (1 : ℂ)) zero_le_one
      (fun _ _ => by simp))
  have hproj := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (f := fun p : ℝ × Space => dotL e (chartJ f ν τ₀ p))
    (g := fun p : ℝ × Space => chartJ f ν τ₀ p) (c := ‖dotL e‖)
    (μ := μS)
    (Eventually.of_forall fun p => (dotL e).le_opNorm _) q
  rw [hchart', hstrip] at hproj
  have hfinal := hproj.trans (mul_le_mul_of_nonneg_left hpull (by positivity))
  calc
    _ ≤ ENNReal.ofReal ‖dotL e‖ * ENNReal.ofReal
        ((2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / q.toReal) * ‖f‖) := hfinal
    _ = ENNReal.ofReal (‖dotL e‖ *
        (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / q.toReal) * ‖f‖) := by
      rw [← ENNReal.ofReal_mul (norm_nonneg (dotL e))]
      congr 1
      ring

/-- The actual cutoff source has a uniform Lq bound in the observation time. -/
theorem chartJ_cutoff_FST_uniform_eLpNorm {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1)
    {qR : ℝ} (hqR : 5 / 2 < qR) [Fact (1 ≤ ENNReal.ofReal qR)]
    {ν : ℝ} (hν : 0 < ν) {w a b : Yq P (ENNReal.ofReal qR)} (e : CVec3) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ τ₀ : ℝ,
      eLpNorm (chartJCutoffFST ν τ₀ e w b a) (ENNReal.ofReal qR) volume ≤ C := by
  let qE : ℝ≥0∞ := ENNReal.ofReal qR
  haveI : Fact (1 ≤ qE) := ‹Fact (1 ≤ ENNReal.ofReal qR)›
  have hqfinite : qE ≠ ⊤ := by dsimp [qE]; exact ENNReal.ofReal_ne_top
  obtain ⟨Mχ, Mχt, hMχ, hMχt, hχbound, hχtbound⟩ :=
    exists_resolventTimeCutoff_bounds
  let κA : ℝ → ℝ := fun t => resolventTimeCutoff t * Real.exp (-t)
  have hκc : Continuous κA := by
    dsimp [κA]
    exact continuous_resolventTimeCutoff.mul (Real.continuous_exp.comp continuous_neg)
  have hMA : 0 ≤ Mχ * Real.exp (1 / 2) := by positivity
  have hκbound : ∀ t, ‖(κA t : ℂ)‖ ≤ Mχ * Real.exp (1 / 2) := by
    intro t
    by_cases ht : t ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)
    · dsimp only [κA]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hexp : Real.exp (-t) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.mpr (by linarith [ht.1])
      have hχ : |resolventTimeCutoff t| ≤ Mχ := by
        simpa [Real.norm_eq_abs] using hχbound t
      exact mul_le_mul hχ hexp (Real.exp_pos _).le hMχ
    · have hz := resolventTimeCutoff_zero_outside_unitStrip ht
      simpa [κA, hz] using hMA
  have hχzero : ∀ t, t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) →
      resolventTimeCutoff t = 0 := fun t ht => resolventTimeCutoff_zero_outside_unitStrip ht
  have hχtzero : ∀ t, t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) →
      resolventTimeCutoffDeriv t = 0 :=
    fun t ht => resolventTimeCutoffDeriv_zero_outside_unitStrip ht
  have hκzero : ∀ t, t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) → κA t = 0 := by
    intro t ht
    simp [κA, hχzero t ht]
  let Cν : ℝ :=
    (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / qE.toReal)
  let Cw : ℝ≥0∞ := ENNReal.ofReal (‖dotL e‖ * Cν * ‖w‖)
  let Ca : ℝ≥0∞ := ENNReal.ofReal (‖dotL e‖ * Cν * ‖a‖)
  let Cb : ℝ≥0∞ := ENNReal.ofReal (‖dotL e‖ * Cν * ‖b‖)
  have hCw : 0 ≤ ‖dotL e‖ * Cν * ‖w‖ := by positivity
  have hCa : 0 ≤ ‖dotL e‖ * Cν * ‖a‖ := by positivity
  have hCb : 0 ≤ ‖dotL e‖ * Cν * ‖b‖ := by positivity
  let C : ℝ≥0∞ := ENNReal.ofReal Mχt * Cw + ENNReal.ofReal Mχ * Cb +
    ENNReal.ofReal (Mχ * Real.exp (1 / 2)) * Ca + ENNReal.ofReal Mχ * Cw
  have hCtop : C < ⊤ := by
    dsimp [C, Cw, Ca, Cb]
    apply ENNReal.add_lt_top.mpr
    constructor
    · apply ENNReal.add_lt_top.mpr
      constructor
      · apply ENNReal.add_lt_top.mpr
        constructor
        · exact ENNReal.mul_lt_top
            (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
            (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
        · exact ENNReal.mul_lt_top
            (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
            (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
      · exact ENNReal.mul_lt_top
          (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
          (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
    · exact ENNReal.mul_lt_top
        (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
        (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  refine ⟨C, hCtop, ?_⟩
  intro τ₀
  let U : ℝ × Space → ℂ := fun p => dotL e (chartJ w ν τ₀ p)
  let B : ℝ × Space → ℂ := fun p => dotL e (chartJ b ν τ₀ p)
  let A : ℝ × Space → ℂ := fun p => dotL e (chartJ a ν τ₀ p)
  let G1 : ℝ × Space → ℂ := fun p => (resolventTimeCutoffDeriv p.1 : ℂ) * U p
  let G2 : ℝ × Space → ℂ := fun p => (resolventTimeCutoff p.1 : ℂ) * B p
  let G3 : ℝ × Space → ℂ := fun p => (κA p.1 : ℂ) * A p
  let G4 : ℝ × Space → ℂ := fun p => (resolventTimeCutoff p.1 : ℂ) * U p
  have hUsm : StronglyMeasurable U := by
    simpa [U] using (dotL e).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_chartJ w ν τ₀)
  have hBsm : StronglyMeasurable B := by
    simpa [B] using (dotL e).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_chartJ b ν τ₀)
  have hAsm : StronglyMeasurable A := by
    simpa [A] using (dotL e).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_chartJ a ν τ₀)
  have hχsm : StronglyMeasurable (fun p : ℝ × Space =>
      (resolventTimeCutoff p.1 : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (continuous_resolventTimeCutoff.comp continuous_fst)).stronglyMeasurable
  have hχtsm : StronglyMeasurable (fun p : ℝ × Space =>
      (resolventTimeCutoffDeriv p.1 : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (continuous_resolventTimeCutoffDeriv.comp continuous_fst)).stronglyMeasurable
  have hκsm : StronglyMeasurable (fun p : ℝ × Space => (κA p.1 : ℂ)) :=
    (Complex.continuous_ofReal.comp (hκc.comp continuous_fst)).stronglyMeasurable
  have hG1sm : StronglyMeasurable G1 := by
    change StronglyMeasurable ((fun p : ℝ × Space =>
      (resolventTimeCutoffDeriv p.1 : ℂ)) * U)
    exact hχtsm.mul hUsm
  have hG2sm : StronglyMeasurable G2 := by
    change StronglyMeasurable ((fun p : ℝ × Space =>
      (resolventTimeCutoff p.1 : ℂ)) * B)
    exact hχsm.mul hBsm
  have hG3sm : StronglyMeasurable G3 := by
    change StronglyMeasurable ((fun p : ℝ × Space => (κA p.1 : ℂ)) * A)
    exact hκsm.mul hAsm
  have hG4sm : StronglyMeasurable G4 := by
    change StronglyMeasurable ((fun p : ℝ × Space =>
      (resolventTimeCutoff p.1 : ℂ)) * U)
    exact hχsm.mul hUsm
  have hUw : eLpNorm U qE (volume.restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))) ≤ Cw := by
    simpa [U, Cw, Cν] using
      (eLpNorm_dotL_chartJ_unitStrip_le hP1 hqfinite hν w τ₀ e)
  have hBa : eLpNorm B qE (volume.restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))) ≤ Cb := by
    simpa [B, Cb, Cν] using
      (eLpNorm_dotL_chartJ_unitStrip_le hP1 hqfinite hν b τ₀ e)
  have hAa : eLpNorm A qE (volume.restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))) ≤ Ca := by
    simpa [A, Ca, Cν] using
      (eLpNorm_dotL_chartJ_unitStrip_le hP1 hqfinite hν a τ₀ e)
  have hG1 : eLpNorm G1 qE volume ≤ ENNReal.ofReal Mχt * Cw := by
    simpa [G1, U] using (eLpNorm_timeMul_unitStrip_le hχtbound hχtzero).trans
      (by gcongr)
  have hG2 : eLpNorm G2 qE volume ≤ ENNReal.ofReal Mχ * Cb := by
    simpa [G2, B] using (eLpNorm_timeMul_unitStrip_le hχbound hχzero).trans
      (by gcongr)
  have hG3 : eLpNorm G3 qE volume ≤ ENNReal.ofReal (Mχ * Real.exp (1 / 2)) * Ca := by
    simpa [G3, A, κA] using (eLpNorm_timeMul_unitStrip_le hκbound hκzero).trans
      (by gcongr <;> norm_num)
  have hG4 : eLpNorm G4 qE volume ≤ ENNReal.ofReal Mχ * Cw := by
    simpa [G4, U] using (eLpNorm_timeMul_unitStrip_le hχbound hχzero).trans
      (by gcongr)
  let Fprod : ℝ × Space → ℂ := G1 + G2 - G3 + G4
  have hFprodSM : StronglyMeasurable Fprod := by
    exact ((hG1sm.add hG2sm).sub hG3sm).add hG4sm
  have htriangle : eLpNorm Fprod qE volume ≤
      eLpNorm G1 qE volume + eLpNorm G2 qE volume +
        eLpNorm G3 qE volume + eLpNorm G4 qE volume := by
    dsimp [Fprod]
    calc
      eLpNorm ((G1 + G2 - G3) + G4) qE volume ≤
          eLpNorm (G1 + G2 - G3) qE volume + eLpNorm G4 qE volume :=
        eLpNorm_add_le ((hG1sm.add hG2sm).sub hG3sm).aestronglyMeasurable
          hG4sm.aestronglyMeasurable (Fact.out : 1 ≤ qE)
      _ ≤ eLpNorm (G1 + G2) qE volume + eLpNorm G3 qE volume +
          eLpNorm G4 qE volume := by
        gcongr
        exact eLpNorm_sub_le (hG1sm.add hG2sm).aestronglyMeasurable
          hG3sm.aestronglyMeasurable (Fact.out : 1 ≤ qE)
      _ ≤ eLpNorm G1 qE volume + eLpNorm G2 qE volume + eLpNorm G3 qE volume +
          eLpNorm G4 qE volume := by
        gcongr
        exact eLpNorm_add_le hG1sm.aestronglyMeasurable hG2sm.aestronglyMeasurable
          (Fact.out : 1 ≤ qE)
  have hFprodBound : eLpNorm Fprod qE volume ≤ C := by
    dsimp [C]
    exact htriangle.trans (add_le_add (add_le_add (add_le_add hG1 hG2) hG3) hG4)
  have hFSTeq : chartJCutoffFST ν τ₀ e w b a =
      fun X : ST => Fprod (productToST.symm X) := by
    funext X
    simp [Fprod, G1, G2, G3, G4, U, B, A, κA, chartJCutoffFST, mul_assoc]
  have hnorm := eLpNorm_comp_measurePreserving (g := Fprod) (p := qE)
    hFprodSM.aestronglyMeasurable B0448.measurePreserving_ofLp
  have heq : chartJCutoffFST ν τ₀ e w b a =ᵐ[volume]
      Fprod ∘ (MeasurableEquiv.toLp 2 (ℝ × Space)).symm := by
    filter_upwards [] with X
    rw [hFSTeq]
    simp [productToST]
  calc
    eLpNorm (chartJCutoffFST ν τ₀ e w b a) qE volume =
        eLpNorm (Fprod ∘ (MeasurableEquiv.toLp 2 (ℝ × Space)).symm) qE volume :=
      eLpNorm_congr_ae heq
    _ = eLpNorm Fprod qE volume := hnorm
    _ ≤ C := hFprodBound

/-- The actual fixed-cutoff graph pair has Lq representatives and therefore a continuous bounded
representative. The period restriction is the small-period regime already available to the final
construction; the graph hypotheses remain the actual time and Laplacian graph properties. -/
theorem chartJ_cutoff_ST_continuous_rep {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1)
    {qR qR' : ℝ} (hqq' : qR.HolderConjugate qR') (hq : 5 / 2 < qR)
    {ν : ℝ} (hν : 0 < ν)
    [Fact (1 ≤ ENNReal.ofReal qR)] {w a b : Yq P (ENNReal.ofReal qR)}
    (hTime : HasPhaseOp driftT w b)
    (hLap : HasPhaseOp (nuLapT ν) w a) (τ₀ : ℝ) (e : CVec3) :
    ∃ H F : Lp ℂ (ENNReal.ofReal qR) (volume : Measure ST),
      H =ᵐ[volume] chartJCutoffHST ν τ₀ e w ∧
      F =ᵐ[volume] chartJCutoffFST ν τ₀ e w b a ∧
      (∀ φ : 𝓢(ST, ℂ), HasCompactSupport φ →
        ∫ X : ST, resolventOpT φ X * H X = ∫ X, φ X * F X) ∧
      (∃ Hc : ST → ℂ, Continuous Hc ∧ chartJCutoffHST ν τ₀ e w =ᵐ[volume] Hc ∧
        ∀ X, ‖Hc X‖ ≤ (eLpNorm stKernel (ENNReal.ofReal qR') volume).toReal *
          (eLpNorm (chartJCutoffFST ν τ₀ e w b a) (ENNReal.ofReal qR) volume).toReal) ∧
      (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ τ : ℝ,
        eLpNorm (chartJCutoffFST ν τ e w b a) (ENNReal.ofReal qR) volume ≤ C) := by
  let qE : ℝ≥0∞ := ENNReal.ofReal qR
  haveI : Fact (1 ≤ qE) := ‹Fact (1 ≤ ENNReal.ofReal qR)›
  have hqfinite : qE ≠ ⊤ := by
    dsimp [qE]
    exact ENNReal.ofReal_ne_top
  have hbounds := exists_resolventTimeCutoff_bounds
  obtain ⟨Mχ, Mχt, hMχ, hMχt, hχbound, hχtbound⟩ := hbounds
  let U : ℝ × Space → ℂ := fun p => dotL e (chartJ w ν τ₀ p)
  let B : ℝ × Space → ℂ := fun p => dotL e (chartJ b ν τ₀ p)
  let A : ℝ × Space → ℂ := fun p => dotL e (chartJ a ν τ₀ p)
  let κA : ℝ → ℝ := fun t => resolventTimeCutoff t * Real.exp (-t)
  have hU : MemLp U qE (volume.restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))) := by
    simpa [U] using memLp_dotL_chartJ_unitStrip hν hP1 hqfinite w τ₀ e
  have hB : MemLp B qE (volume.restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))) := by
    simpa [B] using memLp_dotL_chartJ_unitStrip hν hP1 hqfinite b τ₀ e
  have hA : MemLp A qE (volume.restrict
      (Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ (Set.univ : Set Space))) := by
    simpa [A] using memLp_dotL_chartJ_unitStrip hν hP1 hqfinite a τ₀ e
  have hκc : Continuous κA := by
    dsimp [κA]
    exact continuous_resolventTimeCutoff.mul
      (Real.continuous_exp.comp (continuous_neg))
  have hMA : 0 ≤ Mχ * Real.exp (1 / 2) := by positivity
  have hκbound : ∀ t, ‖(κA t : ℂ)‖ ≤ Mχ * Real.exp (1 / 2) := by
    intro t
    by_cases ht : t ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)
    · dsimp only [κA]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hexp : Real.exp (-t) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.mpr (by linarith [ht.1])
      have hχ : |resolventTimeCutoff t| ≤ Mχ := by
        simpa [Real.norm_eq_abs] using hχbound t
      exact mul_le_mul hχ hexp (Real.exp_pos _).le hMχ
    · have hz := resolventTimeCutoff_zero_outside_unitStrip ht
      simpa [κA, hz] using hMA
  have hχzero : ∀ t, t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) →
      resolventTimeCutoff t = 0 := by
    intro t ht
    exact resolventTimeCutoff_zero_outside_unitStrip ht
  have hχtzero : ∀ t, t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) →
      resolventTimeCutoffDeriv t = 0 := by
    intro t ht
    exact resolventTimeCutoffDeriv_zero_outside_unitStrip ht
  have hpair := memLp_cutoff_resolvent_pair hU hB hA
    continuous_resolventTimeCutoff continuous_resolventTimeCutoffDeriv hκc
    hMχ hMχt hMA hχbound hχtbound hκbound hχzero hχtzero
    (by
      intro t ht
      simp [κA, hχzero t ht])
  let Hprod : ℝ × Space → ℂ := fun p =>
    (resolventTimeCutoff p.1 : ℂ) * U p
  let Fprod : ℝ × Space → ℂ := fun p =>
    (resolventTimeCutoffDeriv p.1 : ℂ) * U p +
      (resolventTimeCutoff p.1 : ℂ) * B p -
      (κA p.1 : ℂ) * A p + (resolventTimeCutoff p.1 : ℂ) * U p
  have hHprod : MemLp Hprod qE volume := by
    simpa [Hprod, U] using hpair.1
  have hFprod : MemLp Fprod qE volume := by
    simpa [Fprod, U, B, A, κA, mul_assoc] using hpair.2
  have hUsm : StronglyMeasurable U := by
    simpa [U] using
      (dotL e).continuous.comp_stronglyMeasurable (stronglyMeasurable_chartJ w ν τ₀)
  have hBsm : StronglyMeasurable B := by
    simpa [B] using
      (dotL e).continuous.comp_stronglyMeasurable (stronglyMeasurable_chartJ b ν τ₀)
  have hAsm : StronglyMeasurable A := by
    simpa [A] using
      (dotL e).continuous.comp_stronglyMeasurable (stronglyMeasurable_chartJ a ν τ₀)
  have hχsm : StronglyMeasurable (fun p : ℝ × Space =>
      (resolventTimeCutoff p.1 : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (continuous_resolventTimeCutoff.comp continuous_fst)).stronglyMeasurable
  have hχtsm : StronglyMeasurable (fun p : ℝ × Space =>
      (resolventTimeCutoffDeriv p.1 : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (continuous_resolventTimeCutoffDeriv.comp continuous_fst)).stronglyMeasurable
  have hκsm : StronglyMeasurable (fun p : ℝ × Space => (κA p.1 : ℂ)) :=
    (Complex.continuous_ofReal.comp (hκc.comp continuous_fst)).stronglyMeasurable
  have hHprodsm : StronglyMeasurable Hprod := by
    exact hχsm.mul hUsm
  have hFprodsm : StronglyMeasurable Fprod := by
    exact (((hχtsm.mul hUsm).add (hχsm.mul hBsm)).sub (hκsm.mul hAsm)).add
      (hχsm.mul hUsm)
  have hHST : MemLp (chartJCutoffHST ν τ₀ e w) qE volume := by
    have hsm : AEStronglyMeasurable (chartJCutoffHST ν τ₀ e w) volume := by
      change AEStronglyMeasurable (Hprod ∘ productToST.symm) volume
      exact hHprodsm.comp_measurable productToST.symm.continuous.measurable |>.aestronglyMeasurable
    have hnorm := eLpNorm_comp_measurePreserving (g := Hprod) (p := qE)
      hHprodsm.aestronglyMeasurable B0448.measurePreserving_ofLp
    have heq : chartJCutoffHST ν τ₀ e w =ᵐ[volume]
        Hprod ∘ (MeasurableEquiv.toLp 2 (ℝ × Space)).symm := by
      filter_upwards [] with X
      rfl
    refine ⟨hsm, ?_⟩
    rw [eLpNorm_congr_ae heq, hnorm]
    exact hHprod.2
  have hFST : MemLp (chartJCutoffFST ν τ₀ e w b a) qE volume := by
    have hFSTeq : chartJCutoffFST ν τ₀ e w b a =
        fun X : ST => Fprod (productToST.symm X) := by
      funext X
      simp [Fprod, U, B, A, κA, chartJCutoffFST, mul_assoc]
    have hsm : AEStronglyMeasurable (chartJCutoffFST ν τ₀ e w b a) volume := by
      rw [hFSTeq]
      exact hFprodsm.comp_measurable productToST.symm.continuous.measurable |>.aestronglyMeasurable
    have hnorm := eLpNorm_comp_measurePreserving (g := Fprod) (p := qE)
      hFprodsm.aestronglyMeasurable B0448.measurePreserving_ofLp
    have heq : chartJCutoffFST ν τ₀ e w b a =ᵐ[volume]
        Fprod ∘ (MeasurableEquiv.toLp 2 (ℝ × Space)).symm := by
      filter_upwards [] with X
      rw [hFSTeq]
      simp [productToST]
    refine ⟨hsm, ?_⟩
    rw [eLpNorm_congr_ae heq, hnorm]
    exact hFprod.2
  let H : Lp ℂ qE (volume : Measure ST) := hHST.toLp (chartJCutoffHST ν τ₀ e w)
  let F : Lp ℂ qE (volume : Measure ST) := hFST.toLp (chartJCutoffFST ν τ₀ e w b a)
  have hHae : (H : ST → ℂ) =ᵐ[volume] chartJCutoffHST ν τ₀ e w :=
    hHST.coeFn_toLp
  have hFae : (F : ST → ℂ) =ᵐ[volume] chartJCutoffFST ν τ₀ e w b a :=
    hFST.coeFn_toLp
  have hHF : ∀ φ : 𝓢(ST, ℂ), HasCompactSupport φ →
      ∫ X : ST, resolventOpT φ X * H X = ∫ X, φ X * F X := by
    intro φ hφc
    have hraw := chartJ_cutoff_ST_resolvent hν hqfinite
      (by simpa [qE] using (show 1 < qR by linarith)) hTime hLap τ₀ e hφc
    calc
      ∫ X : ST, resolventOpT φ X * H X =
          ∫ X : ST, resolventOpT φ X * chartJCutoffHST ν τ₀ e w X := by
            apply integral_congr_ae
            filter_upwards [hHae] with X hX
            rw [hX]
      _ = ∫ X : ST, φ X * chartJCutoffFST ν τ₀ e w b a X := hraw
      _ = ∫ X : ST, φ X * F X := by
            apply integral_congr_ae
            filter_upwards [hFae] with X hX
            rw [hX]
  have hHeat := Heat.strip_sup_le hqq' hq hHF
  rcases hHeat with ⟨hKernel, Hc, hHc, hHaeC, hbound⟩
  have hboundF : ∀ X, ‖Hc X‖ ≤
      (eLpNorm stKernel (ENNReal.ofReal qR') volume).toReal *
        (eLpNorm (chartJCutoffFST ν τ₀ e w b a) (ENNReal.ofReal qR) volume).toReal := by
    intro X
    have hnorm : eLpNorm F (ENNReal.ofReal qR) volume =
        eLpNorm (chartJCutoffFST ν τ₀ e w b a) (ENNReal.ofReal qR) volume :=
      eLpNorm_congr_ae hFae
    rw [hnorm] at hbound
    exact hbound X
  have huniform := chartJ_cutoff_FST_uniform_eLpNorm hP1 hq hν
    (w := w) (a := a) (b := b) e
  exact ⟨H, F, hHae, hFae, hHF, ⟨Hc, hHc, hHae.symm.trans hHaeC, hboundF⟩,
    huniform⟩

end UnforcedLeray.B0449

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0448

/-- A single observation-time resolvent gives a continuous representative of its chart field on
the open interval where the fixed cutoff equals one. -/
theorem chartJ_cutoff_local_continuous_rep {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1)
    {qR qR' : ℝ} (hqq' : qR.HolderConjugate qR') (hq : 5 / 2 < qR)
    {ν : ℝ} (hν : 0 < ν)
    [Fact (1 ≤ ENNReal.ofReal qR)] {w a b : Yq P (ENNReal.ofReal qR)}
    (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)
    (τ₀ : ℝ) (e : CVec3) :
    ∃ f : ℝ × Space → ℂ, Continuous f ∧
      f =ᵐ[volume.restrict
        (Ioo (-(1 / 8 : ℝ)) (1 / 8) ×ˢ (Set.univ : Set Space))]
        (fun p => dotL e (chartJ w ν τ₀ p)) := by
  obtain ⟨H, F, hHae, hFae, hHF, ⟨Hc, hHc, hHcraw, hHbound⟩, hUniform⟩ :=
    chartJ_cutoff_ST_continuous_rep hP1 hqq' hq hν hTime hLap τ₀ e
  let f : ℝ × Space → ℂ := fun p => Hc (productToST p)
  have hf : Continuous f := hHc.comp productToST.continuous
  have hpull : (fun p : ℝ × Space => Hc (productToST p)) =ᵐ[volume]
      fun p => chartJCutoffHST ν τ₀ e w (productToST p) :=
    (B0448.measurePreserving_ofLp.symm).quasiMeasurePreserving.ae_eq_comp hHcraw.symm
  have hS : MeasurableSet
      (Ioo (-(1 / 8 : ℝ)) (1 / 8) ×ˢ (Set.univ : Set Space)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  refine ⟨f, hf, ?_⟩
  rw [Filter.EventuallyEq, ae_restrict_iff' hS]
  filter_upwards [hpull] with p hp hpS
  have ht : |p.1| ≤ 1 / 8 := by
    rw [abs_le]
    constructor <;> linarith [hpS.1.1, hpS.1.2]
  have hχ : resolventTimeCutoff p.1 = 1 := resolventTimeCutoff_eq_one ht
  simpa [f, chartJCutoffHST, hχ, productToST] using hp

end UnforcedLeray.B0449
