import UnforcedLeray.Short.PartIIa.Sub.F11
import UnforcedLeray.Units.B0449.GraphResolventBounded

/-!
# Part II-a, task `PartII-a:F11`: the supremum embedding `graphSupEmbedding`

Source of record: `the November 2 reference manuscript`, lines 1524-1531
(`bg:supremum-embedding`).

The assembly (continuity, periodicity, phase trace identification, descent to the circle, pointwise
bound) is `graphSupEmbedding_of` in `Short/PartII-a/Sub/F11.lean`, conditional on the explicit
cutoff-source bound `ChartCutoffExplicit`. This file proves that bound: the proof of
`chartJ_cutoff_FST_uniform_eLpNorm` (Units/B0449/GraphResolventBounded.lean) already bounds the
`L^q` norm of the cutoff source by an explicit combination of `‖dotL e‖`, the unit-strip constant
`(2 e^{3/4} ν^{-3/2})^{1/q}` and the norms of `w`, `𝒯w`, `νΔw`; we repeat it with the time-cutoff
constants as hypotheses (`fstCutoff_eLpNorm_le_aux`) and simplify the constant
(`(c₀ ν^{-3/2})^{1/q} = c₀^{1/q} ν^{-3/(2q)}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal SchwartzMap

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0448 UnforcedLeray.Heat
  UnforcedLeray.B0449 UnforcedLeray.B0411

/-- **Explicit form of `chartJ_cutoff_FST_uniform_eLpNorm`**: the cutoff source `F` has `L^q`
norm at most the displayed finite combination of the norms of `w`, `b = 𝒯w`, `a = νΔw` (copy of
the proof of `chartJ_cutoff_FST_uniform_eLpNorm`, Units/B0449/GraphResolventBounded.lean lines
107-280, with the time-cutoff constants `Mχ`, `Mχt` taken as hypotheses and the final bound
`C` kept explicit). -/
theorem fstCutoff_eLpNorm_le_aux {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1)
    {qR : ℝ} (hqR : 5 / 2 < qR) [Fact (1 ≤ ENNReal.ofReal qR)]
    {ν : ℝ} (hν : 0 < ν) {w a b : Yq P (ENNReal.ofReal qR)} (e : CVec3)
    {Mχ Mχt : ℝ} (hMχ : 0 ≤ Mχ) (hMχt : 0 ≤ Mχt)
    (hχbound : ∀ t, ‖(resolventTimeCutoff t : ℂ)‖ ≤ Mχ)
    (hχtbound : ∀ t, ‖(resolventTimeCutoffDeriv t : ℂ)‖ ≤ Mχt) (τ₀ : ℝ) :
    eLpNorm (chartJCutoffFST ν τ₀ e w b a) (ENNReal.ofReal qR) volume ≤
      ENNReal.ofReal Mχt * ENNReal.ofReal (‖dotL e‖ *
          (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / (ENNReal.ofReal qR).toReal) * ‖w‖) +
        ENNReal.ofReal Mχ * ENNReal.ofReal (‖dotL e‖ *
          (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / (ENNReal.ofReal qR).toReal) * ‖b‖) +
        ENNReal.ofReal (Mχ * Real.exp (1 / 2)) * ENNReal.ofReal (‖dotL e‖ *
          (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / (ENNReal.ofReal qR).toReal) * ‖a‖) +
        ENNReal.ofReal Mχ * ENNReal.ofReal (‖dotL e‖ *
          (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / (ENNReal.ofReal qR).toReal) * ‖w‖) := by
  let qE : ℝ≥0∞ := ENNReal.ofReal qR
  haveI : Fact (1 ≤ qE) := ‹Fact (1 ≤ ENNReal.ofReal qR)›
  have hqfinite : qE ≠ ⊤ := by dsimp [qE]; exact ENNReal.ofReal_ne_top
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

/-- **The explicit cutoff-source bound** (`ChartCutoffExplicit`). -/
theorem chartCutoffExplicit : ChartCutoffExplicit := by
  intro qR hqR _
  obtain ⟨Mχ, Mχt, hMχ, hMχt, hχbound, hχtbound⟩ := exists_resolventTimeCutoff_bounds
  have hqpos : 0 < qR := by linarith
  have hc0 : 0 < 2 * Real.exp (3 / 4) := by positivity
  refine ⟨(2 * Real.exp (3 / 4)) ^ (1 / qR) * (Mχt + 2 * Mχ + Mχ * Real.exp (1 / 2)),
    by positivity, ?_⟩
  intro P _ hP1 ν hν w a b e τ₀
  refine (fstCutoff_eLpNorm_le_aux hP1 hqR hν (w := w) (a := a) (b := b) e hMχ hMχt hχbound
    hχtbound τ₀).trans ?_
  have hCν : (2 * Real.exp (3 / 4) * ν ^ (-(3 / 2 : ℝ))) ^ (1 / (ENNReal.ofReal qR).toReal) =
      (2 * Real.exp (3 / 4)) ^ (1 / qR) * ν ^ (-(3 / (2 * qR))) := by
    rw [ENNReal.toReal_ofReal hqpos.le, Real.mul_rpow hc0.le (Real.rpow_nonneg hν.le _),
      ← Real.rpow_mul hν.le]
    congr 2
    field_simp
  rw [hCν]
  have hν0 : 0 ≤ ν ^ (-(3 / (2 * qR))) := Real.rpow_nonneg hν.le _
  have hF : 0 ≤ ‖dotL e‖ * ((2 * Real.exp (3 / 4)) ^ (1 / qR) * ν ^ (-(3 / (2 * qR)))) := by
    positivity
  have hX : ∀ n : ℝ, 0 ≤ n → 0 ≤ ‖dotL e‖ * ((2 * Real.exp (3 / 4)) ^ (1 / qR) *
      ν ^ (-(3 / (2 * qR)))) * n := fun n hn => mul_nonneg hF hn
  rw [← ENNReal.ofReal_mul hMχt, ← ENNReal.ofReal_mul hMχ,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ Mχ * Real.exp (1 / 2)), ← ENNReal.ofReal_mul hMχ,
    ← ENNReal.ofReal_add (mul_nonneg hMχt (hX _ (norm_nonneg w)))
      (mul_nonneg hMχ (hX _ (norm_nonneg b))),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hMχt (hX _ (norm_nonneg w)))
      (mul_nonneg hMχ (hX _ (norm_nonneg b))))
      (mul_nonneg (by positivity : 0 ≤ Mχ * Real.exp (1 / 2)) (hX _ (norm_nonneg a))),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (mul_nonneg hMχt (hX _ (norm_nonneg w)))
      (mul_nonneg hMχ (hX _ (norm_nonneg b))))
      (mul_nonneg (by positivity : 0 ≤ Mχ * Real.exp (1 / 2)) (hX _ (norm_nonneg a))))
      (mul_nonneg hMχ (hX _ (norm_nonneg w)))]
  apply ENNReal.ofReal_le_ofReal
  have he : 0 ≤ Real.exp (1 / 2) := (Real.exp_pos _).le
  set F := ‖dotL e‖ * ((2 * Real.exp (3 / 4)) ^ (1 / qR) * ν ^ (-(3 / (2 * qR)))) with hFdef
  have hw := norm_nonneg w
  have hb := norm_nonneg b
  have ha := norm_nonneg a
  have hEq : (2 * Real.exp (3 / 4)) ^ (1 / qR) * (Mχt + 2 * Mχ + Mχ * Real.exp (1 / 2)) *
      ‖dotL e‖ * ν ^ (-(3 / (2 * qR))) * (‖w‖ + ‖b‖ + ‖a‖) =
      F * ((Mχt + 2 * Mχ + Mχ * Real.exp (1 / 2)) * (‖w‖ + ‖b‖ + ‖a‖)) := by
    rw [hFdef]; ring
  rw [hEq]
  have hK : 0 ≤ Mχt + 2 * Mχ + Mχ * Real.exp (1 / 2) := by positivity
  have key : Mχt * (F * ‖w‖) + Mχ * (F * ‖b‖) + Mχ * Real.exp (1 / 2) * (F * ‖a‖) +
      Mχ * (F * ‖w‖) ≤ F * ((Mχt + 2 * Mχ + Mχ * Real.exp (1 / 2)) * (‖w‖ + ‖b‖ + ‖a‖)) := by
    have e1 : 0 ≤ F * ‖w‖ := mul_nonneg hF hw
    have e2 : 0 ≤ F * ‖b‖ := mul_nonneg hF hb
    have e3 : 0 ≤ F * ‖a‖ := mul_nonneg hF ha
    nlinarith [mul_nonneg hMχ e1, mul_nonneg hMχ e2, mul_nonneg hMχ e3, mul_nonneg hMχt e1,
      mul_nonneg hMχt e2, mul_nonneg hMχt e3, mul_nonneg (mul_nonneg hMχ he) e1,
      mul_nonneg (mul_nonneg hMχ he) e2, mul_nonneg (mul_nonneg hMχ he) e3]
  linarith [key]

/-- **Supremum embedding** (`bg:supremum-embedding`, source lines 1524-1531). -/
theorem graphSupEmbedding : GraphSupEmbedding := graphSupEmbedding_of chartCutoffExplicit

end UnforcedLeray.Short.PartIIa
