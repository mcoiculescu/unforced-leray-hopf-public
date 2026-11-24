import UnforcedLeray.Short.PartI.Sub.T07
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.CellBridge
import UnforcedLeray.Units.B0151.DivCurl

/-!
# Part I, task `PartI:T07`, target `cylGradInterpL2_proof`: gradient interpolation on the cylinder

Source of record: `the November 2 reference manuscript`, lines 366-374 (the cylinder
interpolation inequality; its gradient part is `‖Df‖₂² ≤ 4 ‖f‖₂ ‖D²f‖₂`).

Proof. Write `∂_q = GaussianVortex.partialX`, `∂_η = GaussianVortex.partialY`.
* Pointwise, `|∂_q f z|, |∂_η f z| ≤ ‖D f z‖ ≤ |∂_q f z| + |∂_η f z|` and
  `|∂_q² f z|, |∂_η² f z| ≤ ‖D² f z‖`, from `cylJetWord_proof` (`CylJetWord`) at `l = 1, 2`.
* `B0151.interpolation_q` and `B0151.interpolation_η` (constant `1`, on the library cell
  `B0151.cellMeasure c`) give `‖∂_v f‖₂² ≤ ‖f‖₂ ‖∂_v² f‖₂` for `v = q, η`. The transfer
  `eLpNorm_cellMeasure_eq` moves every norm to the centred cell `Cyl.cellμ c`.
* Minkowski gives `‖Df‖₂ ≤ ‖∂_q f‖₂ + ‖∂_η f‖₂`; with `(a + b)² ≤ 2 (a² + b²)` this gives
  `‖Df‖₂² ≤ 2 (F Q + F E) ≤ 4 F D₂`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.GaussianVortex (partialX partialY)

/-- The words of length one are exactly `[true]` and `[false]`. -/
theorem gradInterp_wordsOfLength_one : wordsOfLength 1 = {[true], [false]} := by
  ext w
  simp only [wordsOfLength, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    have h0 : List.ofFn r = [r 0] := by
      simp [List.ofFn_succ]
    rw [h0]
    cases hr : r 0 <;> simp
  · rintro (rfl | rfl)
    · exact ⟨fun _ => true, by simp⟩
    · exact ⟨fun _ => false, by simp⟩

/-- Sum over the words of length one. -/
theorem gradInterp_sum_wordsOfLength_one (g : List Bool → ℝ) :
    ∑ w ∈ wordsOfLength 1, g w = g [true] + g [false] := by
  rw [gradInterp_wordsOfLength_one,
    Finset.sum_insert (show [true] ∉ ({[false]} : Finset (List Bool)) by simp),
    Finset.sum_singleton]

/-- The elementary inequality `(a + b)² ≤ 2 (a² + b²)` in `ℝ≥0∞` (the `ℝ≥0` case is AM-GM). -/
theorem gradInterp_enn_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  have key : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    calc (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
      _ ≤ a ^ 2 + (a ^ 2 + b ^ 2) + b ^ 2 := by
        gcongr
        exact two_mul_le_add_sq a b
      _ = 2 * (a ^ 2 + b ^ 2) := by ring
  exact_mod_cast key

/-- **Target** `cylGradInterpL2_proof` (source lines 366-374): gradient interpolation on the
cylinder, `‖Df‖₂² ≤ 4 ‖f‖₂ ‖D²f‖₂` (`CylGradInterpL2`, `Sub/T07.lean`). -/
theorem cylGradInterpL2_proof : UnforcedLeray.Short.PartI.CylGradInterpL2 := by
  intro c hc f hf hper hf0 hj1 hj2
  -- Pointwise word bounds from the jet-word lemma.
  have hJ1X : ∀ z, ‖partialX f z‖ ≤ ‖Train.jet 1 f z‖ := by
    intro z
    have h := (cylJetWord_proof f hf 1 z).1 [true] rfl
    rw [Real.norm_eq_abs]
    exact h
  have hJ1Y : ∀ z, ‖partialY f z‖ ≤ ‖Train.jet 1 f z‖ := by
    intro z
    have h := (cylJetWord_proof f hf 1 z).1 [false] rfl
    rw [Real.norm_eq_abs]
    exact h
  have hJ2X : ∀ z, ‖partialX (partialX f) z‖ ≤ ‖Train.jet 2 f z‖ := by
    intro z
    have h := (cylJetWord_proof f hf 2 z).1 [true, true] rfl
    rw [Real.norm_eq_abs]
    exact h
  have hJ2Y : ∀ z, ‖partialY (partialY f) z‖ ≤ ‖Train.jet 2 f z‖ := by
    intro z
    have h := (cylJetWord_proof f hf 2 z).1 [false, false] rfl
    rw [Real.norm_eq_abs]
    exact h
  have hU1 : ∀ z, ‖Train.jet 1 f z‖ ≤ ‖partialX f z‖ + ‖partialY f z‖ := by
    intro z
    have h := (cylJetWord_proof f hf 1 z).2
    rw [gradInterp_sum_wordsOfLength_one] at h
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact h
  -- Smoothness, continuity, measurability and periodicity.
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have hfc : Continuous f := hf.continuous
  have hPX : ContDiff ℝ ∞ (partialX f) := UnforcedLeray.B0151.contDiff_partialX_infty hf
  have hPY : ContDiff ℝ ∞ (partialY f) := UnforcedLeray.B0151.contDiff_partialY_infty hf
  have hPXX : ContDiff ℝ ∞ (partialX (partialX f)) :=
    UnforcedLeray.B0151.contDiff_partialX_infty hPX
  have hPYY : ContDiff ℝ ∞ (partialY (partialY f)) :=
    UnforcedLeray.B0151.contDiff_partialY_infty hPY
  have hq : UnforcedLeray.B0151.IsPeriodicQ c f := fun q η => hper (q, η)
  have hqX := hq.partialX
  have hqY := hq.partialY
  have hqXX := hqX.partialX
  have hqYY := hqY.partialY
  have perX : Cyl.IsPeriodic c (partialX f) := fun z => hqX z.1 z.2
  have perY : Cyl.IsPeriodic c (partialY f) := fun z => hqY z.1 z.2
  have perXX : Cyl.IsPeriodic c (partialX (partialX f)) := fun z => hqXX z.1 z.2
  have perYY : Cyl.IsPeriodic c (partialY (partialY f)) := fun z => hqYY z.1 z.2
  have mf : Measurable f := hfc.measurable
  have mX : Measurable (partialX f) := hPX.continuous.measurable
  have mY : Measurable (partialY f) := hPY.continuous.measurable
  have mXX : Measurable (partialX (partialX f)) := hPXX.continuous.measurable
  have mYY : Measurable (partialY (partialY f)) := hPYY.continuous.measurable
  -- `L²` membership on the centred cell, from the jet hypotheses.
  have hX : MemLp (partialX f) 2 (Cyl.cellμ c) :=
    MemLp.of_le hj1.norm hPX.continuous.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [norm_norm] using hJ1X z)
  have hY : MemLp (partialY f) 2 (Cyl.cellμ c) :=
    MemLp.of_le hj1.norm hPY.continuous.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [norm_norm] using hJ1Y z)
  have hXX : MemLp (partialX (partialX f)) 2 (Cyl.cellμ c) :=
    MemLp.of_le hj2.norm hPXX.continuous.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [norm_norm] using hJ2X z)
  have hYY : MemLp (partialY (partialY f)) 2 (Cyl.cellμ c) :=
    MemLp.of_le hj2.norm hPYY.continuous.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [norm_norm] using hJ2Y z)
  -- Transfer to the library cell `(0, c]` for the interpolation inequalities.
  have cf : MemLp f 2 (UnforcedLeray.B0151.cellMeasure c) :=
    (memLp_cellMeasure_iff hc mf hper 2).2 hf0
  have cX : MemLp (partialX f) 2 (UnforcedLeray.B0151.cellMeasure c) :=
    (memLp_cellMeasure_iff hc mX perX 2).2 hX
  have cY : MemLp (partialY f) 2 (UnforcedLeray.B0151.cellMeasure c) :=
    (memLp_cellMeasure_iff hc mY perY 2).2 hY
  have cXX : MemLp (partialX (partialX f)) 2 (UnforcedLeray.B0151.cellMeasure c) :=
    (memLp_cellMeasure_iff hc mXX perXX 2).2 hXX
  have cYY : MemLp (partialY (partialY f)) 2 (UnforcedLeray.B0151.cellMeasure c) :=
    (memLp_cellMeasure_iff hc mYY perYY 2).2 hYY
  -- Interpolation, constant `1`, in each direction.
  have IQ := UnforcedLeray.B0151.interpolation_q hc hf2 hq cf cX cXX
  have IY := UnforcedLeray.B0151.interpolation_η (L := c) hf2 cf cY cYY
  rw [eLpNorm_cellMeasure_eq hc mX perX 2, eLpNorm_cellMeasure_eq hc mf hper 2,
    eLpNorm_cellMeasure_eq hc mXX perXX 2] at IQ
  rw [eLpNorm_cellMeasure_eq hc mY perY 2, eLpNorm_cellMeasure_eq hc mf hper 2,
    eLpNorm_cellMeasure_eq hc mYY perYY 2] at IY
  -- Second-order norms are dominated by the jet norm.
  have hQ : eLpNorm (partialX (partialX f)) 2 (Cyl.cellμ c) ≤
      eLpNorm (fun z => ‖Train.jet 2 f z‖) 2 (Cyl.cellμ c) :=
    eLpNorm_mono_real fun z => hJ2X z
  have hQY : eLpNorm (partialY (partialY f)) 2 (Cyl.cellμ c) ≤
      eLpNorm (fun z => ‖Train.jet 2 f z‖) 2 (Cyl.cellμ c) :=
    eLpNorm_mono_real fun z => hJ2Y z
  have hA : eLpNorm (partialX f) 2 (Cyl.cellμ c) ^ 2 ≤
      eLpNorm f 2 (Cyl.cellμ c) * eLpNorm (fun z => ‖Train.jet 2 f z‖) 2 (Cyl.cellμ c) :=
    IQ.trans (by gcongr)
  have hB : eLpNorm (partialY f) 2 (Cyl.cellμ c) ^ 2 ≤
      eLpNorm f 2 (Cyl.cellμ c) * eLpNorm (fun z => ‖Train.jet 2 f z‖) 2 (Cyl.cellμ c) :=
    IY.trans (by gcongr)
  -- Minkowski: `‖Df‖₂ ≤ ‖∂_q f‖₂ + ‖∂_η f‖₂`.
  have nX : AEStronglyMeasurable (fun z => ‖partialX f z‖) (Cyl.cellμ c) :=
    hPX.continuous.norm.aestronglyMeasurable
  have nY : AEStronglyMeasurable (fun z => ‖partialY f z‖) (Cyl.cellμ c) :=
    hPY.continuous.norm.aestronglyMeasurable
  have hD1 : eLpNorm (fun z => ‖Train.jet 1 f z‖) 2 (Cyl.cellμ c) ≤
      eLpNorm (partialX f) 2 (Cyl.cellμ c) + eLpNorm (partialY f) 2 (Cyl.cellμ c) := by
    have h1 : eLpNorm (fun z => ‖Train.jet 1 f z‖) 2 (Cyl.cellμ c) ≤
        eLpNorm (fun z => ‖partialX f z‖ + ‖partialY f z‖) 2 (Cyl.cellμ c) :=
      eLpNorm_mono_real fun z => by simpa only [norm_norm] using hU1 z
    have h2 : eLpNorm (fun z => ‖partialX f z‖ + ‖partialY f z‖) 2 (Cyl.cellμ c) ≤
        eLpNorm (fun z => ‖partialX f z‖) 2 (Cyl.cellμ c) +
          eLpNorm (fun z => ‖partialY f z‖) 2 (Cyl.cellμ c) :=
      eLpNorm_add_le nX nY (by norm_num)
    rw [eLpNorm_norm, eLpNorm_norm] at h2
    exact h1.trans h2
  -- Assemble: `‖Df‖₂² ≤ 2 (‖∂_q f‖₂² + ‖∂_η f‖₂²) ≤ 4 ‖f‖₂ ‖D²f‖₂`.
  have key : eLpNorm (fun z => ‖Train.jet 1 f z‖) 2 (Cyl.cellμ c) ^ 2 ≤
      4 * (eLpNorm f 2 (Cyl.cellμ c) * eLpNorm (fun z => ‖Train.jet 2 f z‖) 2 (Cyl.cellμ c)) := by
    calc eLpNorm (fun z => ‖Train.jet 1 f z‖) 2 (Cyl.cellμ c) ^ 2
        ≤ (eLpNorm (partialX f) 2 (Cyl.cellμ c) + eLpNorm (partialY f) 2 (Cyl.cellμ c)) ^ 2 := by
          gcongr
      _ ≤ 2 * (eLpNorm (partialX f) 2 (Cyl.cellμ c) ^ 2 +
            eLpNorm (partialY f) 2 (Cyl.cellμ c) ^ 2) :=
          gradInterp_enn_add_sq_le _ _
      _ ≤ 2 * (eLpNorm f 2 (Cyl.cellμ c) * eLpNorm (fun z => ‖Train.jet 2 f z‖) 2 (Cyl.cellμ c) +
            eLpNorm f 2 (Cyl.cellμ c) * eLpNorm (fun z => ‖Train.jet 2 f z‖) 2 (Cyl.cellμ c)) := by
          gcongr
      _ = 4 * (eLpNorm f 2 (Cyl.cellμ c) * eLpNorm (fun z => ‖Train.jet 2 f z‖) 2 (Cyl.cellμ c)) := by
          ring
  unfold Train.cellL2
  rw [← eLpNorm_norm (Train.jet 1 f), ← eLpNorm_norm (Train.jet 2 f)]
  exact key

end UnforcedLeray.Short.PartI
