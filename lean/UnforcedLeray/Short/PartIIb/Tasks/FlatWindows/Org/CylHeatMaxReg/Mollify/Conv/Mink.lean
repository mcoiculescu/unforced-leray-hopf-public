import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import UnforcedLeray.Lib.SobolevB.Mollify
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3_3

/-!
# Part II-b, task `PartII-b:T13/1/4/3/3/1` (`chmMink`): Minkowski's integral inequality

Source: `the November 2 reference manuscript` (SP) lines 1933-1935. Proof:
`chmConv ρ g - g = ∫ ρ(y) (g(· - y) - g) dy` (since `∫ ρ = 1`), then Minkowski's integral
inequality `PlanarBS.Conv.eLpNorm_integral_le` for `μ = cylMeas c`, `ν = volume`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal

/-- A finite scalar multiple of a σ-finite measure is σ-finite. -/
theorem chm_sigmaFinite_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (c : ℝ≥0∞) (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  rw [sigmaFinite_iff]
  exact ⟨{ set := spanningSets μ
           set_mem := fun _ => mem_univ _
           finite := fun i => by
             rw [Measure.smul_apply, smul_eq_mul]
             exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc) (measure_spanningSets_lt_top μ i)
           spanning := iUnion_spanningSets μ }⟩

/-- `cylMeas c` is absolutely continuous with respect to Lebesgue measure on `Coord`. -/
theorem chm_cylMeas_ac (c : ℝ) (_hc : 0 < c) : cylMeas c ≪ (volume : Measure Coord) := by
  intro s hs
  have hM : (volume : Measure Coord) (toMeasurable volume s) = 0 := by
    rw [measure_toMeasurable]; exact hs
  have hMm : MeasurableSet (toMeasurable volume s) := measurableSet_toMeasurable _ _
  refine measure_mono_null (subset_toMeasurable (volume : Measure Coord) s) ?_
  have hvol0 : ∫⁻ x, (volume : Measure (ℝ × ℝ)) (Prod.mk x ⁻¹' toMeasurable volume s) = 0 := by
    rw [← Measure.prod_apply hMm, ← Measure.volume_eq_prod]
    exact hM
  have hslice : ∀ x : ℝ, UnforcedLeray.Cyl.avgμ c (Prod.mk x ⁻¹' toMeasurable volume s) ≤
      ENNReal.ofReal c⁻¹ * (volume : Measure (ℝ × ℝ)) (Prod.mk x ⁻¹' toMeasurable volume s) := by
    intro x
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    rw [Measure.smul_apply, smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ zero_le
    exact Measure.restrict_apply_le _ _
  unfold cylMeas
  refine le_antisymm ?_ zero_le
  calc ((volume : Measure ℝ).prod (UnforcedLeray.Cyl.avgμ c)) (toMeasurable volume s)
      = ∫⁻ x, UnforcedLeray.Cyl.avgμ c (Prod.mk x ⁻¹' toMeasurable volume s) := Measure.prod_apply hMm
    _ ≤ ∫⁻ x, ENNReal.ofReal c⁻¹ * (volume : Measure (ℝ × ℝ)) (Prod.mk x ⁻¹' toMeasurable volume s) :=
        lintegral_mono hslice
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ x, (volume : Measure (ℝ × ℝ)) (Prod.mk x ⁻¹' toMeasurable volume s) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = 0 := by rw [hvol0, mul_zero]

/-- The difference map `(x, y) ↦ x - y` is quasi measure preserving from `μ.prod volume` to
`volume`, for every `μ` (Tonelli, with translation invariance of Lebesgue measure in the slices). -/
theorem chm_sub_qmp (μ : Measure Coord) :
    Measure.QuasiMeasurePreserving (fun p : Coord × Coord => p.1 - p.2) (μ.prod volume) volume := by
  have hm : Measurable (fun p : Coord × Coord => p.1 - p.2) := measurable_fst.sub measurable_snd
  refine ⟨hm, ?_⟩
  intro N hN
  have hM : (volume : Measure Coord) (toMeasurable volume N) = 0 := by
    rw [measure_toMeasurable]; exact hN
  have hMm : MeasurableSet (toMeasurable volume N) := measurableSet_toMeasurable _ _
  refine le_antisymm ?_ zero_le
  calc Measure.map (fun p : Coord × Coord => p.1 - p.2) (μ.prod volume) N
      ≤ Measure.map (fun p : Coord × Coord => p.1 - p.2) (μ.prod volume)
          (toMeasurable volume N) := measure_mono (subset_toMeasurable _ _)
    _ = (μ.prod volume) ((fun p : Coord × Coord => p.1 - p.2) ⁻¹' toMeasurable volume N) :=
        Measure.map_apply hm hMm
    _ = 0 := by
        rw [Measure.prod_apply (hm hMm)]
        have hz : ∀ x : Coord,
            (volume : Measure Coord) (Prod.mk x ⁻¹' ((fun p : Coord × Coord => p.1 - p.2) ⁻¹'
              toMeasurable volume N)) = 0 := by
          intro x
          have h2 : Prod.mk x ⁻¹' ((fun p : Coord × Coord => p.1 - p.2) ⁻¹'
              toMeasurable volume N) = (fun y : Coord => x - y) ⁻¹' toMeasurable volume N := rfl
          rw [h2, (Measure.measurePreserving_sub_left (volume : Measure Coord) x).measure_preimage
            hMm.nullMeasurableSet, hM]
        simp only [hz, lintegral_zero]

/-- Minkowski's integral inequality for the cylinder measure: the `L^r(cylMeas c)` norm of the
mollified difference is bounded by the average of the translation differences. -/
theorem chmMink : UnforcedLeray.Short.IIb.ChmMink := by
  intro r hr c hc ρ g hρc hρs hρint hg
  -- Pointwise identity: `chmConv ρ g x - g x = ∫ ρ(y) (g(x - y) - g x) dy`.
  have hcyl : ∀ x : Coord, chmConv ρ g x - g x = ∫ y, (ρ y : ℂ) * (g (x - y) - g x) := by
    intro x
    have h1 : Integrable (fun y : Coord => (ρ y : ℂ) * g (x - y)) volume := by
      have h := (hρs.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip
        hg hρc x).integrable_swap
      have h' : Integrable (fun y : Coord => ρ y • g (x - y)) volume := by simpa using h
      simpa only [Complex.real_smul] using h'
    have h2 : Integrable (fun y : Coord => (ρ y : ℂ) * g x) volume := by
      have hi : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρs
      exact hi.ofReal.mul_const (g x)
    have hint : ∫ y, (ρ y : ℂ) = 1 := by
      rw [show (∫ y, (ρ y : ℂ)) = ((∫ y, ρ y : ℝ) : ℂ) from integral_ofReal, hρint]; simp
    have e : ∫ y, (ρ y : ℂ) * (g (x - y) - g x)
        = (∫ y, (ρ y : ℂ) * g (x - y)) - ∫ y, (ρ y : ℂ) * g x := by
      rw [← integral_sub h1 h2]
      congr 1
      ext y
      ring
    simp only [chmConv]
    rw [e, integral_mul_const, hint, one_mul]
  -- Measurability on the product.
  have hgv : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  have hgc : AEStronglyMeasurable g (cylMeas c) := hgv.mono_ac (chm_cylMeas_ac c hc)
  have hF : AEStronglyMeasurable
      (Function.uncurry fun (x y : Coord) => (ρ y : ℂ) * (g (x - y) - g x))
      ((cylMeas c).prod (volume : Measure Coord)) := by
    have h1 : AEStronglyMeasurable (fun p : Coord × Coord => (ρ p.2 : ℂ))
        ((cylMeas c).prod (volume : Measure Coord)) :=
      (Complex.continuous_ofReal.comp (hρc.comp continuous_snd)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : Coord × Coord => g (p.1 - p.2))
        ((cylMeas c).prod (volume : Measure Coord)) :=
      hgv.comp_quasiMeasurePreserving (chm_sub_qmp (cylMeas c))
    have h3 : AEStronglyMeasurable (fun p : Coord × Coord => g p.1)
        ((cylMeas c).prod (volume : Measure Coord)) :=
      hgc.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    exact h1.mul (h2.sub h3)
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.mpr hr
  have hp' : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA : SigmaFinite (UnforcedLeray.Cyl.avgμ c) :=
    chm_sigmaFinite_smul ((volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.Cyl.cell c))
      (ENNReal.ofReal c⁻¹) ENNReal.ofReal_ne_top
  have hσ : SigmaFinite (cylMeas c) := by
    unfold cylMeas
    infer_instance
  have hmink := UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le
    (μ := cylMeas c) (ν := (volume : Measure Coord))
    (F := fun (x y : Coord) => (ρ y : ℂ) * (g (x - y) - g x)) hF hp hp'
  have hfun : (fun x => chmConv ρ g x - g x)
      = fun x => ∫ y, (ρ y : ℂ) * (g (x - y) - g x) := funext hcyl
  show eLpNorm (fun x => chmConv ρ g x - g x) (ENNReal.ofReal r) (cylMeas c) ≤ _
  rw [hfun]
  refine hmink.trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  have hn : ‖(ρ y : ℂ)‖ₑ = ENNReal.ofReal |ρ y| := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  show eLpNorm (fun x => (ρ y : ℂ) * (g (x - y) - g x)) (ENNReal.ofReal r) (cylMeas c)
      = ENNReal.ofReal |ρ y| * eLpNorm (fun x => g (x - y) - g x) (ENNReal.ofReal r) (cylMeas c)
  rw [← hn]
  exact eLpNorm_const_smul (ρ y : ℂ) (fun x => g (x - y) - g x) (ENNReal.ofReal r) (cylMeas c)

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.chmMink
