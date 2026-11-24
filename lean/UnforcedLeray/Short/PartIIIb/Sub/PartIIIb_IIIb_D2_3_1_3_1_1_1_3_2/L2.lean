import UnforcedLeray.Lib.Axisymmetric.Cylindrical
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Cylinder slicing (`PartIII-b:IIIb-D2/3/1/3/1/1/1/3/2/2`)

Source 3631-3646.  The cylinder `{ϱ ≤ r}` lies in the box `[-r,r]²` in the coordinates `(z 0, z 1)`,
so the integrand is bounded by `1_{[-r,r]}(z 0) · 1_{[-r,r]}(z 1) · G(z 2)`.  The integral over
`EuclideanSpace ℝ (Fin 3)` is transferred to `Fin 3 → ℝ` (`PiLp.volume_preserving_ofLp`) and
factorised by Fubini on the product `ℝ × (Fin 2 → ℝ)` and then `ℝ × ℝ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Two-coordinate product integral on `Fin 2 → ℝ`. -/
theorem farSlice_fin2 (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ q : Fin 2 → ℝ, f (q 0) * g (q 1) ∂(Measure.pi fun _ : Fin 2 => (volume : Measure ℝ)) =
      (∫⁻ t, f t) * (∫⁻ t, g t) := by
  have hmp := measurePreserving_finTwoArrow (volume : Measure ℝ)
  have hmeas : Measurable (fun p : ℝ × ℝ => f p.1 * g p.2) := by fun_prop
  calc ∫⁻ q : Fin 2 → ℝ, f (q 0) * g (q 1) ∂(Measure.pi fun _ : Fin 2 => (volume : Measure ℝ))
      = ∫⁻ p : ℝ × ℝ, f p.1 * g p.2 ∂((volume : Measure ℝ).prod volume) :=
        hmp.lintegral_comp hmeas
    _ = (∫⁻ t, f t) * (∫⁻ t, g t) := lintegral_prod_mul hf.aemeasurable hg.aemeasurable

/-- Three-coordinate product integral on `Fin 3 → ℝ`. -/
theorem farSlice_fin3 (f0 f1 f2 : ℝ → ℝ≥0∞) (h0 : Measurable f0) (h1 : Measurable f1)
    (h2 : Measurable f2) :
    ∫⁻ y : Fin 3 → ℝ, f0 (y 0) * (f1 (y 1) * f2 (y 2)) =
      (∫⁻ t, f0 t) * ((∫⁻ t, f1 t) * (∫⁻ t, f2 t)) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) 0
  have hmeas : Measurable (fun p : ℝ × (Fin 2 → ℝ) => f0 p.1 * (f1 (p.2 0) * f2 (p.2 1))) := by
    fun_prop
  have hg : Measurable (fun q : Fin 2 → ℝ => f1 (q 0) * f2 (q 1)) := by fun_prop
  calc ∫⁻ y : Fin 3 → ℝ, f0 (y 0) * (f1 (y 1) * f2 (y 2))
      = ∫⁻ p : ℝ × (Fin 2 → ℝ), f0 p.1 * (f1 (p.2 0) * f2 (p.2 1))
          ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ))) :=
        hmp.lintegral_comp hmeas
    _ = (∫⁻ t, f0 t) * ∫⁻ q : Fin 2 → ℝ, f1 (q 0) * f2 (q 1)
          ∂(Measure.pi fun _ : Fin 2 => (volume : Measure ℝ)) :=
        lintegral_prod_mul h0.aemeasurable hg.aemeasurable
    _ = (∫⁻ t, f0 t) * ((∫⁻ t, f1 t) * (∫⁻ t, f2 t)) := by
        rw [farSlice_fin2 f1 f2 h1 h2]

theorem farSlice (r : ℝ) (hr : 0 < r) (G : ℝ → ℝ≥0∞) (hG : Measurable G) : ∫⁻ z : Space, Set.indicator {z : Space | ϱ z ≤ r} (fun z => G (z 2)) z ≤ ENNReal.ofReal (4 * r ^ 2) * ∫⁻ t : ℝ, G t := by
  have hBm : Measurable ((Icc (-r) r).indicator (fun _ : ℝ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator measurableSet_Icc
  have hset : MeasurableSet {y : Fin 3 → ℝ | Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  have hgm : Measurable (fun y : Fin 3 → ℝ =>
      Set.indicator {y : Fin 3 → ℝ | Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ r} (fun y => G (y 2)) y) :=
    (hG.comp (measurable_pi_apply 2)).indicator hset
  have hfun : ∀ z : Space, Set.indicator {z : Space | ϱ z ≤ r} (fun z => G (z 2)) z =
      Set.indicator {y : Fin 3 → ℝ | Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ r} (fun y => G (y 2))
        (WithLp.ofLp z) := fun z => rfl
  have hgsum : ∫⁻ z : Space, Set.indicator {z : Space | ϱ z ≤ r} (fun z => G (z 2)) z =
      ∫⁻ y : Fin 3 → ℝ, Set.indicator {y : Fin 3 → ℝ | Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ r}
        (fun y => G (y 2)) y := by
    rw [lintegral_congr hfun]
    exact (PiLp.volume_preserving_ofLp (Fin 3)).lintegral_comp hgm
  have hpt : ∀ y : Fin 3 → ℝ,
      Set.indicator {y : Fin 3 → ℝ | Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ r} (fun y => G (y 2)) y ≤
        (Icc (-r) r).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (y 0) *
          ((Icc (-r) r).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (y 1) * G (y 2)) := by
    intro y
    by_cases h : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ r
    · obtain ⟨_, hsq⟩ := Real.sqrt_le_iff.1 h
      have h0 : y 0 ∈ Icc (-r) r :=
        ⟨by nlinarith [sq_nonneg (y 1)], by nlinarith [sq_nonneg (y 1)]⟩
      have h1 : y 1 ∈ Icc (-r) r :=
        ⟨by nlinarith [sq_nonneg (y 0)], by nlinarith [sq_nonneg (y 0)]⟩
      have hmem : y ∈ {y : Fin 3 → ℝ | Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ r} := h
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h0, Set.indicator_of_mem h1]
      simp
    · have hmem : y ∉ {y : Fin 3 → ℝ | Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ r} := h
      rw [Set.indicator_of_notMem hmem]
      exact zero_le
  calc ∫⁻ z : Space, Set.indicator {z : Space | ϱ z ≤ r} (fun z => G (z 2)) z
      = ∫⁻ y : Fin 3 → ℝ, Set.indicator {y : Fin 3 → ℝ | Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ r}
          (fun y => G (y 2)) y := hgsum
    _ ≤ ∫⁻ y : Fin 3 → ℝ, (Icc (-r) r).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (y 0) *
          ((Icc (-r) r).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (y 1) * G (y 2)) :=
        lintegral_mono hpt
    _ = (∫⁻ t, (Icc (-r) r).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t) *
          ((∫⁻ t, (Icc (-r) r).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t) * ∫⁻ t : ℝ, G t) :=
        farSlice_fin3 _ _ _ hBm hBm hG
    _ = ENNReal.ofReal (4 * r ^ 2) * ∫⁻ t : ℝ, G t := by
        rw [lintegral_indicator_const measurableSet_Icc, one_mul, Real.volume_Icc, ← mul_assoc,
          ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ r - -r)]
        rw [show (r - -r) * (r - -r) = 4 * r ^ 2 by ring]

end UnforcedLeray.Short.PartIIIb.Concrete
