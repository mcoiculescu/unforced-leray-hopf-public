import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Fubini on `Space = ℝ³` (helper for `PartIII-b:C/rep/2/4/{2,3,4,6}`)

`∫_{ℝ³} f = ∫∫∫ f(x,y,s) dy dx` as an iterated integral (volume on `EuclideanSpace ℝ (Fin 3)` against
`ℝ × ℝ × ℝ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `Space ≃ ℝ × ℝ × ℝ` is volume preserving. -/
theorem measurePreserving_spaceProd :
    MeasurePreserving (fun y : Space => (y 0, (y 1, y 2))) volume volume := by
  have h1 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h3 : MeasurePreserving (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) volume volume :=
    volume_preserving_finTwoArrow ℝ
  have h4 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ))
      volume volume := (MeasurePreserving.id volume).prod h3
  have h5 := h4.comp (h2.comp h1)
  have e : (fun y : Space => (y 0, (y 1, y 2))) =
      Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ∘
        ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘
          ⇑(MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm := by
    funext y
    simp [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.finTwoArrow, Fin.succAbove]
    exact ⟨rfl, rfl⟩
  rw [e]
  exact h5

/-- **Iterated form of the volume integral on `Space`.** -/
theorem lintegral_space_xys (f : Space → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y : Space, f y = ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ s : ℝ, f !₂[x, y, s] := by
  have hmp := measurePreserving_spaceProd
  set ψ : ℝ × ℝ × ℝ → Space := fun q => !₂[q.1, q.2.1, q.2.2] with hψ
  have hψc : Continuous ψ := by
    simp only [hψ]
    fun_prop
  have hψm : Measurable ψ := hψc.measurable
  have hcomp : ∀ y : Space, ψ (y 0, (y 1, y 2)) = y := by
    intro y
    ext i
    fin_cases i <;> simp [hψ]
  have h1 := hmp.lintegral_comp (hf.comp hψm)
  simp only [Function.comp, hcomp] at h1
  rw [h1, Measure.volume_eq_prod, lintegral_prod (fun z => f (ψ z)) (hf.comp hψm).aemeasurable,
    Measure.volume_eq_prod]
  refine lintegral_congr fun x => ?_
  rw [lintegral_prod (fun z => f (ψ (x, z))) (hf.comp (hψm.comp measurable_prodMk_left)).aemeasurable]

/-- Reordering of a triple integral: `dy dx` outside `ds` versus `ds` outside. -/
theorem lintegral_xys_swap (F : ℝ × ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ s : ℝ, F (x, y, s) = ∫⁻ s : ℝ, ∫⁻ x : ℝ, ∫⁻ y : ℝ, F (x, y, s) := by
  have h1 : ∀ x : ℝ, ∫⁻ y : ℝ, ∫⁻ s : ℝ, F (x, y, s) = ∫⁻ s : ℝ, ∫⁻ y : ℝ, F (x, y, s) := by
    intro x
    refine lintegral_lintegral_swap ?_
    exact (hF.comp (by fun_prop : Measurable fun p : ℝ × ℝ => (x, p.1, p.2))).aemeasurable
  simp_rw [h1]
  refine lintegral_lintegral_swap ?_
  have : Measurable fun p : ℝ × ℝ => ∫⁻ y : ℝ, F (p.1, y, p.2) :=
    (hF.comp (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2, q.1.2))).lintegral_prod_right'
  exact this.aemeasurable

/-- The area of the disk `{x² + y² ≤ r²} ⊂ ℝ²` is `π r²`. -/
theorem volume_disk (r : ℝ) (hr : 0 ≤ r) :
    volume {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2} = ENNReal.ofReal (Real.pi * r ^ 2) := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
    {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2}
  have hset : (Complex.measurableEquivRealProd ⁻¹' {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2}) =
      Metric.closedBall (0 : ℂ) r := by
    ext a
    simp only [Set.mem_preimage, Complex.measurableEquivRealProd_apply, Set.mem_setOf_eq,
      Metric.mem_closedBall, dist_zero_right]
    rw [Complex.norm_def, Complex.normSq_apply]
    constructor
    · intro h
      exact Real.sqrt_le_iff.2 ⟨hr, by nlinarith⟩
    · intro h
      have h2 := (Real.sqrt_le_left hr).1 h
      nlinarith
  rw [← h, hset, Complex.volume_closedBall, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr]
  rw [mul_comm]
  congr 1
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

end UnforcedLeray.Short.PartIIIb.Concrete
