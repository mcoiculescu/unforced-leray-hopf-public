import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import UnforcedLeray.Short.PartIIIa.Defs

/-!
# Split helper: `Space ≃ (ℝ × ℝ) × ℝ` and the horizontal scaling (T17/1)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem t17s_spaceProd :
    MeasurePreserving (fun y : Space => ((y 0, y 1), y 2)) volume volume := by
  have h1 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h3 : MeasurePreserving (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) volume volume :=
    volume_preserving_finTwoArrow ℝ
  have h4 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ))
      volume volume := (MeasurePreserving.id volume).prod h3
  have h5 := h4.comp (h2.comp h1)
  have h6 : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ).symm volume volume :=
    (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) (volume : Measure ℝ)).symm _
  have h7 := h6.comp h5
  have e : (fun y : Space => ((y 0, y 1), y 2)) =
      (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ).symm ∘
      Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ∘
        ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘
          ⇑(MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm := by
    funext y
    simp [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.finTwoArrow]
    simp [Fin.tail]
    rfl
  rw [e]
  exact h7

theorem t17s_scale (ε : ℝ) (hε : 0 < ε) (f : (ℝ × ℝ) × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ w : (ℝ × ℝ) × ℝ, f ((ε * w.1.1, ε * w.1.2), w.2) =
      ENNReal.ofReal (ε⁻¹) ^ 2 * ∫⁻ w, f w := by
  have hm : Measurable (fun a : ℝ => ε * a) := measurable_const.mul measurable_id
  have h1 : Measure.map (fun a : ℝ => ε * a) volume = ENNReal.ofReal |ε⁻¹| • volume :=
    Real.map_volume_mul_left hε.ne'
  rw [abs_of_pos (inv_pos.2 hε)] at h1
  set c := ENNReal.ofReal ε⁻¹ with hc
  have h2 : Measure.map (Prod.map (fun a : ℝ => ε * a) (fun a : ℝ => ε * a))
      (volume : Measure (ℝ × ℝ)) = c ^ 2 • volume := by
    rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ hm hm, h1, Measure.prod_smul_left,
      Measure.prod_smul_right, smul_smul, sq]
  have h3 : Measure.map (Prod.map (Prod.map (fun a : ℝ => ε * a) (fun a : ℝ => ε * a)) (id : ℝ → ℝ))
      (volume : Measure ((ℝ × ℝ) × ℝ)) = c ^ 2 • volume := by
    rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (hm.prodMap hm) measurable_id, h2,
      Measure.map_id, Measure.prod_smul_left, ← Measure.volume_eq_prod]
  have hS : Measurable (Prod.map (Prod.map (fun a : ℝ => ε * a) (fun a : ℝ => ε * a)) (id : ℝ → ℝ)) :=
    (hm.prodMap hm).prodMap measurable_id
  have := lintegral_map hf hS (μ := (volume : Measure ((ℝ × ℝ) × ℝ)))
  rw [h3, lintegral_smul_measure] at this
  exact this.symm

end UnforcedLeray.Short.IIIa

end
