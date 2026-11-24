import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# `ℝ³ ≅ (ℝ × ℝ) × ℝ` and the horizontal dilation (helper for `OscFarPt`)

`∫⁻_{z ∈ ℝ³} φ((εz₀, εz₁), z₂) = ε⁻² ∫⁻_w φ(w)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

open UnforcedLeray

/-- `ℝ³ ≃ᵐ (ℝ × ℝ) × ℝ`, `z ↦ ((z₀, z₁), z₂)`. -/
def splitE : Space ≃ᵐ (ℝ × ℝ) × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).trans
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow).trans
        MeasurableEquiv.prodComm))

theorem splitE_apply (z : Space) : splitE z = ((z 0, z 1), z 2) := by
  rfl

theorem splitE_mp : MeasurePreserving splitE volume volume := by
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).trans ?_
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).trans ?_
  refine ((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)).trans ?_
  exact Measure.measurePreserving_swap

/-- the horizontal dilation as a map of `(ℝ×ℝ)×ℝ` -/
def hsc (ε : ℝ) (w : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ := ((ε * w.1.1, ε * w.1.2), w.2)

theorem hsc_emb {ε : ℝ} (hε : ε ≠ 0) : MeasurableEmbedding (hsc ε) := by
  let e : (ℝ × ℝ) × ℝ ≃ᵐ (ℝ × ℝ) × ℝ :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodCongr (Homeomorph.mulLeft₀ ε hε).toMeasurableEquiv
        (Homeomorph.mulLeft₀ ε hε).toMeasurableEquiv) (MeasurableEquiv.refl ℝ)
  exact e.measurableEmbedding

theorem hsc_map {ε : ℝ} (hε : 0 < ε) :
    Measure.map (hsc ε) (volume : Measure ((ℝ × ℝ) × ℝ)) =
      ENNReal.ofReal (ε⁻¹) ^ 2 • volume := by
  have hm : Measurable (fun x : ℝ => ε * x) := measurable_const.mul measurable_id
  have h1 : Measure.map (fun x : ℝ => ε * x) (volume : Measure ℝ) =
      ENNReal.ofReal (ε⁻¹) • volume := by
    rw [Real.map_volume_mul_left hε.ne', abs_of_pos (inv_pos.2 hε)]
  have h2 : Measure.map (Prod.map (fun x : ℝ => ε * x) (fun x : ℝ => ε * x))
      (volume : Measure (ℝ × ℝ)) = (ENNReal.ofReal (ε⁻¹) ^ 2) • volume := by
    rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ hm hm, h1, Measure.prod_smul_left,
      Measure.prod_smul_right, smul_smul, sq]
  have h3 : hsc ε = Prod.map (Prod.map (fun x : ℝ => ε * x) (fun x : ℝ => ε * x)) id := by
    funext w; rfl
  rw [h3, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (hm.prodMap hm) measurable_id,
    ← Measure.volume_eq_prod, h2, Measure.map_id, Measure.prod_smul_left]
  rfl

theorem lintegral_space_scale {ε : ℝ} (hε : 0 < ε) (φ : (ℝ × ℝ) × ℝ → ℝ≥0∞) :
    ∫⁻ z : Space, φ ((ε * z 0, ε * z 1), z 2) = ENNReal.ofReal (ε⁻¹) ^ 2 * ∫⁻ w, φ w := by
  have h1 : ∫⁻ z : Space, φ ((ε * z 0, ε * z 1), z 2) = ∫⁻ z : Space, (φ ∘ hsc ε) (splitE z) := by
    rfl
  rw [h1, splitE_mp.lintegral_comp_emb splitE.measurableEmbedding (φ ∘ hsc ε)]
  have h2 := (hsc_emb hε.ne').lintegral_map φ (μ := volume)
  rw [hsc_map hε, lintegral_smul_measure] at h2
  simp only [Function.comp]
  rw [← h2]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
