import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.VLink
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.Scale2
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.DiffLocal2

/-!
# Mean part helper: the `sepW` derivative as a rescaled product integral (T17/2)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mp_psi_map (ε : ℝ) (hε : 0 < ε) :
    Measure.map (mpPsi ε hε) (volume : Measure Space) = ENNReal.ofReal (ε⁻¹) ^ 2 • volume := by
  have e1 : (mpPsi ε hε : Space → (ℝ × ℝ) × ℝ) =
      Prod.map (Prod.map (fun a : ℝ => ε * a) (fun a : ℝ => ε * a)) (id : ℝ → ℝ) ∘
        (fun y : Space => ((y 0, y 1), y 2)) := rfl
  have hS : Measurable (Prod.map (Prod.map (fun a : ℝ => ε * a) (fun a : ℝ => ε * a)) (id : ℝ → ℝ)) :=
    ((measurable_const.mul measurable_id).prodMap (measurable_const.mul measurable_id)).prodMap
      measurable_id
  rw [e1, ← Measure.map_map hS t17s_spaceProd.measurable, t17s_spaceProd.map_eq, mp_mapS ε hε]

theorem mp_Psi_map (ε : ℝ) (hε : 0 < ε) :
    Measure.map (Prod.map (id : ℝ → ℝ) (mpPsi ε hε)) sepDiffRho =
      ENNReal.ofReal (ε⁻¹) ^ 2 • mpRho2 := by
  unfold sepDiffRho mpRho2
  rw [← Measure.map_prod_map _ _ measurable_id (mpPsi ε hε).continuous.measurable, Measure.map_id,
    mp_psi_map ε hε, Measure.prod_smul_right]

theorem mp_Psi_embedding (ε : ℝ) (hε : 0 < ε) :
    MeasurableEmbedding (Prod.map (id : ℝ → ℝ) (mpPsi ε hε)) :=
  MeasurableEmbedding.id.prodMap (mpPsi ε hε).measurableEmbedding

/-- The rescaled derivative integrand on `(λ, w)`-space. -/
def mpHW (ν ε : ℝ) (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (xo v : Space) (i : Fin 3)
    (p : ℝ × ((ℝ × ℝ) × ℝ)) : ℂ :=
  -2 * ((p.1 : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
    ((iteratedFDeriv ℝ 2 (fun x => heatLerayK (ν * (1 - p.1 ^ 2) * ε ^ 2) i j x)
      (xo - p.1 • (!₂[p.2.1.1, p.2.1.2, ε * p.2.2] : Space)) ![v, coordinateVector k] : ℝ) : ℂ) *
        ((G p.2.1 p.2.2 j k : ℝ) : ℂ))

theorem mpHW_scale (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) (μ : ℂ)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (xo v : Space) (i : Fin 3) (l : ℝ)
    (hl : l ∈ Ioo (0 : ℝ) 1) (z : Space) :
    -2 * ((l : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
      ((iteratedFDeriv ℝ 2 (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x) (ε⁻¹ • xo - l • z)
        ![v, coordinateVector k] : ℝ) : ℂ) * ((G (ε * z 0, ε * z 1) (z 2) j k : ℝ) : ℂ)) =
      (ε : ℂ) ^ 5 * mpHW ν ε μ G xo v i (l, ((ε * z 0, ε * z 1), z 2)) := by
  have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith [hl.1, hl.2])
  have harg : ε⁻¹ • xo - l • z = ε⁻¹ • (xo - l • (!₂[ε * z 0, ε * z 1, ε * z 2] : Space)) := by
    ext n
    fin_cases n <;> simp [hε.ne'] <;> field_simp
  unfold mpHW
  simp only
  rw [harg]
  have key : ∀ (j k : Fin 3), (iteratedFDeriv ℝ 2 (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)
      (ε⁻¹ • (xo - l • (!₂[ε * z 0, ε * z 1, ε * z 2] : Space))) ![v, coordinateVector k] : ℝ) =
      ε ^ 5 * iteratedFDeriv ℝ 2 (fun x => heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x)
        (xo - l • (!₂[ε * z 0, ε * z 1, ε * z 2] : Space)) ![v, coordinateVector k] := by
    intro j k
    rw [mp_scale i j _ ε ht hε]
    simp
  simp only [key, Complex.ofReal_mul, Complex.ofReal_pow]
  have hs : ∀ (a : ℂ) (f : Fin 3 → Fin 3 → ℂ), ∑ j : Fin 3, ∑ k : Fin 3, a * f j k =
      a * ∑ j : Fin 3, ∑ k : Fin 3, f j k := by
    intro a f; simp [Finset.mul_sum]
  simp only [mul_assoc, hs]
  ring

end UnforcedLeray.Short.IIIa

end
