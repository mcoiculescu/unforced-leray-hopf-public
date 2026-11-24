import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Fubini split of the physical space along the axis (`PartIII-b:C/near/masked/14/2/3/2/1/3`)

Source: `shorter-proof-2026-11-02.tex`, the `z₂`-integral in `SchurOne` (source 3996-4011).

The coordinate map `z ↦ ((z 0, z 1), z 2)` from `Space = EuclideanSpace ℝ (Fin 3)` to
`(ℝ × ℝ) × ℝ` is measure preserving, so the integral over `Space` splits into the planar
integral over `(z₀, z₁)` and the axial integral over `z₂` (`lintegral_prod`).

Adaptation: the target names `UnforcedLeray.Axi.Space` and `UnforcedLeray.Axi.vecSp`, which
the library does not define. `Axi.Space` is an abbreviation of the library's `UnforcedLeray.Space`
(`EuclideanSpace ℝ (Fin 3)`), and `Axi.vecSp v` is the point `WithLp.toLp 2 v` with coordinates
`v 0, v 1, v 2` (the convention of the draft `Concrete/ReturnRepair` file).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Axi

/-- The physical space `EuclideanSpace ℝ (Fin 3)` under the axisymmetric layer's name. -/
abbrev Space := UnforcedLeray.Space

/-- The point of `Space` with coordinates `v 0, v 1, v 2`. -/
def vecSp (v : Fin 3 → ℝ) : Space := WithLp.toLp 2 v

end UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb

theorem lintegral_space_split (F : UnforcedLeray.Axi.Space → ENNReal) (hF : Measurable F) : ∫⁻ z : UnforcedLeray.Axi.Space, F z = ∫⁻ p : ℝ × ℝ, ∫⁻ t : ℝ, F (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) := by
  -- z ↦ (z 2, (z 0, z 1)) is measure preserving: pivot the last coordinate, then split the two others
  have hA : MeasurePreserving (fun z : UnforcedLeray.Axi.Space => (z 2, (z 0, z 1))) volume volume := by
    have h : (fun z : UnforcedLeray.Axi.Space => (z 2, (z 0, z 1)))
        = (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ))
          ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2) ∘ WithLp.ofLp := by
      funext z
      rfl
    rw [h]
    have h1 := (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
    have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
    have h3 := PiLp.volume_preserving_ofLp (Fin 3)
    exact (h1.comp h2).comp h3
  have hψmp : MeasurePreserving (fun z : UnforcedLeray.Axi.Space => ((z 0, z 1), z 2)) volume volume :=
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))).comp hA
  have hφψ : ∀ z : UnforcedLeray.Axi.Space,
      UnforcedLeray.Axi.vecSp ![((z 0, z 1), z 2).1.1, ((z 0, z 1), z 2).1.2, ((z 0, z 1), z 2).2] = z := by
    intro z
    ext i
    fin_cases i <;> simp [UnforcedLeray.Axi.vecSp]
  have hφm : Measurable (fun q : (ℝ × ℝ) × ℝ => UnforcedLeray.Axi.vecSp ![q.1.1, q.1.2, q.2]) := by
    have : (fun q : (ℝ × ℝ) × ℝ => UnforcedLeray.Axi.vecSp ![q.1.1, q.1.2, q.2])
        = (WithLp.toLp 2 : (Fin 3 → ℝ) → UnforcedLeray.Axi.Space) ∘
          (fun q : (ℝ × ℝ) × ℝ => (![q.1.1, q.1.2, q.2] : Fin 3 → ℝ)) := rfl
    rw [this]
    refine (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp ?_
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact (measurable_fst.comp measurable_fst)
    · exact (measurable_snd.comp measurable_fst)
    · exact measurable_snd
  calc ∫⁻ z : UnforcedLeray.Axi.Space, F z
      = ∫⁻ z : UnforcedLeray.Axi.Space,
          F (UnforcedLeray.Axi.vecSp ![((z 0, z 1), z 2).1.1, ((z 0, z 1), z 2).1.2, ((z 0, z 1), z 2).2]) := by
        simp only [hφψ]
    _ = ∫⁻ q : (ℝ × ℝ) × ℝ, F (UnforcedLeray.Axi.vecSp ![q.1.1, q.1.2, q.2]) :=
        hψmp.lintegral_comp (hF.comp hφm)
    _ = ∫⁻ p : ℝ × ℝ, ∫⁻ t : ℝ, F (UnforcedLeray.Axi.vecSp ![p.1, p.2, t]) := by
        rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ]
        exact lintegral_prod _ (hF.comp hφm).aemeasurable
