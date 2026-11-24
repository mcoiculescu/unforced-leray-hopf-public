import UnforcedLeray.Short.PartIIIa.Sub.T20_4

/-!
# Part III-a, task `PartIII-a:T20/4/5`: the horizontal mean of `ω ∈ X_{m,c}` is `ω̄`

Proves `CTE.MeanPartOfX` (statement in `Sub/T20_4.lean`). Source of record:
`the November 2 reference manuscript`, lines 3236-3240 (the zero mode of the
vorticity is the horizontal mean `ω̄(η) = c⁻¹ ∫_{-c/2}^{c/2} ω(q, η) dq`).

Proof. `B0581.meanPart_ae` and `B0581.modeCoeff_zero`:
`meanPart (ofX ω) (q, η) = c⁻¹ ∫_{qInt c} (ofX ω)(q', η) dq'` for a.e. `(q, η)`; `ofX ω = ω` a.e.
on the cell (`coeFn_ofX`), hence (Fubini-type argument as in `B0583.ae_modeCoeff_congr`) for a.e.
`η` the `q`-integrals agree; `integral_complex_ofReal`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Short.IIIa

namespace CTE

theorem meanPartOfX : MeanPartOfX := by
  intro c hc m hm ω
  have hmean := B0581.meanPart_ae c (B0581.ofX c m hm ω)
  have hof := B0581.coeFn_ofX c m hm ω
  have hslice : ∀ᵐ η ∂(volume : Measure ℝ),
      B0581.modeCoeff c 0 (B0581.ofX c m hm ω : B0579.Plane → ℂ) η =
        ((B0583.omegaBar c ω η : ℝ) : ℂ) := by
    rw [EventuallyEq, B0581.ae_cellVol] at hof
    have h1 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := B0581.μq c)).quasiMeasurePreserving.ae_eq_comp hof
    have h2 := Measure.ae_ae_of_ae_prod h1
    filter_upwards [h2] with η hη
    rw [B0581.modeCoeff_zero, B0583.omegaBar]
    have : ∫ q in B0581.qInt c, (B0581.ofX c m hm ω : B0579.Plane → ℂ) (q, η) =
        ∫ q in B0581.qInt c, ((ω (q, η) : ℝ) : ℂ) := by
      refine integral_congr_ae ?_
      filter_upwards [hη] with q hq
      simpa using hq
    rw [this, integral_complex_ofReal, smul_eq_mul]
    push_cast
    rfl
  have hsnd : Measure.QuasiMeasurePreserving (Prod.snd : B0579.Plane → ℝ) (B0581.cellVol c)
      volume := by
    rw [B0581.cellVol_eq]
    exact Measure.quasiMeasurePreserving_snd
  filter_upwards [hmean, hsnd.ae hslice] with x h1 h2
  rw [h1, h2]

end CTE

end UnforcedLeray.Short.IIIa
