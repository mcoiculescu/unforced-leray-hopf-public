import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.MollRegular

/-!
# Leaf `MollSliceDeriv`: the derivative of an `s`-slice of the tensor mollification

Proves `MollSliceDeriv` (defined in `Sub/T11_6.lean`) by the chain rule applied to the slice
embedding `z ↦ (s, z)`, the formula `mollRegular` for the derivative of `mollC`, and the product
rule for the tensor kernel `ρ₁(y.1) ρ₂(y.2)` in the planar direction `(0, u)`.
Classical argument; the source of record is
`the November 2 reference manuscript`, SP 2618 (free uniqueness step).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The derivative of the tensor kernel in the planar direction `(0, u)`. -/
theorem msd_fderiv_tensorK (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) (h : IsMollKer δ ρ₁ ρ₂)
    (y : Coord) (u : ℝ × ℝ) :
    fderiv ℝ (tensorK ρ₁ ρ₂) y (0, u) = ρ₁ y.1 * fderiv ℝ ρ₂ y.2 u := by
  have hd1 : DifferentiableAt ℝ ρ₁ y.1 := (h.smooth₁.differentiable (by simp)) _
  have hd2 : DifferentiableAt ℝ ρ₂ y.2 := (h.smooth₂.differentiable (by simp)) _
  have hA : HasFDerivAt (fun y : Coord => ρ₁ y.1)
      ((fderiv ℝ ρ₁ y.1).comp (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) y :=
    hd1.hasFDerivAt.comp y hasFDerivAt_fst
  have hB : HasFDerivAt (fun y : Coord => ρ₂ y.2)
      ((fderiv ℝ ρ₂ y.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) y :=
    hd2.hasFDerivAt.comp y hasFDerivAt_snd
  have hM : HasFDerivAt (fun y : Coord => ρ₁ y.1 * ρ₂ y.2)
      (ρ₁ y.1 • (fderiv ℝ ρ₂ y.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
        ρ₂ y.2 • (fderiv ℝ ρ₁ y.1).comp (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) y :=
    hA.mul hB
  have htk : tensorK ρ₁ ρ₂ = fun y : Coord => ρ₁ y.1 * ρ₂ y.2 := rfl
  rw [htk, hM.fderiv]
  simp

/-- **Leaf `MollSliceDeriv`.** The `s`-slice of the tensor mollification of the cut-off has the
planar derivative given by the convolution of the cut-off against the tensor kernel's derivative. -/
theorem mollSliceDeriv : UnforcedLeray.Short.IIb.MollSliceDeriv := by
  intro g δ ρ₁ ρ₂ hδ hK hloc s z u
  obtain ⟨hC, hD⟩ := mollRegular g δ ρ₁ ρ₂ hδ hK hloc
  have hinner : HasFDerivAt (fun w : ℝ × ℝ => ((s, w) : Coord))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) z :=
    (hasFDerivAt_const s z).prodMk (hasFDerivAt_id z)
  have hdiff : DifferentiableAt ℝ (mollC δ ρ₁ ρ₂ g) (s, z) :=
    (hC.differentiable (by simp)) _
  have hcomp : HasFDerivAt (mollSlice δ ρ₁ ρ₂ g s)
      ((fderiv ℝ (mollC δ ρ₁ ρ₂ g) (s, z)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) z :=
    hdiff.hasFDerivAt.comp z hinner
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rw [hD (s, z) (0, u)]
  congr 1
  funext x
  simp only [msd_fderiv_tensorK δ ρ₁ ρ₂ hK, Prod.fst_sub, Prod.snd_sub]

end UnforcedLeray.Short.IIb
