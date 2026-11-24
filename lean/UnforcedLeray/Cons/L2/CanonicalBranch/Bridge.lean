import UnforcedLeray.Blueprint.Construction.Planar
import UnforcedLeray.Units.B0010

/-!
# G3b, part 2: profiles of the blueprint versus elements of `X_G`

`paper/main.tex`, line 675 (`eq:st18-t00005`: `X_G` and its norm `∫₀^∞ |f₂|² G⁻¹ r dr`); blueprint
unit B0010. The blueprint statement of G3b (`Blueprint.Planar.IsCanonicalBranch`) is written for
profiles `f : ℝ → ℂ` with `MemXG f` and the norm `gaussianNorm f`; the evolution of G3b is built on
B0010's Hilbert space `XG = L²((0,∞), G⁻¹ r dr)`. This file identifies the two.

* `gaussianWeightInv_eq`: the blueprint's `G⁻¹` is B0010's `(radialGaussianWeight)⁻¹`;
* `memLp_of_memXG`, `memXG_of_memLp`: membership agrees;
* **`gaussianNorm_eq_norm`**: if a profile `f` is a representative of `u ∈ X_G`
  (`f =ᵐ[xGMeasure] u`), then `gaussianNorm f = ‖u‖`;
* `gaussianPairing_eq_inner`: the blueprint pairing `⟨f, g⟩_{X_G}` (`eq:st18-t00005`, line 676)
  is the inner product `⟪g, f⟫` of B0010's `X_G` (Mathlib's convention: conjugate-linear in the
  first slot).

All integrals are of nonnegative integrable functions (`norm_sq_toLp`), so no junk value enters.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 Blueprint.Planar

theorem gaussianWeightInv_eq (r : ℝ) :
    gaussianWeightInv r = (radialGaussianWeight r)⁻¹ := by
  rw [radialGaussianWeight_inv]
  rfl

theorem memLp_of_memXG {f : Profile} (hf : MemXG f) : MemLp f 2 xGMeasure := by
  rw [memLp_iff_integrableOn hf.measurable]
  refine hf.integrable.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [gaussianWeightInv_eq]
  ring

theorem memXG_of_memLp {f : Profile} (hm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : MemLp f 2 xGMeasure) : MemXG f := by
  refine ⟨hm, ?_⟩
  rw [memLp_iff_integrableOn hm] at hf
  refine hf.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [gaussianWeightInv_eq]
  ring

theorem gaussianNorm_eq_norm_toLp {f : Profile} (hf : MemLp f 2 xGMeasure) :
    gaussianNorm f = ‖hf.toLp f‖ := by
  rw [gaussianNorm, ← Real.sqrt_sq (norm_nonneg (hf.toLp f)), norm_sq_toLp]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [gaussianWeightInv_eq]
  ring

/-- **The blueprint norm of a representative is the `X_G` norm.** -/
theorem gaussianNorm_eq_norm {f : Profile} {u : XG} (h : f =ᵐ[xGMeasure] (u : ℝ → ℂ)) :
    gaussianNorm f = ‖u‖ := by
  have hf : MemLp f 2 xGMeasure := (Lp.memLp u).ae_eq h.symm
  rw [gaussianNorm_eq_norm_toLp hf]
  congr 1
  exact Lp.ext ((MemLp.coeFn_toLp hf).trans h)

/-- **The blueprint pairing is the inner product of `X_G`.** -/
theorem gaussianPairing_eq_inner {f g : Profile} (hf : MemXG f) (hg : MemXG g) :
    gaussianPairing f g =
      inner ℂ ((memLp_of_memXG hg).toLp g) ((memLp_of_memXG hf).toLp f) := by
  rw [← pairing_eq_inner, pairing_toLp, gaussianPairing]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp only [gaussianWeightInv_eq]

end UnforcedLeray.Cons.G3b
