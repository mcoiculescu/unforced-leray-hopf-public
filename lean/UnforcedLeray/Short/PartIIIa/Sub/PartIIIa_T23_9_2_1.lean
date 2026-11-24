import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9_2

/-!
# `PartIII-a:T23/9/2/1`: `GreenInverseMeasurable` from two integral-measurability leaves

`greenInverse f r = -¼ [ (r²)⁻¹ ∫₀^r s³ f(s) ds + r² ∫_{(r,∞)} s⁻¹ f(s) ds ]`
(`Blueprint/Construction/Planar.lean:74`).  For an *arbitrary* `g : ℝ → ℂ` both `r ↦ ∫₀^r g` and
`r ↦ ∫_{(r,∞)} g` are Borel (Lebesgue integrals are `0` when `g` is not integrable).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.IIIa.T23_9_Sub

/-- Leaf `T23/9/2/1/1`: the primitive `r ↦ ∫₀^r g` is measurable for every `g : ℝ → ℂ`. -/
def IntervalPrimMeasurable : Prop :=
  ∀ g : ℝ → ℂ, Measurable (fun r : ℝ => ∫ s in (0 : ℝ)..r, g s)

/-- Leaf `T23/9/2/1/2`: the tail integral `r ↦ ∫_{(r,∞)} g` is measurable for every `g : ℝ → ℂ`. -/
def IoiTailMeasurable : Prop :=
  ∀ g : ℝ → ℂ, Measurable (fun r : ℝ => ∫ s in Ioi r, g s)

theorem greenInverse_measurable_of (h1 : IntervalPrimMeasurable) (h2 : IoiTailMeasurable) :
    GreenInverseMeasurable := by
  intro f
  unfold UnforcedLeray.Blueprint.Planar.greenInverse
  have hr : Measurable (fun r : ℝ => (r : ℂ)) := Complex.measurable_ofReal
  have a1 : Measurable (fun r : ℝ => ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s) :=
    h1 (fun s => (s : ℂ) ^ 3 * f s)
  have a2 : Measurable (fun r : ℝ => ∫ s in Ioi r, (s : ℂ)⁻¹ * f s) :=
    h2 (fun s => (s : ℂ)⁻¹ * f s)
  exact measurable_const.mul ((((hr.pow_const 2).inv).mul a1).add ((hr.pow_const 2).mul a2))

end UnforcedLeray.Short.IIIa.T23_9_Sub

#print axioms UnforcedLeray.Short.IIIa.T23_9_Sub.greenInverse_measurable_of
