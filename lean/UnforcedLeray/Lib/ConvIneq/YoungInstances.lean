import UnforcedLeray.Lib.ConvIneq.YoungGroup
import UnforcedLeray.Analysis.Pressure.Young
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Instances of the group Young inequality (INF22 A1, bypass BP1)


target A1 ("instances for Space, ℝ, ℂ, AddCircle c × ℝ") and §6 risk 5 (Haar instances on
`AddCircle c × ℝ`). The group Young inequality `UnforcedLeray.Conv.eLpNorm_convAbs_le_young`
needs a σ-finite measure invariant under translations and negation:

* on `Space = EuclideanSpace ℝ (Fin 3)`, `ℝ`, `ℂ` and `EuclideanSpace ℝ (Fin 2)` the volume
  measure has these instances already (checked by the `example`s below);
* on a product of groups, negation invariance is `isNegInvariant_prod` (absent from Mathlib);
  the volume of the cylinder `AddCircle c × ℝ` gets its instances from it.

`convAbs_space_eq` identifies the compiled ℝ³ majorant `PressureAnalysis.convAbs`
(`lean/UnforcedLeray/Analysis/Pressure/Young.lean:48`) with `Conv.convAbs volume`, so the
compiled ℝ³ statements are specializations of the group statements (BP1, "downstream").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Conv

/-- Negation invariance of a product measure (not in Mathlib at the pinned revision). -/
instance isNegInvariant_prod {G H : Type*} [AddGroup G] [AddGroup H] [MeasurableSpace G]
    [MeasurableSpace H] [MeasurableNeg G] [MeasurableNeg H] (μ : Measure G) (ν : Measure H)
    [SFinite μ] [SFinite ν] [μ.IsNegInvariant] [ν.IsNegInvariant] :
    (μ.prod ν).IsNegInvariant := by
  constructor
  change Measure.map Neg.neg (μ.prod ν) = μ.prod ν
  have h : (Neg.neg : G × H → G × H) = Prod.map Neg.neg Neg.neg := rfl
  rw [h, ← Measure.map_prod_map μ ν measurable_neg measurable_neg, Measure.map_neg_eq_self,
    Measure.map_neg_eq_self]

instance (c : ℝ) [Fact (0 < c)] : (volume : Measure (AddCircle c × ℝ)).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

instance (c : ℝ) [Fact (0 < c)] : (volume : Measure (AddCircle c × ℝ)).IsNegInvariant := by
  rw [Measure.volume_eq_prod]; exact isNegInvariant_prod _ _

example : SigmaFinite (volume : Measure Space) := inferInstance
example : (volume : Measure Space).IsAddLeftInvariant := inferInstance
example : (volume : Measure Space).IsNegInvariant := inferInstance
example : (volume : Measure ℝ).IsNegInvariant := inferInstance
example : (volume : Measure ℂ).IsAddLeftInvariant := inferInstance
example : (volume : Measure ℂ).IsNegInvariant := inferInstance
example : (volume : Measure (EuclideanSpace ℝ (Fin 2))).IsNegInvariant := inferInstance
example (c : ℝ) [Fact (0 < c)] : SigmaFinite (volume : Measure (AddCircle c × ℝ)) :=
  inferInstance

/-- Young on the cylinder group `AddCircle c × ℝ` (instance check for INF22 A1). -/
theorem eLpNorm_convAbs_le_young_cylinder (c : ℝ) [Fact (0 < c)] {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {K : AddCircle c × ℝ → E}
    {g : AddCircle c × ℝ → F} (hK : AEStronglyMeasurable K volume)
    (hg : AEStronglyMeasurable g volume) {s p r : ℝ} (hs : 1 ≤ s) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hspr : 1 / s + 1 / p = 1 + 1 / r) :
    eLpNorm (convAbs volume K g) (ENNReal.ofReal r) volume ≤
      eLpNorm K (ENNReal.ofReal s) volume * eLpNorm g (ENNReal.ofReal p) volume :=
  eLpNorm_convAbs_le_young volume hK hg hs hp hr hspr

/-- The compiled ℝ³ majorant of `Pressure/Young.lean` is the group majorant for `volume`. -/
theorem convAbs_space_eq {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (K : Space → E) (g : Space → F) :
    PressureAnalysis.convAbs K g = convAbs volume K g := rfl

end UnforcedLeray.Conv
