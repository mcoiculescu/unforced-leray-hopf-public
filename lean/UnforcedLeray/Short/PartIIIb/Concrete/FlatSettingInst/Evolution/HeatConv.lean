import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Leaves

/-!
# The planar heat convolutions commute with `x ↦ -x` (source 2819-2836)

Source of record: `the November 2 reference manuscript` (73 pages).

The free part of the Volterra iteration is the heat semigroup `e^{θΔ}` (an even kernel) and its
divergence response `e^{θΔ}div` (the odd gradient kernel), as convolutions on the plane
(`B0284.heat`, `B0296.heatDiv`):

* `heat_refl`: if `g' = g(-·)` a.e. then `e^{θΔ}g'(z) = e^{θΔ}g(-z)` for every `z`;
* `heatDiv_refl`: if `T' = -T(-·)` a.e. then `e^{θΔ}div T'(z) = e^{θΔ}div T(-z)` for every `z`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol

/-- The planar heat kernel is even. -/
theorem heatKernel2_neg (θ : ℝ) (w : ℝ × ℝ) :
    UnforcedLeray.B0284.heatKernel2 θ (-w) = UnforcedLeray.B0284.heatKernel2 θ w := by
  simp only [UnforcedLeray.B0284.heatKernel2, Prod.fst_neg, Prod.snd_neg,
    UnforcedLeray.B0191.heatKernel, neg_sq]

/-- The gradient of the planar heat kernel is odd. -/
theorem gradHeatKernel2_neg (θ : ℝ) (w : ℝ × ℝ) :
    UnforcedLeray.B0296.gradHeatKernel2 θ (-w) = -UnforcedLeray.B0296.gradHeatKernel2 θ w := by
  simp only [UnforcedLeray.B0296.gradHeatKernel2, UnforcedLeray.B0296.dHeatKernel, Prod.fst_neg,
    Prod.snd_neg, UnforcedLeray.B0191.heatKernel, neg_sq, Prod.neg_mk]
  ext <;> simp only [neg_div] <;> ring

/-- **The heat semigroup commutes with the reflection** (even kernel). -/
theorem heat_refl {θ : ℝ} (hθ : 0 < θ) {g g' : ℝ × ℝ → ℝ × ℝ}
    (hg : g' =ᵐ[volume] fun z => g (-z)) (z : ℝ × ℝ) :
    UnforcedLeray.B0284.heat θ g' z = UnforcedLeray.B0284.heat θ g (-z) := by
  rw [UnforcedLeray.B0284.heat_apply_of_pos hθ, UnforcedLeray.B0284.heat_apply_of_pos hθ]
  have h1 : ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w • g' (z - w) =
      ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w • g (-(z - w)) := by
    refine integral_congr_ae ?_
    filter_upwards [((volume : Measure (ℝ × ℝ)).measurePreserving_sub_left z).quasiMeasurePreserving.ae
      hg] with w hw
    rw [hw]
  rw [h1, ← integral_neg_eq_self]
  congr 1
  funext w
  rw [heatKernel2_neg]
  congr 2
  abel

/-- **The heat-divergence response intertwines the reflections** (odd gradient kernel). -/
theorem heatDiv_refl {θ : ℝ} (hθ : 0 < θ) {T T' : ℝ × ℝ → (ℝ × ℝ) × (ℝ × ℝ)}
    (hT : T' =ᵐ[volume] fun z => -T (-z)) (z : ℝ × ℝ) :
    UnforcedLeray.B0296.heatDiv θ T' z = UnforcedLeray.B0296.heatDiv θ T (-z) := by
  rw [UnforcedLeray.B0296.heatDiv_apply_of_pos hθ, UnforcedLeray.B0296.heatDiv_apply_of_pos hθ]
  have h1 : ∫ w : ℝ × ℝ, UnforcedLeray.B0296.divKernel θ w (T' (z - w)) =
      ∫ w : ℝ × ℝ, UnforcedLeray.B0296.divKernel θ w (-T (-(z - w))) := by
    refine integral_congr_ae ?_
    filter_upwards [((volume : Measure (ℝ × ℝ)).measurePreserving_sub_left z).quasiMeasurePreserving.ae
      hT] with w hw
    rw [hw]
  rw [h1, ← integral_neg_eq_self]
  congr 1
  funext w
  have e : (-(z - -w) : ℝ × ℝ) = -z - w := by abel
  rw [e]
  simp only [UnforcedLeray.B0296.divKernel, gradHeatKernel2_neg, Prod.fst_neg, Prod.snd_neg,
    neg_smul, smul_neg, neg_neg]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol
