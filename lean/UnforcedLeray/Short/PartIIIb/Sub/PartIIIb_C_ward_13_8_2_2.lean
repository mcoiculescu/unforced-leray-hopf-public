import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_2

/-!
# `PartIII-b:C/ward/13/8/2/2`: decomposition of `AnnularPoincare`

Source `the November 2 reference manuscript`
117-118, 2641-2642 (annular Poincare inequality used for the Deny-Lions constant).
Route: convex-set Poincare (segment formula, Cauchy-Schwarz, Fubini) -> finite chain cover of the
unit annulus -> scaling `y = R z`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub

/-- **Poincare inequality on a compact convex set of positive volume** (constant depends on `K`). -/
def ConvexPoincare : Prop :=
  ∀ K : Set UnforcedLeray.Space, Convex ℝ K → IsCompact K → 0 < (volume K).toReal →
    ∃ C : ℝ, ∀ p : UnforcedLeray.Space → ℝ, ContDiff ℝ 1 p → ∃ m : ℝ,
      ∫ y in K, (p y - m) ^ 2 ≤ C * ∫ y in K, ‖physGrad p y‖ ^ 2

/-- **Poincare inequality on the unit annulus** `{1 <= |y| <= 4}` (chaining over a finite cover by
convex sets with positive-measure overlaps). -/
def UnitAnnularPoincare : Prop :=
  ∃ C : ℝ, ∀ p : UnforcedLeray.Space → ℝ, ContDiff ℝ 1 p → ∃ m : ℝ,
    ∫ y in {y : UnforcedLeray.Space | 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 4}, (p y - m) ^ 2 ≤
      C * ∫ y in {y : UnforcedLeray.Space | 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 4}, ‖physGrad p y‖ ^ 2

/-- **Scaling step**: the unit-annulus inequality gives the scale-invariant one
(`p_R(z) = p(R z)`, integrals scale by `R^3`, gradient by `R`). -/
def AnnularScaling : Prop := UnitAnnularPoincare → AnnularPoincare

theorem annularPoincare_of (h : AnnularScaling) (hu : UnitAnnularPoincare) : AnnularPoincare := h hu

end UnforcedLeray.Short.PartIIIb.Concrete.AnnPoinSub
