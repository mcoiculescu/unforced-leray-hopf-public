import UnforcedLeray.Analysis.Sturm.FreeResolventOperator
import UnforcedLeray.Analysis.Sturm.FreeResolventDerivativeOperator
import UnforcedLeray.Analysis.Sturm.L2TestPairing

/-!
# The actual weak free-resolvent equation for every L² datum

The compact-data Green identities pass to all L² inputs by density and the
closedness of the standard test-function weak derivative graph. Thus the
bounded extension has genuine L² first and second weak derivatives.
-/

noncomputable section
open MeasureTheory Set Filter
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob

variable {L : ℝ} (hL : 0 < L)
include hL

/-- The second derivative dictated by the actual free equation. -/
def freeResolventSecondOperator : ComplexL2 →L[ℂ] ComplexL2 :=
  (L : ℂ) ^ 2 • freeResolventOperator hL - ContinuousLinearMap.id ℂ ComplexL2

theorem coeFn_freeResolventSecondOperator (f : ComplexL2) :
    freeResolventSecondOperator hL f =ᵐ[volume]
      (fun x => (L : ℂ) ^ 2 * freeResolventOperator hL f x - f x) := by
  change ((L : ℂ) ^ 2 • freeResolventOperator hL f - f : ComplexL2) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub ((L : ℂ) ^ 2 • freeResolventOperator hL f) f,
    Lp.coeFn_smul ((L : ℂ) ^ 2) (freeResolventOperator hL f)] with x hs hm
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hs hm
  rw [hs, hm]

theorem coeFn_freeResolventSecondOperator_on_compact (f : compactL2) :
    freeResolventSecondOperator hL (f : ComplexL2) =ᵐ[volume]
      freeResolventSecond L (f : ComplexL2) := by
  filter_upwards [coeFn_freeResolventSecondOperator hL (f : ComplexL2),
    coeFn_freeResolventOperator_on_compact hL f] with x hs hu
  rw [hs, hu]
  rfl

/-- The bounded extension's first derivative is the actual weak derivative. -/
theorem freeResolventOperator_weak_one (f : ComplexL2) :
    HasWeakDerivOn univ (derivList 1)
      (freeResolventOperator hL f : ℝ → ℂ)
      (freeResolventDerivativeOperator hL f : ℝ → ℂ) := by
  refine denseRange_compactL2_subtypeL.induction_on
    (p := fun g => HasWeakDerivOn univ (derivList 1)
      (freeResolventOperator hL g : ℝ → ℂ)
      (freeResolventDerivativeOperator hL g : ℝ → ℂ)) f
    (isClosed_hasWeakDerivOn_precomp (derivList 1)
      (freeResolventOperator hL).continuous (freeResolventDerivativeOperator hL).continuous) ?_
  intro g
  apply (freeResolvent_weak_one hL (CompactL2.integrable g)).congr_ae
  · filter_upwards [coeFn_freeResolventOperator_on_compact hL g] with x hx
    exact fun _ => hx.symm
  · filter_upwards [coeFn_freeResolventDerivativeOperator_on_compact hL g] with x hx
    exact fun _ => hx.symm

/-- The actual weak second derivative for every L² input. -/
theorem freeResolventOperator_weak_two (f : ComplexL2) :
    HasWeakDerivOn univ (derivList 2)
      (freeResolventOperator hL f : ℝ → ℂ)
      (freeResolventSecondOperator hL f : ℝ → ℂ) := by
  refine denseRange_compactL2_subtypeL.induction_on
    (p := fun g => HasWeakDerivOn univ (derivList 2)
      (freeResolventOperator hL g : ℝ → ℂ)
      (freeResolventSecondOperator hL g : ℝ → ℂ)) f
    (isClosed_hasWeakDerivOn_precomp (derivList 2)
      (freeResolventOperator hL).continuous (freeResolventSecondOperator hL).continuous) ?_
  intro g
  obtain ⟨a, b, hab⟩ := CompactL2.exists_interval g
  apply (freeResolvent_weak_two hL (CompactL2.integrable g) hab).congr_ae
  · filter_upwards [coeFn_freeResolventOperator_on_compact hL g] with x hx
    exact fun _ => hx.symm
  · filter_upwards [coeFn_freeResolventSecondOperator_on_compact hL g] with x hx
    exact fun _ => hx.symm

/-- The derivative operator itself has the claimed first weak derivative. -/
theorem freeResolventDerivativeOperator_weak_one (f : ComplexL2) :
    HasWeakDerivOn univ (derivList 1)
      (freeResolventDerivativeOperator hL f : ℝ → ℂ)
      (freeResolventSecondOperator hL f : ℝ → ℂ) := by
  refine denseRange_compactL2_subtypeL.induction_on
    (p := fun g => HasWeakDerivOn univ (derivList 1)
      (freeResolventDerivativeOperator hL g : ℝ → ℂ)
      (freeResolventSecondOperator hL g : ℝ → ℂ)) f
    (isClosed_hasWeakDerivOn_precomp (derivList 1)
      (freeResolventDerivativeOperator hL).continuous (freeResolventSecondOperator hL).continuous) ?_
  intro g
  obtain ⟨a, b, hab⟩ := CompactL2.exists_interval g
  apply (freeResolventDeriv_weak_one hL (CompactL2.integrable g) hab).congr_ae
  · filter_upwards [coeFn_freeResolventDerivativeOperator_on_compact hL g] with x hx
    exact fun _ => hx.symm
  · filter_upwards [coeFn_freeResolventSecondOperator_on_compact hL g] with x hx
    exact fun _ => hx.symm

/-- The free equation as an equality of actual L² equivalence classes. -/
theorem freeResolventOperator_equation (f : ComplexL2) :
    -freeResolventSecondOperator hL f + (L : ℂ) ^ 2 • freeResolventOperator hL f = f := by
  change -((L : ℂ) ^ 2 • freeResolventOperator hL f - f) +
    (L : ℂ) ^ 2 • freeResolventOperator hL f = f
  abel

end UnforcedLeray.Sturm
