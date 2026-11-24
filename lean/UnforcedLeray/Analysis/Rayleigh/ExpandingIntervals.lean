import Mathlib.Topology.Order.Compact
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic

/-!
# Actual compact-test containment in expanding intervals

Compactness gives finite lower and upper bounds, and the two endpoint limits
then give eventual strict containment. The support assumptions used in the
annular weak limit are thus derived from the actual expanding geometry.
-/

open Filter Set
namespace UnforcedLeray.Rayleigh

variable {ι : Type*} {p : Filter ι} {left right : ι → ℝ}

/-- Every fixed compact set is eventually strictly inside the expanding interval. -/
theorem eventually_compact_subset_expanding_Ioo
    (hl : Tendsto left p atBot) (hr : Tendsto right p atTop)
    {K : Set ℝ} (hK : IsCompact K) :
    ∀ᶠ i in p, K ⊆ Ioo (left i) (right i) := by
  obtain ⟨a, ha⟩ := hK.bddBelow
  obtain ⟨b, hb⟩ := hK.bddAbove
  filter_upwards [hl.eventually_lt_atBot a, hr.eventually_gt_atTop b] with i hi hj
  intro x hx
  exact ⟨hi.trans_le (ha hx), (hb hx).trans_lt hj⟩

theorem eventually_compact_subset_expanding_Ioc
    (hl : Tendsto left p atBot) (hr : Tendsto right p atTop)
    {K : Set ℝ} (hK : IsCompact K) :
    ∀ᶠ i in p, K ⊆ Ioc (left i) (right i) :=
  (eventually_compact_subset_expanding_Ioo hl hr hK).mono
    (fun _ hi => hi.trans Ioo_subset_Ioc_self)

/-- The actual topological support of every fixed compact test is eventually interior. -/
theorem eventually_tsupport_subset_expanding_Ioo {E : Type*} [Zero E]
    (hl : Tendsto left p atBot) (hr : Tendsto right p atTop)
    {φ : ℝ → E} (hφ : HasCompactSupport φ) :
    ∀ᶠ i in p, tsupport φ ⊆ Ioo (left i) (right i) :=
  eventually_compact_subset_expanding_Ioo hl hr hφ

theorem eventually_tsupport_subset_expanding_Ioc {E : Type*} [Zero E]
    (hl : Tendsto left p atBot) (hr : Tendsto right p atTop)
    {φ : ℝ → E} (hφ : HasCompactSupport φ) :
    ∀ᶠ i in p, tsupport φ ⊆ Ioc (left i) (right i) :=
  eventually_compact_subset_expanding_Ioc hl hr hφ

/-- Strict support containment actually removes both endpoint test values. -/
theorem endpoints_eq_zero_of_tsupport_subset_Ioo {E : Type*} [Zero E]
    {φ : ℝ → E} {l r : ℝ} (hφ : tsupport φ ⊆ Ioo l r) :
    φ l = 0 ∧ φ r = 0 := by
  have hl : l ∉ tsupport φ := fun ht => (lt_irrefl l) (hφ ht).1
  have hr : r ∉ tsupport φ := fun ht => (lt_irrefl r) (hφ ht).2
  exact ⟨image_eq_zero_of_notMem_tsupport hl, image_eq_zero_of_notMem_tsupport hr⟩

/-- Endpoint cancellation in integration by parts follows from the actual geometry. -/
theorem eventually_test_endpoints_zero {E : Type*} [Zero E]
    (hl : Tendsto left p atBot) (hr : Tendsto right p atTop)
    {φ : ℝ → E} (hφ : HasCompactSupport φ) :
    ∀ᶠ i in p, φ (left i) = 0 ∧ φ (right i) = 0 :=
  (eventually_tsupport_subset_expanding_Ioo hl hr hφ).mono
    (fun _ hi => endpoints_eq_zero_of_tsupport_subset_Ioo hi)

/-- The derivative support stays in the same compact set, so one eventual
containment handles the original test and its derivative together. -/
theorem eventually_test_and_deriv_support
    (hl : Tendsto left p atBot) (hr : Tendsto right p atTop)
    {φ : ℝ → ℂ} (hφ : HasCompactSupport φ) :
    ∀ᶠ i in p, tsupport φ ⊆ Ioo (left i) (right i) ∧
      tsupport (deriv φ) ⊆ Ioo (left i) (right i) :=
  (eventually_tsupport_subset_expanding_Ioo hl hr hφ).mono
    (fun _ hi => ⟨hi, tsupport_deriv_subset.trans hi⟩)

/-- Derivative endpoint values vanish as well; no derivative boundary condition is assumed. -/
theorem eventually_test_and_deriv_endpoints_zero
    (hl : Tendsto left p atBot) (hr : Tendsto right p atTop)
    {φ : ℝ → ℂ} (hφ : HasCompactSupport φ) :
    ∀ᶠ i in p, (φ (left i) = 0 ∧ φ (right i) = 0) ∧
      (deriv φ (left i) = 0 ∧ deriv φ (right i) = 0) :=
  (eventually_test_and_deriv_support hl hr hφ).mono
    (fun _ hi => ⟨endpoints_eq_zero_of_tsupport_subset_Ioo hi.1,
      endpoints_eq_zero_of_tsupport_subset_Ioo hi.2⟩)

end UnforcedLeray.Rayleigh
