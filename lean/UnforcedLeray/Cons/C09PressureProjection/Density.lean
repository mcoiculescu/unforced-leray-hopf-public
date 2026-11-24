import UnforcedLeray.Cons.C09PressureProjection.Cutoff
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# C9 helper: a countable dense family of tests

Step C9 (`PressureProjectionStep`, blueprint unit B0708, `paper/main.tex` lines 13719–13733;
the skeleton's "countable dense family of tests (separability of `H²`)"). Testing (2.5) on
`η(τ)∇Φ(y)` gives the Hessian relation for each scalar test `Φ` at almost every phase, with
an exceptional set that depends on `Φ`. Since the relation is a continuous functional of the
Hessian columns `hessL2 Φ ∈ (L²)³`, and `(L²)³` is separable (`Lp.SecondCountableTopology`),
a countable subfamily whose Hessians are dense among all test Hessians suffices: outside a
single null set the relation holds for all tests (`ae_forall_colPairing_hessL2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.Cons.C09

open UnforcedLeray.Blueprint UnforcedLeray.RieszLp

/-- **Countable reduction.** For a family `H : ι → E` in a separable pseudometrizable space
and continuous functionals `L a`, if `L a (H i) = 0` for `μ`-a.e. `a`, for each `i`, then
for `μ`-a.e. `a` it holds for all `i` at once. -/
theorem ae_forall_of_separable {α ι E : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace E] [TopologicalSpace.SeparableSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E]
    (H : ι → E) (L : α → E → ℝ) (hL : ∀ a, Continuous (L a))
    (h : ∀ i, ∀ᵐ a ∂μ, L a (H i) = 0) : ∀ᵐ a ∂μ, ∀ i, L a (H i) = 0 := by
  obtain ⟨t, hts, htc, hdense⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (Set.range H)).exists_countable_dense_subset
  have hpick : ∀ x : t, ∃ i, H i = x := fun x => hts x.2
  choose idx hidx using hpick
  have : Countable t := htc.to_subtype
  have hall : ∀ᵐ a ∂μ, ∀ x : t, L a x = 0 := by
    rw [ae_all_iff]
    intro x
    filter_upwards [h (idx x)] with a ha
    rw [← hidx x]
    exact ha
  filter_upwards [hall] with a ha i
  have hsub : closure t ⊆ {e | L a e = 0} :=
    closure_minimal (fun x hx => ha ⟨x, hx⟩) (isClosed_eq (hL a) continuous_const)
  exact hsub (hdense ⟨i, rfl⟩)

/-- `(L²(ℝ³;ℝ³))³` is separable (Mathlib's `Lp.SecondCountableTopology`). -/
theorem separableSpace_L2triple : TopologicalSpace.SeparableSpace (Fin 3 → L2Space) := by
  have : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨ENNReal.ofNat_ne_top⟩
  have : SecondCountableTopology L2Space := MeasureTheory.Lp.SecondCountableTopology
  infer_instance

/-- **One null set for all tests.** If for each compact smooth scalar test `Φ` the Hessian
relation `Σ_j ⟨G_j(a), ∇∂_jΦ⟩ = 0` holds for `μ`-a.e. `a`, then for `μ`-a.e. `a` it holds
for every test. -/
theorem ae_forall_colPairing_hessL2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (G : α → Fin 3 → L2Space)
    (h : ∀ Φ, IsSpatialTest Φ → ∀ᵐ a ∂μ, colPairing (G a) (hessL2 Φ) = 0) :
    ∀ᵐ a ∂μ, ∀ Φ, IsSpatialTest Φ → colPairing (G a) (hessL2 Φ) = 0 := by
  have := separableSpace_L2triple
  have hc := ae_forall_of_separable (μ := μ) (fun Φ : {Φ : Space → ℝ // IsSpatialTest Φ} =>
    hessL2 Φ.1) (fun a => colPairing (G a)) (fun a => continuous_colPairing (G a))
    (fun Φ => h Φ.1 Φ.2)
  filter_upwards [hc] with a ha Φ hΦ
  exact ha ⟨Φ, hΦ⟩

end UnforcedLeray.Cons.C09
