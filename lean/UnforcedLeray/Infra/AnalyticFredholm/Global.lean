import UnforcedLeray.Infra.AnalyticFredholm.Local
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.DiscreteSubset

/-!
# The analytic Fredholm theorem (discreteness form)

Let `X` be a complex Banach space, `U ⊆ ℂ` preconnected, and `F : ℂ → (X →L[ℂ] X)` analytic
on a neighbourhood of each point of `U`, with every `F z` (`z ∈ U`) a norm limit of finite-rank
operators (`IsApproximable`; such operators are compact, `IsApproximable.isCompactOperator`).
If `1 - F z₀` is invertible for one `z₀ ∈ U`, then the singular set

`singularSet F U = {z ∈ U | ¬ IsUnit (1 - F z)}`

has no accumulation point in `U`:

* `analyticFredholm`: every `w ∈ U` has a punctured neighbourhood on which `1 - F z` is
  invertible;
* `analyticFredholm_codiscreteWithin`: `{z | IsUnit (1 - F z)}` is codiscrete within `U`
  (Mathlib's `Filter.codiscreteWithin`);
* `analyticFredholm_not_accPt`, `analyticFredholm_isDiscrete`,
  `analyticFredholm_closure_inter_subset`: the singular set is discrete and closed in `U`;
* `analyticFredholm_finite_inter_compact`: it meets every compact `K ⊆ U` in a finite set;
* `analyticOnNhd_ring_inverse_one_sub`: `z ↦ (1 - F z)⁻¹` (`Ring.inverse`) is analytic on
  `U \ singularSet F U`.

`analyticFredholm_of_differentiableOn` takes `DifferentiableOn ℂ F U` on an open `U` instead.

Proof: by `eventually_not_isUnit_or_eventually_isUnit` (finite-rank approximation and a holomorphic
determinant) every point of `U` lies in the open set `A` of points near which `1 - F` is never
invertible, or in the open set `B` of points with a punctured neighbourhood on which `1 - F` is
invertible.  `A ∩ B = ∅`, `z₀ ∈ B`, so preconnectedness of `U` forces `U ∩ A = ∅`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Infra.AnalyticFredholm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The points of `U` at which `1 - F z` is not invertible. -/
def singularSet (F : ℂ → X →L[ℂ] X) (U : Set ℂ) : Set ℂ :=
  {z | z ∈ U ∧ ¬ IsUnit (1 - F z)}

/-- **Analytic Fredholm theorem.** Let `U ⊆ ℂ` be preconnected, `F` analytic on a neighbourhood
of each point of `U`, and `F z` approximable by finite-rank operators for `z ∈ U`.  If
`1 - F z₀` is invertible for some `z₀ ∈ U`, then every `w ∈ U` has a punctured neighbourhood on
which `1 - F z` is invertible. -/
theorem analyticFredholm {F : ℂ → X →L[ℂ] X} {U : Set ℂ} (hU : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F U) (happrox : ∀ z ∈ U, IsApproximable (F z)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) (hinv : IsUnit (1 - F z₀)) :
    ∀ w ∈ U, ∀ᶠ z in 𝓝[≠] w, IsUnit (1 - F z) := by
  set A : Set ℂ := {w | ∀ᶠ z in 𝓝 w, ¬ IsUnit (1 - F z)} with hAdef
  set B : Set ℂ := {w | ∀ᶠ z in 𝓝[≠] w, IsUnit (1 - F z)} with hBdef
  have hAopen : IsOpen A := isOpen_iff_mem_nhds.mpr fun w hw => hw.eventually_nhds
  have hBopen : IsOpen B := by
    rw [isOpen_iff_mem_nhds]
    intro w hw
    have hw' : ∀ᶠ z in 𝓝 w, z ∈ ({w}ᶜ : Set ℂ) → IsUnit (1 - F z) :=
      eventually_nhdsWithin_iff.mp hw
    filter_upwards [hw'.eventually_nhds] with y hy
    by_cases hyw : y = w
    · rw [hyw]; exact hw
    · have hne : ∀ᶠ z in 𝓝 y, z ≠ w := isOpen_ne.mem_nhds hyw
      exact nhdsWithin_le_nhds ((hy.and hne).mono fun z hz => hz.1 hz.2)
  have hcover : U ⊆ A ∪ B := fun w hw =>
    eventually_not_isUnit_or_eventually_isUnit (hF w hw) (happrox w hw)
  have hdisj : ∀ w, w ∈ A → w ∈ B → False := by
    intro w hA hB
    obtain ⟨z, hz⟩ := ((hA.filter_mono nhdsWithin_le_nhds).and hB).exists
    exact hz.1 hz.2
  have hz₀B : z₀ ∈ B := (hcover hz₀).resolve_left fun h => h.self_of_nhds hinv
  have hAU : ∀ w ∈ U, w ∉ A := by
    intro w hw hwA
    obtain ⟨x, _, hxA, hxB⟩ := hU A B hAopen hBopen hcover ⟨w, hw, hwA⟩ ⟨z₀, hz₀, hz₀B⟩
    exact hdisj x hxA hxB
  intro w hw
  exact (hcover hw).resolve_left (hAU w hw)

/-- Variant of `analyticFredholm` for `F` complex differentiable on an open set `U`. -/
theorem analyticFredholm_of_differentiableOn {F : ℂ → X →L[ℂ] X} {U : Set ℂ} (hUo : IsOpen U)
    (hU : IsPreconnected U) (hF : DifferentiableOn ℂ F U)
    (happrox : ∀ z ∈ U, IsApproximable (F z)) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hinv : IsUnit (1 - F z₀)) :
    ∀ w ∈ U, ∀ᶠ z in 𝓝[≠] w, IsUnit (1 - F z) :=
  analyticFredholm hU (hF.analyticOnNhd hUo) happrox hz₀ hinv

section Consequences

variable {F : ℂ → X →L[ℂ] X} {U : Set ℂ}

/-- Metric form: every `w ∈ U` has a ball on which `1 - F z` is invertible except possibly at
`z = w`. -/
theorem analyticFredholm_exists_ball (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U)
    (happrox : ∀ z ∈ U, IsApproximable (F z)) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hinv : IsUnit (1 - F z₀)) :
    ∀ w ∈ U, ∃ ε > 0, ∀ z ∈ Metric.ball w ε, z ≠ w → IsUnit (1 - F z) := by
  intro w hw
  have h := eventually_nhdsWithin_iff.mp (analyticFredholm hU hF happrox hz₀ hinv w hw)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
  exact ⟨ε, hε, fun z hz hzw => hball z hz hzw⟩

/-- The invertibility set is codiscrete within `U` (`Filter.codiscreteWithin`), i.e. its
complement in `U` is discrete and closed in `U`. -/
theorem analyticFredholm_codiscreteWithin (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U)
    (happrox : ∀ z ∈ U, IsApproximable (F z)) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hinv : IsUnit (1 - F z₀)) :
    {z | IsUnit (1 - F z)} ∈ codiscreteWithin U := by
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro w hw
  exact mem_of_superset (analyticFredholm hU hF happrox hz₀ hinv w hw) Set.subset_union_left

/-- No point of `U` is an accumulation point of the singular set. -/
theorem analyticFredholm_not_accPt (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U)
    (happrox : ∀ z ∈ U, IsApproximable (F z)) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hinv : IsUnit (1 - F z₀)) :
    ∀ w ∈ U, ¬ AccPt w (𝓟 (singularSet F U)) := by
  intro w hw hacc
  rw [accPt_iff_frequently] at hacc
  have h := eventually_nhdsWithin_iff.mp (analyticFredholm hU hF happrox hz₀ hinv w hw)
  obtain ⟨z, hz⟩ := (hacc.and_eventually h).exists
  exact hz.1.2.2 (hz.2 hz.1.1)

/-- The singular set is discrete. -/
theorem analyticFredholm_isDiscrete (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U)
    (happrox : ∀ z ∈ U, IsApproximable (F z)) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hinv : IsUnit (1 - F z₀)) :
    IsDiscrete (singularSet F U) := by
  rw [isDiscrete_iff_discreteTopology]
  exact discreteTopology_of_noAccPts fun w hw =>
    analyticFredholm_not_accPt hU hF happrox hz₀ hinv w hw.1

/-- The singular set is closed in `U`. -/
theorem analyticFredholm_closure_inter_subset (hU : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F U) (happrox : ∀ z ∈ U, IsApproximable (F z)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) (hinv : IsUnit (1 - F z₀)) :
    closure (singularSet F U) ∩ U ⊆ singularSet F U := by
  rintro w ⟨hcl, hw⟩
  refine ⟨hw, fun hwu => ?_⟩
  have h := eventually_nhdsWithin_iff.mp (analyticFredholm hU hF happrox hz₀ hinv w hw)
  have h' : ∀ᶠ z in 𝓝 w, IsUnit (1 - F z) := h.mono fun z hz => by
    by_cases hzw : z = w
    · rw [hzw]; exact hwu
    · exact hz hzw
  rw [mem_closure_iff_frequently] at hcl
  obtain ⟨z, hz⟩ := (hcl.and_eventually h').exists
  exact hz.1.2 hz.2

/-- The singular set meets every compact subset of `U` in a finite set. -/
theorem analyticFredholm_finite_inter_compact (hU : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F U) (happrox : ∀ z ∈ U, IsApproximable (F z)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) (hinv : IsUnit (1 - F z₀)) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    (singularSet F U ∩ K).Finite := by
  have hnhds : ∀ w ∈ K, {z | z ≠ w → IsUnit (1 - F z)} ∈ 𝓝 w := fun w hw =>
    eventually_nhdsWithin_iff.mp (analyticFredholm hU hF happrox hz₀ hinv w (hKU hw))
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover _ hnhds
  refine t.finite_toSet.subset ?_
  rintro z ⟨⟨-, hz⟩, hzK⟩
  obtain ⟨w, hwt, hzw⟩ := Set.mem_iUnion₂.mp (hcover hzK)
  by_cases h : z = w
  · rw [h]; exact hwt
  · exact absurd (hzw h) hz

end Consequences

/-- `z ↦ (1 - F z)⁻¹` is analytic at every point where `F` is analytic and `1 - F z` is
invertible; in particular on `U \ singularSet F U` when `F` is analytic on `U`. -/
theorem analyticOnNhd_ring_inverse_one_sub {F : ℂ → X →L[ℂ] X} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (fun z => Ring.inverse (1 - F z)) (U \ singularSet F U) := by
  intro w hw
  have hwu : IsUnit (1 - F w) := by
    by_contra h
    exact hw.2 ⟨hw.1, h⟩
  exact (analyticAt_inverse (𝕜 := ℂ) hwu.unit).comp_of_eq
    (analyticAt_const.sub (hF w hw.1)) hwu.unit_spec.symm

/-- On an open `U`, the invertibility set `U \ singularSet F U` is open when `F` is
continuous on `U`. -/
theorem isOpen_sdiff_singularSet {F : ℂ → X →L[ℂ] X} {U : Set ℂ} (hUo : IsOpen U)
    (hF : ContinuousOn F U) : IsOpen (U \ singularSet F U) := by
  have heq : U \ singularSet F U = U ∩ (fun z => 1 - F z) ⁻¹' {x | IsUnit x} := by
    ext z
    simp only [singularSet, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_preimage, not_and, not_not]
    constructor
    · rintro ⟨hz, h⟩; exact ⟨hz, h hz⟩
    · rintro ⟨hz, h⟩; exact ⟨hz, fun _ => h⟩
  rw [heq]
  exact (continuousOn_const.sub hF).isOpen_inter_preimage hUo Units.isOpen

end UnforcedLeray.Infra.AnalyticFredholm
