import UnforcedLeray.Infra.AnalyticFredholm.FiniteRank
import UnforcedLeray.Infra.AnalyticFredholm.Local
import UnforcedLeray.Infra.AnalyticFredholm.Global
import UnforcedLeray.Infra.AnalyticFredholm.Spectrum

/-!
# Analytic Fredholm theorem (discreteness form)

General infrastructure for the localization of `paper/main.tex` (§ "A right inverse on the
ancient interval", lines 341–357, where Glück, *Functional Analysis I*, Theorem 6.2.9 is cited for
the finiteness of the spectrum of the period map outside every circle of radius larger than the
essential spectral radius).

Setting: `X` a complex Banach space, operators `X →L[ℂ] X`.  "Approximable" (`IsApproximable`)
means: a norm limit of finite-rank operators; approximable operators are compact
(`IsApproximable.isCompactOperator`), so compactness need not be assumed separately.

Files:

* `AnalyticFredholm/FiniteRank.lean`: `IsFiniteRank`, `IsApproximable`, the normal form
  `sumRankOne`, compactness, stability under composition, and the determinant criterion
  `isUnit_one_sub_sumRankOne_iff` (via Mathlib's Fredholm alternative);
* `AnalyticFredholm/Local.lean`: the local holomorphic determinant `exists_local_det` and the
  local dichotomy `eventually_not_isUnit_or_eventually_isUnit`;
* `AnalyticFredholm/Global.lean`: the theorem `analyticFredholm` and its consequences
  (discreteness, closedness in `U`, finiteness on compacta, analyticity of `(1 - F)⁻¹`);
* `AnalyticFredholm/Spectrum.lean`: the corollary `finite_spectrum_add_inter` for
  `spectrum ℂ (A + K)` outside a circle of radius larger than the spectral radius of `A`.

This file packages the main theorem as a single statement, `analyticFredholm_main`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Infra.AnalyticFredholm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **Analytic Fredholm theorem, packaged.**  Let `U ⊆ ℂ` be open and connected (preconnected
suffices), `F : ℂ → (X →L[ℂ] X)` analytic on `U`, and every `F z` (`z ∈ U`) a norm limit of
finite-rank operators (hence compact).  If `1 - F z₀` is invertible for some `z₀ ∈ U`, then the
singular set `S = {z ∈ U | ¬ IsUnit (1 - F z)}` satisfies:

1. every point of `U` has a punctured neighbourhood disjoint from `S`;
2. `S` is discrete;
3. `S` is closed in `U`;
4. `S ∩ K` is finite for every compact `K ⊆ U`;
5. `U \ S` is open;
6. `z ↦ (1 - F z)⁻¹` (`Ring.inverse`) is analytic on `U \ S`. -/
theorem analyticFredholm_main {F : ℂ → X →L[ℂ] X} {U : Set ℂ} (hUo : IsOpen U)
    (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U)
    (happrox : ∀ z ∈ U, IsApproximable (F z)) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hinv : IsUnit (1 - F z₀)) :
    (∀ w ∈ U, ∀ᶠ z in 𝓝[≠] w, IsUnit (1 - F z)) ∧
    IsDiscrete (singularSet F U) ∧
    closure (singularSet F U) ∩ U ⊆ singularSet F U ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ U → (singularSet F U ∩ K).Finite) ∧
    IsOpen (U \ singularSet F U) ∧
    AnalyticOnNhd ℂ (fun z => Ring.inverse (1 - F z)) (U \ singularSet F U) :=
  ⟨analyticFredholm hU hF happrox hz₀ hinv,
    analyticFredholm_isDiscrete hU hF happrox hz₀ hinv,
    analyticFredholm_closure_inter_subset hU hF happrox hz₀ hinv,
    fun _ hK hKU => analyticFredholm_finite_inter_compact hU hF happrox hz₀ hinv hK hKU,
    isOpen_sdiff_singularSet hUo hF.continuousOn,
    analyticOnNhd_ring_inverse_one_sub hF⟩

end UnforcedLeray.Infra.AnalyticFredholm
