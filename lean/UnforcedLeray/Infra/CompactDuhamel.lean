import UnforcedLeray.Infra.CompactDuhamel.Strip
import UnforcedLeray.Infra.CompactDuhamel.Global
import UnforcedLeray.Infra.CompactDuhamel.Spectrum

/-!
# Compact Duhamel perturbation and the essential spectrum of the period map

Abstract form of `paper/main.tex`, Section `sec:st18-329`, lines 332-357: "`S_0(r)𝓑_* : X → X`
is compact for `r > 0`. Its alternative factorization through `L²` has norm `O(r^{-1/2})`.
Apply the Duhamel formula to a weakly null sequence in `X`: compactness at each positive `r`
and this integrable bound show that `E(t,s) - S_0(t-s)` is compact. … `r_ess(𝓜) ≤ e^{-𝒯/4}` …
finitely many spectral points outside each circle of radius larger than `e^{-𝒯/4}` … We may
choose `σ < β < 2σ`, `{|ξ| = e^{β𝒯}} ∩ spec(𝓜) = ∅`."

Setting: `D : VolterraData 𝕜 X Y` (`UnforcedLeray.Infra.VolterraEvolution`) with `X` a Hilbert
space, and the compactness hypothesis

  `hK : ∀ t r, 0 < t → t ≤ 1 → IsCompactOperator ((D.S t).comp (D.B r))`.

Files:

* `CompactDuhamel/Strip.lean` (Part 1): `isCompactOperator_stripEvolution_sub`,
  `E(τ,s) - S₀(τ-s)` is compact on the strip `s ≤ τ ≤ s + 1` (weakly null sequences, dominated
  convergence in the Duhamel integral, `isCompactOperator_of_forall_weaklyNull`);
* `CompactDuhamel/Global.lean` (Part 2): `isCompactOperator_evolution_sub`, the same for all
  `s ≤ τ`, under `D.Compatible` and the semigroup law of `S₀` on `[0, ∞)`;
* `CompactDuhamel/Spectrum.lean` (Parts 3, 4): `FreeSemigroupDecay D M κ` (semigroup on
  `[0, ∞)`, `‖S₀ t‖ ≤ M e^{-κt}`), `spectralRadius_S₀_le`, `monodromy_decomposition`,
  `finite_spectrum_monodromy_inter` (finitely many spectral points of `E(P,0)` in `|z| ≥ r`,
  `r > e^{-κP}`), `exists_weight_sphere_subset_resolventSet` and `exists_weight_monodromy`
  (a spectrum-free circle `|z| = e^{βP}`, `σ₁ < β < σ₂`).

This file collects the four parts over `ℂ` in `compact_duhamel`.
-/

set_option autoImplicit false

noncomputable section

open Set Real Metric

namespace UnforcedLeray.Infra.CompactDuhamel

open UnforcedLeray.Infra.VolterraEvolution UnforcedLeray.Infra.VolterraEvolution.VolterraData

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- **Compact Duhamel perturbation and essential spectrum** (`paper/main.tex`, lines 332-357).
Let `X` be a complex Hilbert space and `D : VolterraData ℂ X Y` compatible, whose free evolution
`S₀` is a semigroup on `[0, ∞)` with `‖S₀ t‖ ≤ M e^{-κt}`, and such that `S t ∘ B r : X → X` is
compact for `0 < t ≤ 1` and all `r`. Let `P > 0`. Then

1. `E(τ,s) - S₀(τ-s)` is compact on every strip `s ≤ τ ≤ s + 1` (`stripEvolution`);
2. `E(τ,s) - S₀(τ-s)` is compact for all `s ≤ τ` (`evolution`);
3. `spectralRadius ℂ (S₀ P) ≤ e^{-κP}`, and for every `r > e^{-κP}` the period map
   `𝓜 = E(P,0)` has only finitely many spectral points with `|z| ≥ r`;
4. for `σ₁ < σ₂` with `e^{σ₁P} > e^{-κP}` some `β ∈ (σ₁, σ₂)` has the circle `|z| = e^{βP}` in
   the resolvent set of `𝓜`. -/
theorem compact_duhamel {D : VolterraData ℂ X Y} (hD : D.Compatible) {M κ : ℝ}
    (hF : FreeSemigroupDecay D M κ)
    (hK : ∀ t r : ℝ, 0 < t → t ≤ 1 → IsCompactOperator ((D.S t).comp (D.B r)))
    {P : ℝ} (hP : 0 < P) :
    (∀ s τ : ℝ, τ ∈ Icc s (s + 1) →
        IsCompactOperator (D.stripEvolution τ s - D.S₀ (τ - s))) ∧
      (∀ s τ : ℝ, s ≤ τ → IsCompactOperator (D.evolution τ s - D.S₀ (τ - s))) ∧
      spectralRadius ℂ (D.S₀ P) ≤ ENNReal.ofReal (exp (-(κ * P))) ∧
      (∀ r : ℝ, exp (-(κ * P)) < r →
        (spectrum ℂ (D.evolution P 0) ∩ {z : ℂ | r ≤ ‖z‖}).Finite) ∧
      (∀ σ₁ σ₂ : ℝ, σ₁ < σ₂ → exp (-(κ * P)) < exp (σ₁ * P) →
        ∃ β ∈ Ioo σ₁ σ₂, sphere (0 : ℂ) (exp (β * P)) ⊆ resolventSet ℂ (D.evolution P 0)) :=
  ⟨fun _ _ hτ => isCompactOperator_stripEvolution_sub D hK hτ,
    fun _ _ hsτ => isCompactOperator_evolution_sub D hD hF.S₀_comp_S₀ hK hsτ,
    spectralRadius_S₀_le hF hP.le,
    fun _ hr => finite_spectrum_monodromy_inter hD hF hK hP.le hr,
    fun _ _ h12 hσ => by
      obtain ⟨β, hβ, hsph, -⟩ := exists_weight_monodromy hD hF hK hP h12 hσ
      exact ⟨β, hβ, hsph⟩⟩

end UnforcedLeray.Infra.CompactDuhamel
