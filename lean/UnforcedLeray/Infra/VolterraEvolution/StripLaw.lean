import UnforcedLeray.Infra.VolterraEvolution.Strip
import UnforcedLeray.Infra.VolterraEvolution.Cocycle

/-!
# Evolution law and periodicity of the strip evolution

* `stripEvolution_comp`: if the free evolution is a semigroup compatible with the smoothing
  family (`VolterraData.Compatible`), then `E(τ,r) E(r,s) = E(τ,s)` for
  `s ≤ r ≤ τ ≤ s + 1`;
* `stripEvolution_periodic`: if `B` is `P`-periodic then `E(τ+P, s+P) = E(τ,s)`.

Both are consequences of the uniqueness theorem `eqOn_stripEvolution`
(`paper/main.tex`, lines 296-306).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral Real

namespace UnforcedLeray.Infra.VolterraEvolution

namespace VolterraData

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (D : VolterraData 𝕜 X Y)

/-- Semigroup compatibility of the data: `S₀ a S₀ b = S₀ (a + b)` and `S₀ a S b = S (a + b)`
for elapsed times in the unit strip (in the manuscript both are the semigroup law of the free
similarity evolution, `S` being `S₀` viewed as a map `L² → H¹`). -/
structure Compatible : Prop where
  S₀_comp_S₀ : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b ≤ 1 → (D.S₀ a).comp (D.S₀ b) = D.S₀ (a + b)
  S₀_comp_S : ∀ a b : ℝ, 0 ≤ a → 0 < b → a + b ≤ 1 → (D.S₀ a).comp (D.S b) = D.S (a + b)

variable [NormedSpace ℝ X] [SMulCommClass ℝ 𝕜 X] [CompleteSpace X]

/-- **Evolution law on the strip.** `E(τ,r) E(r,s) = E(τ,s)` for `s ≤ r ≤ τ ≤ s + 1`. -/
theorem stripEvolution_comp {D : VolterraData 𝕜 X Y} (hD : D.Compatible) {s r τ : ℝ}
    (hsr : s ≤ r) (hrτ : r ≤ τ) (hτ : τ ≤ s + 1) :
    (D.stripEvolution τ r).comp (D.stripEvolution r s) = D.stripEvolution τ s := by
  ext x
  rw [ContinuousLinearMap.comp_apply]
  have hr : r ∈ Icc s (s + 1) := ⟨hsr, hrτ.trans hτ⟩
  have hcs : ContinuousOn (fun t => D.stripEvolution t s x) (Icc s (s + 1)) :=
    D.continuousOn_stripEvolution s x
  have key : ∀ t ∈ Icc r (s + 1), D.stripEvolution t s x =
      D.S₀ (t - r) (D.stripEvolution r s x) +
        ∫ σ in r..t, D.S (t - σ) (D.B σ (D.stripEvolution σ s x)) := by
    intro t ht
    have ht' : t ∈ Icc s (s + 1) := ⟨hsr.trans ht.1, ht.2⟩
    have hint : IntervalIntegrable (fun σ => D.S (t - σ) (D.B σ (D.stripEvolution σ s x)))
        volume s t :=
      D.intervalIntegrable_integrand ht'.1 ht'.2 (hcs.mono (Icc_subset_Icc_right ht'.2))
    have hint1 : IntervalIntegrable (fun σ => D.S (t - σ) (D.B σ (D.stripEvolution σ s x)))
        volume s r :=
      hint.mono_set (by rw [uIcc_of_le hsr, uIcc_of_le ht'.1]; exact Icc_subset_Icc_right ht.1)
    have hint2 : IntervalIntegrable (fun σ => D.S (t - σ) (D.B σ (D.stripEvolution σ s x)))
        volume r t :=
      hint.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le ht'.1]; exact Icc_subset_Icc_left hsr)
    have hintr : IntervalIntegrable (fun σ => D.S (r - σ) (D.B σ (D.stripEvolution σ s x)))
        volume s r :=
      D.intervalIntegrable_integrand hsr hr.2 (hcs.mono (Icc_subset_Icc_right hr.2))
    have e1 : D.S₀ (t - r) (D.S₀ (r - s) x) = D.S₀ (t - s) x := by
      have := congrArg (fun L : X →L[𝕜] X => L x)
        (hD.S₀_comp_S₀ (t - r) (r - s) (by linarith [ht.1]) (by linarith) (by linarith [ht.2]))
      simpa only [ContinuousLinearMap.comp_apply, sub_add_sub_cancel] using this
    have e2 : D.S₀ (t - r) (∫ σ in s..r, D.S (r - σ) (D.B σ (D.stripEvolution σ s x))) =
        ∫ σ in s..r, D.S (t - σ) (D.B σ (D.stripEvolution σ s x)) := by
      rw [← (D.S₀ (t - r)).intervalIntegral_comp_comm hintr]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_ne_real r] with σ hσr hσ
      rw [uIoc_of_le hsr] at hσ
      have hlt : σ < r := lt_of_le_of_ne hσ.2 hσr
      have := congrArg (fun L : Y →L[𝕜] X => L (D.B σ (D.stripEvolution σ s x)))
        (hD.S₀_comp_S (t - r) (r - σ) (by linarith [ht.1]) (by linarith)
          (by linarith [hσ.1, ht.2]))
      simpa only [ContinuousLinearMap.comp_apply, sub_add_sub_cancel] using this
    rw [D.stripEvolution_eq hr x, map_add, e1, e2, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    exact D.stripEvolution_eq ht' x
  exact (D.eqOn_stripEvolution (s := r) (T := s + 1) (by linarith)
    (hcs.mono (Icc_subset_Icc_left hsr)) key τ ⟨hrτ, hτ⟩).symm

/-- The strip evolution satisfies the local law of `Cocycle` (multiplication in
`X →L[𝕜] X` is composition). -/
theorem localLaw_stripEvolution {D : VolterraData 𝕜 X Y} (hD : D.Compatible) :
    Cocycle.LocalLaw D.stripEvolution := fun _ _ _ hsr hrτ hτ => by
  rw [ContinuousLinearMap.mul_def]
  exact stripEvolution_comp hD hsr hrτ hτ

/-- **Periodicity.** If the coefficients are `P`-periodic, the strip evolution is jointly
`P`-periodic: `E(τ + P, s + P) = E(τ, s)` (for all `τ, s`). -/
theorem stripEvolution_periodic {P : ℝ} (hB : ∀ r, D.B (r + P) = D.B r) (τ s : ℝ) :
    D.stripEvolution (τ + P) (s + P) = D.stripEvolution τ s := by
  by_cases hτ : τ ∈ Icc s (s + 1)
  · ext x
    have hcont : ContinuousOn (fun t => D.stripEvolution (t + P) (s + P) x) (Icc s (s + 1)) :=
      (D.continuousOn_stripEvolution (s + P) x).comp (continuousOn_id.add continuousOn_const)
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    refine D.eqOn_stripEvolution le_rfl hcont (fun t ht => ?_) τ hτ
    have ht' : t + P ∈ Icc (s + P) (s + P + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [D.stripEvolution_eq ht' x, add_sub_add_right_eq_sub]
    congr 1
    rw [← intervalIntegral.integral_comp_add_right]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [add_sub_add_right_eq_sub, hB]
  · have hτ' : τ + P ∉ Icc (s + P) (s + P + 1) := fun h =>
      hτ ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [D.stripEvolution_of_notMem hτ, D.stripEvolution_of_notMem hτ']

end VolterraData

end UnforcedLeray.Infra.VolterraEvolution
