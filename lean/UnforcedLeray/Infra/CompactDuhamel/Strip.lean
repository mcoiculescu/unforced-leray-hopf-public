import UnforcedLeray.Infra.VolterraEvolution
import UnforcedLeray.Infra.WeaklyNullCompact

/-!
# Compact Duhamel perturbation on one strip

`paper/main.tex`, lines 332-340: "`S_0(r) 𝓑_* : X → X` is compact for `r > 0`. Its alternative
factorization through `L²` has norm `O(r^{-1/2})`. Apply the Duhamel formula to a weakly null
sequence in `X`: compactness at each positive `r` and this integrable bound show that
`E(t,s) - S_0(t-s)` is compact."

Abstract setting: `D : VolterraData 𝕜 X Y` (`UnforcedLeray.Infra.VolterraEvolution`) over a
Hilbert space `X` (`RCLike 𝕜`, `X` complete inner product space), with the hypothesis that
`S t ∘ B r : X → X` is a compact operator for every `0 < t ≤ 1` and every `r`.

* `tendsto_stripEvolution_sub_apply_of_weaklyNull`: for a weakly null sequence `x n`,
  `(E(τ,s) - S₀(τ-s)) (x n) → 0` in norm on the strip `s ≤ τ ≤ s + 1`.  By the Volterra
  equation `(E(τ,s) - S₀(τ-s)) x = ∫ r in s..τ, S (τ - r) (B r (E(r,s) x))`; for `s < r < τ`
  the sequence `E(r,s) x n` is weakly null, so the compact operator `S (τ - r) ∘ B r` maps it
  to a norm null sequence, and the integrands are dominated by
  `C₀ β (τ - r)^{-1/2} ‖E‖ sup ‖x n‖`, which is integrable: dominated convergence.
* `isCompactOperator_stripEvolution_sub`: hence `E(τ,s) - S₀(τ-s)` is compact
  (`isCompactOperator_of_forall_weaklyNull`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral Real
open scoped InnerProductSpace

namespace UnforcedLeray.Infra.CompactDuhamel

open UnforcedLeray.Infra.VolterraEvolution UnforcedLeray.Infra.WeaklyNullCompact

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ X]
  [SMulCommClass ℝ 𝕜 X]

omit [NormedSpace ℝ X] [SMulCommClass ℝ 𝕜 X] in
/-- A bounded operator maps weakly null sequences to weakly null sequences. -/
theorem weaklyNull_map (T : X →L[𝕜] X) {x : ℕ → X}
    (hx : ∀ y : X, Tendsto (fun n => ⟪y, x n⟫_𝕜) atTop (𝓝 0)) :
    ∀ y : X, Tendsto (fun n => ⟪y, T (x n)⟫_𝕜) atTop (𝓝 0) := by
  have h := (weakTendsto_zero_iff.mpr hx).map T
  rw [map_zero] at h
  exact weakTendsto_zero_iff.mp h

/-- **Duhamel term on weakly null sequences.** On the strip `s ≤ τ ≤ s + 1`, if every
`S t ∘ B r` (`0 < t ≤ 1`) is compact, then `(E(τ,s) - S₀(τ-s)) (x n) → 0` for every weakly null
sequence `x`. -/
theorem tendsto_stripEvolution_sub_apply_of_weaklyNull (D : VolterraData 𝕜 X Y)
    (hK : ∀ t r : ℝ, 0 < t → t ≤ 1 → IsCompactOperator ((D.S t).comp (D.B r)))
    {s τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) {x : ℕ → X}
    (hx : ∀ y : X, Tendsto (fun n => ⟪y, x n⟫_𝕜) atTop (𝓝 0)) :
    Tendsto (fun n => (D.stripEvolution τ s - D.S₀ (τ - s)) (x n)) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := exists_norm_le_of_weaklyNull (𝕜 := 𝕜) hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hrep : ∀ n, (D.stripEvolution τ s - D.S₀ (τ - s)) (x n) =
      ∫ r in s..τ, D.S (τ - r) (D.B r (D.stripEvolution r s (x n))) := by
    intro n
    change D.stripEvolution τ s (x n) - D.S₀ (τ - s) (x n) = _
    rw [D.stripEvolution_eq hτ, add_sub_cancel_left]
  simp only [hrep]
  have hlim : Tendsto (fun n => ∫ r in s..τ, D.S (τ - r) (D.B r (D.stripEvolution r s (x n))))
      atTop (𝓝 (∫ _ in s..τ, (0 : X))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun r => D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) * (D.stripBound * M)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      have hint := D.intervalIntegrable_integrand hτ.1 hτ.2
        (f := fun r => D.stripEvolution r s (x n))
        ((D.continuousOn_stripEvolution s (x n)).mono (Icc_subset_Icc_right hτ.2))
      exact hint.def'.aestronglyMeasurable
    · refine Eventually.of_forall fun n => ?_
      filter_upwards [ae_ne_real τ] with r hrτ hr
      rw [uIoc_of_le hτ.1] at hr
      have hr' : r ∈ Ico s τ := ⟨hr.1.le, lt_of_le_of_ne hr.2 hrτ⟩
      refine (D.norm_integrand_le hτ.2 hr' (fun r => D.stripEvolution r s (x n))).trans ?_
      have hk : 0 ≤ D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg (mul_nonneg D.C₀_nonneg D.β_nonneg) (rpow_nonneg (by linarith [hr'.2]) _)
      refine mul_le_mul_of_nonneg_left ?_ hk
      calc ‖D.stripEvolution r s (x n)‖ ≤ ‖D.stripEvolution r s‖ * ‖x n‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ D.stripBound * M :=
            mul_le_mul (D.norm_stripEvolution_le r s) (hM n) (norm_nonneg _) D.stripBound_nonneg
    · exact ((intervalIntegrable_kernel τ s τ).const_mul (D.C₀ * D.β)).mul_const _
    · filter_upwards [ae_ne_real τ] with r hrτ hr
      rw [uIoc_of_le hτ.1] at hr
      have hpos : 0 < τ - r := by
        have := lt_of_le_of_ne hr.2 hrτ
        linarith
      have hle : τ - r ≤ 1 := by linarith [hr.1, hτ.2]
      have h := tendsto_norm_of_isCompactOperator_of_weaklyNull (hK (τ - r) r hpos hle)
        (weaklyNull_map (D.stripEvolution r s) hx)
      rw [← tendsto_zero_iff_norm_tendsto_zero] at h
      exact h
  simpa only [intervalIntegral.integral_zero] using hlim

/-- **Compact Duhamel perturbation on a strip** (`paper/main.tex`, lines 332-340). Let `X` be a
Hilbert space and `D : VolterraData 𝕜 X Y` such that `S t ∘ B r : X → X` is compact for every
`0 < t ≤ 1` and every `r`. Then `E(τ,s) - S₀(τ - s)` is compact for `s ≤ τ ≤ s + 1`. -/
theorem isCompactOperator_stripEvolution_sub (D : VolterraData 𝕜 X Y)
    (hK : ∀ t r : ℝ, 0 < t → t ≤ 1 → IsCompactOperator ((D.S t).comp (D.B r)))
    {s τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) :
    IsCompactOperator (D.stripEvolution τ s - D.S₀ (τ - s)) :=
  isCompactOperator_of_forall_weaklyNull _ fun _ hx =>
    tendsto_zero_iff_norm_tendsto_zero.mp
      (tendsto_stripEvolution_sub_apply_of_weaklyNull D hK hτ hx)

end UnforcedLeray.Infra.CompactDuhamel
