import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1.Slices
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `L2SqDiff`: `F r - F s ∈ L²` with `∫ (F r - F s)² ≤ (r - s)² K` (source 341-348)

The left Riemann sums `R n` of `∂ₜF` over `[s, r]` satisfy `R n ² ≤ ((r-s)²/n) ∑ₖ (∂ₜF t_k)²`,
whose integral is at most `(r-s)² K`. Since `R n → F r - F s` pointwise, Fatou's lemma
transfers the bound to the limit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open UnforcedLeray.Cyl

theorem l2SqDiff : UnforcedLeray.Short.PartI.L2SqDeriv.L2SqDiff := by
  intro μ F s ε K H _ r hr
  obtain ⟨hε, hC, hF, hD⟩ := H
  have hK : 0 ≤ K := le_trans (integral_nonneg fun z => sq_nonneg _)
    (hD s (by simp [hε])).2
  have hslice_m : ∀ n : ℕ, AEStronglyMeasurable
      (UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice F s r n) μ := fun n =>
    UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice_aesm F s ε r hr
      (fun t ht => (hD t ht).1.aestronglyMeasurable) n
  have hDm : AEStronglyMeasurable (fun z => F r z - F s z) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hslice_m
      (Eventually.of_forall fun z =>
        UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice_tendsto F hC s r z)
  -- integrability of the Cauchy-Schwarz majorant
  have hBint : ∀ n : ℕ, Integrable (fun z => ((r - s) ^ 2 / (n : ℝ)) *
      ∑ k ∈ Finset.range n, (deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2) μ := by
    intro n
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun k hk => ?_
    exact (hD _ (UnforcedLeray.Short.PartI.L2SqDeriv.slice_sample_dist hr
      (Finset.mem_range.1 hk))).1.integrable_sq
  -- lower-semicontinuity bound on the lintegrals of the Riemann sums
  have hfin : ∀ n : ℕ, ∫⁻ z, ENNReal.ofReal
      ((UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice F s r n z) ^ 2) ∂μ
        ≤ ENNReal.ofReal ((r - s) ^ 2 * K) := by
    intro n
    calc ∫⁻ z, ENNReal.ofReal ((UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice F s r n z) ^ 2) ∂μ
        ≤ ∫⁻ z, ENNReal.ofReal (((r - s) ^ 2 / (n : ℝ)) *
            ∑ k ∈ Finset.range n, (deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2) ∂μ :=
          lintegral_mono fun z =>
            ENNReal.ofReal_le_ofReal (UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice_sq_le F s r n z)
      _ = ENNReal.ofReal (∫ z, ((r - s) ^ 2 / (n : ℝ)) *
            ∑ k ∈ Finset.range n, (deriv (fun t => F t z) (s + (k : ℝ) * ((r - s) / n))) ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal (hBint n)
            (Eventually.of_forall fun z => by positivity)).symm
      _ ≤ ENNReal.ofReal ((r - s) ^ 2 * K) :=
          ENNReal.ofReal_le_ofReal
            (UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice_sq_integral_le F s ε K r hr hK hD n)
  have hlimpt : ∀ z, Tendsto
      (fun n => ENNReal.ofReal ((UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice F s r n z) ^ 2))
      atTop (𝓝 (ENNReal.ofReal ((F r z - F s z) ^ 2))) := fun z =>
    ENNReal.tendsto_ofReal
      ((UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice_tendsto F hC s r z).pow 2)
  have hF' : ∫⁻ z, ENNReal.ofReal ((F r z - F s z) ^ 2) ∂μ ≤ ENNReal.ofReal ((r - s) ^ 2 * K) := by
    have hmeas : ∀ n : ℕ, AEMeasurable
        (fun z => ENNReal.ofReal ((UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice F s r n z) ^ 2)) μ :=
      fun n => (((UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice_aesm F s ε r hr
        (fun t ht => (hD t ht).1.aestronglyMeasurable) n).aemeasurable).pow_const 2).ennreal_ofReal
    calc ∫⁻ z, ENNReal.ofReal ((F r z - F s z) ^ 2) ∂μ
        = ∫⁻ z, liminf (fun n => ENNReal.ofReal
            ((UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice F s r n z) ^ 2)) atTop ∂μ :=
          lintegral_congr fun z => ((hlimpt z).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ z, ENNReal.ofReal
            ((UnforcedLeray.Short.PartI.L2SqDeriv.riemannSlice F s r n z) ^ 2) ∂μ) atTop :=
          lintegral_liminf_le' hmeas
      _ ≤ ENNReal.ofReal ((r - s) ^ 2 * K) :=
          (Filter.liminf_le_liminf (Eventually.of_forall hfin)).trans (le_of_eq (liminf_const _))
  have hfin2 : ∫⁻ z, ENNReal.ofReal ((F r z - F s z) ^ 2) ∂μ < ⊤ :=
    lt_of_le_of_lt hF' ENNReal.ofReal_lt_top
  have hint : Integrable (fun z => (F r z - F s z) ^ 2) μ :=
    ⟨hDm.pow 2, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg _)).2 hfin2⟩
  have hmem : MemLp (fun z => F r z - F s z) 2 μ := (memLp_two_iff_integrable_sq hDm).2 hint
  refine ⟨hmem, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => sq_nonneg _) (hDm.pow 2)]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (sq_nonneg _) hK) hF'
