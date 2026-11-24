import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramUnfold.Fubini

/-!
# Part III-a, task `PartIII-a:T21/c1/b/1`: unfolding the Gram entry (SP 2894-2895)

`G_ij = ∫_cell P_d λ_i · P_d e_j = Σ_k ∫_{ℝ²} λ_i(y) e_j(y₁ + kd, y₂) dy`: the periodic factor
`P_d e_j` is moved under the sum, the cell integral of `P_d(λ_i · P_d e_j)` is the planar integral
(`integral_bcell_perSum`), and the series of planar integrals is interchanged with the integral
(`integral_tsum`, justified by the uniform cross bound `gramCross_int`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.IIIa

/-- **Leaf 1** (SP 2894-2895): the Gram entry is the summable series of planar cross integrals. -/
theorem perGramUnfold (κ : PlanarFrameKernels) : PerGramUnfold κ := by
  intro d hd i j
  obtain ⟨K, hK0, hK⟩ := gramCross_int κ
  set Fk : ℤ → ℝ × ℝ → ℂ := fun k y => κ.lamP i y * κ.e j (y.1 + (k : ℝ) * d, y.2) with hFk
  have hint : ∀ k, Integrable (Fk k) := fun k => (hK i j ((k : ℝ) * d)).1
  have hnorm : ∀ k, ∫ y, ‖Fk k y‖ ≤ K / (1 + |(k : ℝ) * d|) ^ 2 := fun k =>
    (hK i j ((k : ℝ) * d)).2
  have hb := summable_cross_bound (K := K) hd
  have hsumI : Summable (fun k => ∫ y, ‖Fk k y‖) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _) hnorm hb
  have hsum : Summable (fun k : ℤ => gramTerm κ d i j k) :=
    hsumI.of_norm_bounded fun k => norm_integral_le_integral_norm _
  have hPeSum : ∀ y : ℝ × ℝ, Summable (fun n : ℤ => κ.e j (y.1 + n * d, y.2)) := fun y =>
    (summable_e_shift κ hd j y).of_norm
  have hPeMeas : Measurable (perE κ d j) := measurable_perSum (κ.e_cont j) hPeSum
  have hFsum : ∀ y, κ.lamP i y * perE κ d j y = ∑' k : ℤ, Fk k y := by
    intro y
    simp only [perE, perSum, hFk]
    exact tsum_mul_left.symm
  have hlin : ∀ k, ∫⁻ y, ‖Fk k y‖ₑ = ENNReal.ofReal (∫ y, ‖Fk k y‖) := fun k =>
    (ofReal_integral_norm_eq_lintegral_enorm (hint k)).symm
  have hsumL : ∑' k, ∫⁻ y, ‖Fk k y‖ₑ ≠ ⊤ := by
    simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun y => norm_nonneg _) hsumI]
    exact ENNReal.ofReal_ne_top
  have hmeasF : ∀ k, AEStronglyMeasurable (Fk k) volume := fun k => (hint k).1
  have hInt : Integrable (fun y => ∑' k, Fk k y) := by
    refine ⟨?_, ?_⟩
    · have : (fun y => ∑' k, Fk k y) = fun y => κ.lamP i y * perE κ d j y :=
        funext fun y => (hFsum y).symm
      rw [this]
      exact ((κ.lamP_cont i).measurable.mul hPeMeas).aestronglyMeasurable
    · calc ∫⁻ y, ‖∑' k, Fk k y‖ₑ ≤ ∫⁻ y, ∑' k, ‖Fk k y‖ₑ :=
            lintegral_mono fun y => enorm_tsum_le_tsum_enorm
        _ = ∑' k, ∫⁻ y, ‖Fk k y‖ₑ := lintegral_tsum (fun k => (hmeasF k).enorm)
        _ < ⊤ := lt_top_iff_ne_top.2 hsumL
  have hcell : perGram κ d i j = ∫ y, ∑' k, Fk k y := by
    unfold perGram
    have h1 : ∀ x : ℝ × ℝ,
        perLam0 κ d i x * perE κ d j x = perSum d (fun y => ∑' k, Fk k y) x := by
      intro x
      simp only [perLam0, perSum]
      rw [← tsum_mul_right]
      refine tsum_congr fun n => ?_
      rw [← hFsum]
      congr 1
      exact (perSum_int_period d (κ.e j) n x).symm
    rw [← integral_bcell_perSum hInt hd]
    exact setIntegral_congr_fun (measurableSet_Ico.prod MeasurableSet.univ) fun x _ => h1 x
  refine ⟨hsum, ?_⟩
  rw [hcell, integral_tsum hmeasF hsumL]
  rfl

end UnforcedLeray.Short.IIIa
