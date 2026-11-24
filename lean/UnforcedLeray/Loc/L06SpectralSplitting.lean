import UnforcedLeray.Loc.L06SpectralSplitting.Complexify
import UnforcedLeray.Loc.L06SpectralSplitting.Outer
import UnforcedLeray.Blueprint.Localization.Linear
import UnforcedLeray.Infra.RieszProjection
import UnforcedLeray.Infra.RealStructure
import UnforcedLeray.Infra.CompactDuhamel.Spectrum

/-!
# Step L6: the spectral splitting of the period map

`paper/main.tex`, lines 341-370 (`loc:eq:weight` and the Riesz splitting); blueprint units
B0716 (finite exterior spectrum), B1013 (choice of `β`), B1014 (Riesz splitting and rates).
This file proves `UnforcedLeray.Blueprint.SpectralSplittingStep`
(`Blueprint/Localization/Linear.lean`): a general lemma about one bounded operator `M` on a real
Hilbert space with the Calkin bound `‖Mⁿ - Kₙ‖ ≤ C e^{-n𝒯/4}`, `Kₙ` compact, `𝒯 > 0`,
`0 < σ < 1/4`.

Proof, following lines 348-370:
1. complexify (`L06SpectralSplitting/Complexify.lean`): `T = cx M` on `Cx X`;
2. for `r > e^{-𝒯/4}` the spectrum of `T` in `{|z| ≥ r}` is finite (line 350;
   `finite_outer_spectrum`, via the analytic Fredholm corollary `Infra/AnalyticFredholm`);
3. choose `β ∈ (σ, 2σ)` with the circle `|z| = e^{β𝒯}` in the resolvent set (`loc:eq:weight`;
   `CompactDuhamel.exists_weight_sphere_subset_resolventSet`);
4. `P₋ = rieszProj T e^{β𝒯}`, `P₊ = 1 - P₋`, `𝓜₊⁻¹P₊ = rieszOuterInv T e^{β𝒯}` and the rates
   `‖TⁿP₋‖ ≤ Cρⁿ`, `‖(𝓜₊⁻¹P₊)ⁿ‖ ≤ C R⁻ⁿ`, `ρ < e^{β𝒯} < R` (`Infra/RieszProjection`);
5. both commute with the conjugation (line 361, `Infra/RealStructure`), so they are the
   complexifications of real operators `P₊`, `N` with the same identities and bounds
   (`cx_rePart`, `norm_rePart_le`); `β₋ = log ρ / 𝒯`, `β₊ = log R / 𝒯`;
6. `P₊` has finite rank (line 360; `finiteDimensional_range_of_calkin`), and every operator
   commuting with `M` commutes with `P₊` (the Riesz integral commutes with the commutant).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Metric

namespace UnforcedLeray.Loc.L06

open UnforcedLeray.Blueprint UnforcedLeray.Infra.RieszProjection
  UnforcedLeray.Infra.RealStructure Cx

/-- **Step L6, `SpectralSplittingStep`** (`paper/main.tex`, lines 348-370, `loc:eq:weight`;
blueprint units B0716, B1013, B1014). For every bounded operator `M` on a real Hilbert space
with the Calkin bound of step L5, `𝒯 > 0` and `0 < σ < 1/4`, there are `σ < β < 2σ`, rates
`β₋ < β < β₊`, a finite-rank projection `P₊` commuting with `M` and with its commutant, and
`N = 𝓜₊⁻¹P₊` inverting `M` on `P₊X`, with `‖Mⁿ(1 - P₊)‖ ≤ C e^{β₋n𝒯}` and
`‖Nⁿ‖ ≤ C e^{-β₊n𝒯}`. -/
theorem spectralSplittingStep : SpectralSplittingStep := by
  intro E _ _ _ M period σ hp hσ _hσ4 hcal
  set T : Cx E →L[ℂ] Cx E := cx M with hT_def
  -- the finite exterior spectrum and the weight
  have hσp : 0 < σ * period := mul_pos hσ hp
  have hfin : (spectrum ℂ T ∩ {z : ℂ | Real.exp (σ * period) ≤ ‖z‖}).Finite :=
    finite_outer_spectrum hcal (Real.exp_lt_exp.2 (by linarith))
  obtain ⟨β, hβ, hsph⟩ :=
    UnforcedLeray.Infra.CompactDuhamel.exists_weight_sphere_subset_resolventSet T hp
      (by linarith : σ < 2 * σ) hfin
  have hβp : 0 < β * period := mul_pos (hσ.trans hβ.1) hp
  set r := Real.exp (β * period) with hr_def
  have hr : 0 < r := Real.exp_pos _
  have hr1 : 1 < r := by
    have := Real.add_one_le_exp (β * period)
    linarith
  obtain ⟨ρ, R, C, hρ, hρr, hrR, hC1, hrateP, hrateS⟩ := exists_rates hr hsph
  have hR0 : 0 < R := hr.trans hrR
  have hR1 : 1 < R := hr1.trans hrR
  set P := rieszProj T r with hP_def
  set S := rieszOuterInv T r with hS_def
  -- the complex identities
  have hidemC : IsIdempotentElem (1 - P) := (isIdempotentElem_rieszProj hr hsph).one_sub
  have hcommC : Commute T (1 - P) := (Commute.one_right T).sub_right (commute_self_rieszProj hr.le hsph)
  have hTS : T * S = 1 - P := mul_rieszOuterInv hr hsph
  have hST : S * T = 1 - P := rieszOuterInv_mul hr hsph
  have hSP : S * (1 - P) = S := rieszOuterInv_mul_one_sub hr hsph
  have hPS : (1 - P) * S = S := one_sub_mul_rieszOuterInv hr hsph
  -- real forms (line 361)
  have hJT : cxConj.CommutesWith T := cx_commutesWith M
  set Pp : E →L[ℝ] E := rePart (1 - P) with hPp_def
  set N : E →L[ℝ] E := rePart S with hN_def
  have hPp : cx Pp = 1 - P := cx_rePart (hJT.one_sub_rieszProj_commutesWith r)
  have hN : cx N = S := cx_rePart (hJT.rieszOuterInv_commutesWith r)
  have hidem : Pp * Pp = Pp := cx_injective (by rw [cx_mul, hPp]; exact hidemC.eq)
  have hcomm : M * Pp = Pp * M := cx_injective (by rw [cx_mul, cx_mul, hPp]; exact hcommC.eq)
  have hleft : N * (M * Pp) = Pp := cx_injective (by
    rw [cx_mul, cx_mul, hN, hPp, ← hT_def, ← mul_assoc, hST]; exact hidemC.eq)
  have hNpow : ∀ n : ℕ, ‖N ^ n‖ ≤ C * R⁻¹ ^ n := by
    intro n
    have h : cx (N ^ n) = S ^ n := by rw [cx_pow, hN]
    rw [← rePart_eq_of_cx_eq h]
    exact (norm_rePart_le _).trans (hrateS n)
  have hNb : ∃ C' : ℝ, ∀ n : ℕ, ‖N ^ n‖ ≤ C' := by
    refine ⟨C, fun n => (hNpow n).trans ?_⟩
    have h1 : R⁻¹ ^ n ≤ 1 := pow_le_one₀ (inv_nonneg.2 hR0.le) (inv_le_one_of_one_le₀ hR1.le)
    nlinarith [pow_nonneg (inv_nonneg.2 hR0.le) n]
  refine ⟨⟨β, Real.log ρ / period, Real.log R / period, Pp, N⟩, ?_⟩
  refine
    { weight_lower := hβ.1
      weight_upper := hβ.2
      rate_lower := ?_
      rate_upper := ?_
      idempotent := hidem
      commutes := hcomm
      finite_rank := finiteDimensional_range_of_calkin hp hcal hidem hcomm hleft hNb
      inverse_left := hleft
      inverse_right := cx_injective (by
        change cx (M * N) = cx Pp
        rw [cx_mul, hN, hPp, ← hT_def, hTS])
      inverse_range := cx_injective (by
        change cx (Pp * N) = cx N
        rw [cx_mul, hN, hPp, hPS])
      inverse_kernel := cx_injective (by
        change cx (N * Pp) = cx N
        rw [cx_mul, hN, hPp, hSP])
      stable_rate := ⟨C, fun n => ?_⟩
      unstable_rate := ⟨C, fun n => ?_⟩
      commutant := fun A hA => ?_ }
  · -- `β₋ = log ρ / 𝒯 < β`
    rw [div_lt_iff₀ hp, ← Real.log_exp (β * period)]
    exact Real.log_lt_log hρ hρr
  · -- `β < β₊ = log R / 𝒯`
    rw [lt_div_iff₀ hp, ← Real.log_exp (β * period)]
    exact Real.log_lt_log hr hrR
  · -- `‖Mⁿ P₋‖ ≤ C e^{β₋ n 𝒯}`
    have h : cx (M ^ n * (1 - Pp)) = T ^ n * P := by
      rw [cx_mul, cx_pow, cx_sub, cx_one, hPp, sub_sub_cancel]
    have hexp : Real.exp (Real.log ρ / period * ((n : ℝ) * period)) = ρ ^ n := by
      have : Real.log ρ / period * ((n : ℝ) * period) = n * Real.log ρ := by
        field_simp
      rw [this, Real.exp_nat_mul, Real.exp_log hρ]
    rw [← rePart_eq_of_cx_eq h, hexp]
    exact (norm_rePart_le _).trans (hrateP n)
  · -- `‖(𝓜₊⁻¹P₊)ⁿ‖ ≤ C e^{-β₊ n 𝒯}`
    have hexp : Real.exp (-(Real.log R / period * ((n : ℝ) * period))) = R⁻¹ ^ n := by
      have : -(Real.log R / period * ((n : ℝ) * period)) = n * Real.log R⁻¹ := by
        rw [Real.log_inv]
        field_simp
      rw [this, Real.exp_nat_mul, Real.exp_log (inv_pos.2 hR0)]
    rw [hexp]
    exact hNpow n
  · -- the commutant of `M` commutes with `P₊`
    have hA' : Commute (cx A) T := by
      have h := congrArg cx hA
      change cx (A * M) = cx (M * A) at h
      rw [cx_mul, cx_mul] at h
      exact h
    have hAP : Commute (cx A) (1 - P) :=
      (Commute.one_right _).sub_right (commute_rieszProj_of_commute hA' r)
    refine cx_injective ?_
    change cx (A * Pp) = cx (Pp * A)
    rw [cx_mul, cx_mul, hPp]
    exact hAP.eq

/-- info: 'UnforcedLeray.Loc.L06.spectralSplittingStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spectralSplittingStep

end UnforcedLeray.Loc.L06
