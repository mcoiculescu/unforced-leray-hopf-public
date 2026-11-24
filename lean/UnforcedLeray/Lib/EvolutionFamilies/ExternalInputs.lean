import UnforcedLeray.Infra.WeaklyNullCompact
import UnforcedLeray.Infra.CompactDuhamel
import UnforcedLeray.Infra.PeriodicDichotomy
import UnforcedLeray.Infra.RealStructure

/-!
# External inputs E5–E9: the localisation spectral package, reconciled with the drafts


targets E5–E9, under decision D11 of `scoping/README.md` §3: the statements of E5–E9 are
derived from the drafted modules `Infra/WeaklyNullCompact`, `Infra/CompactDuhamel`,
`Infra/AnalyticFredholm`, `Infra/FiniteRankApprox`, `Infra/RieszProjection` and
`Infra/RealStructure`, which are not rewritten. Only E6 (compactness of a Duhamel remainder with
general operator families, in place of the `VolterraData` instance of `CompactDuhamel/Strip`)
needed a new proof.

Manuscript: `paper/main.tex`, lines 331-370 (Section `sec:st18-329`); blueprint units
B0714(d) (E6), B0716 (E7, E8), B1014 (E9).

* E5 `isCompactOperator_of_forall_weaklyNull`, `tendsto_norm_of_isCompactOperator_of_weaklyNull`
  (lines 338-340);
* E6 `isCompactOperator_of_integral_compact` (B0714(d), lines 332-340);
* E7 `spectralRadius_le_of_norm_pow_le` (BX1, lines 340-345);
* E8 `finite_spectrum_outside_of_compact_perturbation`, `exists_weight_circle` (B0716 and
  `loc:eq:weight`, lines 345-357);
* E9 `monodromy_dichotomy`, `CommutesWith.rieszProj_monodromy` (B1014, lines 359-370).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace NNReal ENNReal

namespace UnforcedLeray.ExternalInputs

open UnforcedLeray.Infra

/-! ### E5. The weakly-null criterion -/

section E5

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **E5, weakly-null criterion** (`paper/main.tex`, lines 338-340; ExternalInputs E5).
On a Hilbert space `E`, a bounded operator that maps weakly null sequences to norm null
sequences is compact. Restatement of `Infra.WeaklyNullCompact.isCompactOperator_of_forall_weaklyNull`. -/
theorem isCompactOperator_of_forall_weaklyNull [CompleteSpace E] (T : E →L[𝕜] F)
    (hT : ∀ x : ℕ → E, (∀ y : E, Tendsto (fun n => ⟪y, x n⟫_𝕜) atTop (𝓝 0)) →
      Tendsto (fun n => ‖T (x n)‖) atTop (𝓝 0)) : IsCompactOperator T :=
  WeaklyNullCompact.isCompactOperator_of_forall_weaklyNull T hT

/-- **E5, converse** (ExternalInputs E5): a compact operator maps weakly null sequences to norm
null sequences. Restatement of
`Infra.WeaklyNullCompact.tendsto_norm_of_isCompactOperator_of_weaklyNull`. -/
theorem tendsto_norm_of_isCompactOperator_of_weaklyNull [CompleteSpace E] {T : E →L[𝕜] F}
    (hT : IsCompactOperator T) {x : ℕ → E}
    (hx : ∀ y : E, Tendsto (fun n => ⟪y, x n⟫_𝕜) atTop (𝓝 0)) :
    Tendsto (fun n => ‖T (x n)‖) atTop (𝓝 0) :=
  WeaklyNullCompact.tendsto_norm_of_isCompactOperator_of_weaklyNull hT hx

end E5

/-! ### E6. Compactness of a Duhamel remainder -/

section E6

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- A bounded operator maps weakly null sequences to weakly null sequences. -/
theorem weaklyNull_map (T : X →L[ℂ] X) {x : ℕ → X}
    (hx : ∀ y : X, Tendsto (fun n => ⟪y, x n⟫_ℂ) atTop (𝓝 0)) :
    ∀ y : X, Tendsto (fun n => ⟪y, T (x n)⟫_ℂ) atTop (𝓝 0) := by
  have h := (WeaklyNullCompact.weakTendsto_zero_iff.mpr hx).map T
  rw [map_zero] at h
  exact WeaklyNullCompact.weakTendsto_zero_iff.mp h

/-- **E6, compactness of a Duhamel remainder** (`paper/main.tex`, lines 332-340, B0714(d);
ExternalInputs E6). Let `X` be a complex Hilbert space, `s < t`, `A r` compact for
`s < r < t` with `‖A r‖ ≤ C (t - r)^{-1/2}`, `‖U r‖ ≤ M` on `[s,t]`, and the integrands
`r ↦ A r (U r x)` strongly measurable. An operator `R` with
`R x = ∫ r in s..t, A r (U r x)` for all `x` is compact.

Proof (the manuscript's): for a weakly null sequence `x n`, `U r (x n)` is weakly null, so
`‖A r (U r (x n))‖ → 0` for `s < r < t`; the integrands are dominated by the integrable
`C (t - r)^{-1/2} M sup ‖x n‖`; dominated convergence and E5. This generalises
`Infra.CompactDuhamel.isCompactOperator_stripEvolution_sub` (whose instance is
`A r = S (τ - r) ∘ B r`, `U r = E(r,s)`). -/
theorem isCompactOperator_of_integral_compact {s t M C : ℝ} (hst : s < t)
    (A U : ℝ → X →L[ℂ] X) (hA : ∀ r ∈ Ioo s t, IsCompactOperator (A r))
    (hAb : ∀ r ∈ Ioo s t, ‖A r‖ ≤ C * (t - r) ^ (-(1 / 2 : ℝ)))
    (hUb : ∀ r ∈ Icc s t, ‖U r‖ ≤ M)
    (hmeas : ∀ x, AEStronglyMeasurable (fun r => A r (U r x)) (volume.restrict (Ioc s t)))
    (R : X →L[ℂ] X) (hR : ∀ x, R x = ∫ r in s..t, A r (U r x)) : IsCompactOperator R := by
  refine isCompactOperator_of_forall_weaklyNull R fun x hx => ?_
  obtain ⟨K, hK⟩ := WeaklyNullCompact.exists_norm_le_of_weaklyNull (𝕜 := ℂ) hx
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hlim : Tendsto (fun n => ∫ r in s..t, A r (U r (x n))) atTop
      (𝓝 (∫ _ in s..t, (0 : X))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun r => C * (t - r) ^ (-(1 / 2 : ℝ)) * (M * K)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      rw [uIoc_of_le hst.le]
      exact hmeas (x n)
    · refine Eventually.of_forall fun n => ?_
      filter_upwards [VolterraEvolution.ae_ne_real t] with r hrt hr
      rw [uIoc_of_le hst.le] at hr
      have hr' : r ∈ Ioo s t := ⟨hr.1, lt_of_le_of_ne hr.2 hrt⟩
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hUb r ⟨hr.1.le, hr.2⟩)
      calc ‖A r (U r (x n))‖ ≤ ‖A r‖ * ‖U r (x n)‖ := (A r).le_opNorm _
        _ ≤ C * (t - r) ^ (-(1 / 2 : ℝ)) * (M * K) := by
          refine mul_le_mul (hAb r hr') ?_ (norm_nonneg _)
            ((norm_nonneg _).trans (hAb r hr'))
          calc ‖U r (x n)‖ ≤ ‖U r‖ * ‖x n‖ := (U r).le_opNorm _
            _ ≤ M * K := mul_le_mul (hUb r ⟨hr.1.le, hr.2⟩) (hK n) (norm_nonneg _) hM0
    · exact ((VolterraEvolution.intervalIntegrable_kernel t s t).const_mul C).mul_const _
    · filter_upwards [VolterraEvolution.ae_ne_real t] with r hrt hr
      rw [uIoc_of_le hst.le] at hr
      have hr' : r ∈ Ioo s t := ⟨hr.1, lt_of_le_of_ne hr.2 hrt⟩
      have h := tendsto_norm_of_isCompactOperator_of_weaklyNull (hA r hr')
        (weaklyNull_map (U r) hx)
      rw [← tendsto_zero_iff_norm_tendsto_zero] at h
      exact h
  simp only [intervalIntegral.integral_zero] at hlim
  have h2 := tendsto_zero_iff_norm_tendsto_zero.mp hlim
  refine h2.congr fun n => ?_
  rw [hR]

end E6

/-! ### E7. A spectral-radius bound from power decay -/

section E7

variable {𝒜 : Type*} [NormedRing 𝒜] [NormedAlgebra ℂ 𝒜] [CompleteSpace 𝒜]

/-- **E7, spectral radius from power decay** (BX1, `paper/main.tex`, lines 340-345; ExternalInputs
E7). In a complex Banach algebra, `‖a ^ n‖ ≤ C q ^ n` for all `n` (`q ≥ 0`) gives
`spectralRadius ℂ a ≤ q`. Derived from
`Infra.RieszProjection.spectrum_subset_closedBall_of_norm_pow_le`; no sign condition on `C` and
no `NormOneClass` are needed. -/
theorem spectralRadius_le_of_norm_pow_le (a : 𝒜) {C q : ℝ} (hq : 0 ≤ q)
    (h : ∀ n : ℕ, ‖a ^ n‖ ≤ C * q ^ n) : spectralRadius ℂ a ≤ ENNReal.ofReal q := by
  have hsub := RieszProjection.spectrum_subset_closedBall_of_norm_pow_le a hq h
  refine iSup₂_le fun k hk => ?_
  have hk' : ‖k‖ ≤ q := mem_closedBall_zero_iff.mp (hsub hk)
  exact ENNReal.coe_le_coe.mpr ((Real.le_toNNReal_iff_coe_le hq).mpr hk')

end E7

/-! ### E8. Finite exterior spectrum and the circle choice -/

section E8

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- **E8, finite exterior spectrum of a compact perturbation** (B0716, `paper/main.tex`,
lines 345-351; ExternalInputs E8). On a complex Hilbert space, if `K` is compact and
`spectralRadius ℂ S < r`, then `spectrum (S + K)` has finitely many points with `|ξ| ≥ r`.
Derived from `Infra.FiniteRankApprox.mem_approximable_of_isCompactOperator` and
`Infra.AnalyticFredholm.finite_spectrum_add_inter_of_spectralRadius_lt`. -/
theorem finite_spectrum_outside_of_compact_perturbation (S K : X →L[ℂ] X)
    (hK : IsCompactOperator K) {r : ℝ} (hr : spectralRadius ℂ S < ENNReal.ofReal r) :
    (spectrum ℂ (S + K) ∩ {ξ : ℂ | r ≤ ‖ξ‖}).Finite := by
  have hr0 : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hr)
  have happrox : AnalyticFredholm.IsApproximable K :=
    AnalyticFredholm.isApproximable_iff.mpr fun ε hε =>
      FiniteRankApprox.mem_approximable_iff.mp
        (FiniteRankApprox.mem_approximable_of_isCompactOperator hK) ε hε
  have hρ : spectralRadius ℂ S < (r.toNNReal : ℝ≥0∞) := hr
  have h := AnalyticFredholm.finite_spectrum_add_inter_of_spectralRadius_lt happrox hρ
  rwa [Real.coe_toNNReal r hr0.le] at h

omit [CompleteSpace X] in
/-- **E8, choice of the circle** (`loc:eq:weight`, `paper/main.tex`, lines 352-357; ExternalInputs
E8). If `M` has finitely many spectral points with `|ξ| ≥ e^{σ𝒯}` (`σ, 𝒯 > 0`), some
`β ∈ (σ, 2σ)` has the circle `|ξ| = e^{β𝒯}` in the resolvent set. Derived from
`Infra.CompactDuhamel.exists_weight_sphere_subset_resolventSet`. -/
theorem exists_weight_circle (M : X →L[ℂ] X) {σ 𝒯 : ℝ} (hσ : 0 < σ) (h𝒯 : 0 < 𝒯)
    (hfin : (spectrum ℂ M ∩ {ξ : ℂ | Real.exp (σ * 𝒯) ≤ ‖ξ‖}).Finite) :
    ∃ β, σ < β ∧ β < 2 * σ ∧ sphere (0 : ℂ) (Real.exp (β * 𝒯)) ⊆ resolventSet ℂ M := by
  obtain ⟨β, hβ, hsph⟩ := CompactDuhamel.exists_weight_sphere_subset_resolventSet M h𝒯
    (by linarith : σ < 2 * σ) hfin
  exact ⟨β, hβ.1, hβ.2, hsph⟩

end E8

/-! ### E9. Monodromy dichotomy with rates -/

section E9

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **E9, monodromy dichotomy with rates** (B1014, `paper/main.tex`, lines 359-370;
ExternalInputs E9). Let `M` be a bounded operator on a complex Banach space and let the circle
`|ξ| = e^{β𝒯}` (`𝒯 > 0`) lie in the resolvent set. Then the Riesz projection
`P₋ = rieszProj M e^{β𝒯}` is an idempotent commuting with `M`, and there are `β₋ < β < β₊` and
`C` with `‖M ^ n P₋‖ ≤ C e^{β₋ n 𝒯}`, `M` invertible on `ran (1 - P₋)` and
`‖(M|_{ran (1-P₋)})^{-n}‖ ≤ C e^{-β₊ n 𝒯}`. The projection is named explicitly. Derived from
`Infra.RieszProjection.riesz_projection` (the `Ring.inverse` there is of a unit, by the
`IsUnit` conjunct). -/
theorem monodromy_dichotomy (M : X →L[ℂ] X) {β 𝒯 : ℝ} (h𝒯 : 0 < 𝒯)
    (hcirc : sphere (0 : ℂ) (Real.exp (β * 𝒯)) ⊆ resolventSet ℂ M) :
    ∃ (Pm : X →L[ℂ] X) (βm βp C : ℝ),
      Pm = RieszProjection.rieszProj M (Real.exp (β * 𝒯)) ∧
      IsIdempotentElem Pm ∧ Commute M Pm ∧ βm < β ∧ β < βp ∧
      (∀ n : ℕ, ‖M ^ n * Pm‖ ≤ C * Real.exp (βm * n * 𝒯)) ∧
      IsUnit (RieszProjection.outerPart M (Real.exp (β * 𝒯))) ∧
      (∀ n : ℕ, ‖Ring.inverse (RieszProjection.outerPart M (Real.exp (β * 𝒯))) ^ n‖
          ≤ C * Real.exp (-(βp * n * 𝒯))) := by
  have hr : 0 < Real.exp (β * 𝒯) := Real.exp_pos _
  obtain ⟨hidem, hcomm, -, -, -, hunit, ⟨ρ, R, C, hρ, hρr, hR, -, h₁, -, h₂⟩, -, -⟩ :=
    RieszProjection.riesz_projection hr hcirc
  have hR0 : 0 < R := hr.trans hR
  refine ⟨_, Real.log ρ / 𝒯, Real.log R / 𝒯, C, rfl, hidem, hcomm, ?_, ?_, ?_, hunit, ?_⟩
  · rw [div_lt_iff₀ h𝒯, ← Real.log_exp (β * 𝒯)]
    exact Real.log_lt_log hρ hρr
  · rw [lt_div_iff₀ h𝒯, ← Real.log_exp (β * 𝒯)]
    exact Real.log_lt_log hr hR
  · intro n
    refine (h₁ n).trans_eq ?_
    have he : Real.log ρ / 𝒯 * n * 𝒯 = n * Real.log ρ := by field_simp
    rw [he, Real.exp_nat_mul, Real.exp_log hρ]
  · intro n
    refine (h₂ n).trans_eq ?_
    have he : -(Real.log R / 𝒯 * n * 𝒯) = n * (-Real.log R) := by field_simp
    rw [he, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hR0]

omit [CompleteSpace X] in
/-- **E9, reality of the splitting** (B1014, line 362, "both preserve real fields";
ExternalInputs E9). If the conjugation `J` commutes with the monodromy `M`, it commutes with
the Riesz projection and with `1 - P₋`. From `Infra.RealStructure`. -/
theorem CommutesWith.rieszProj_monodromy {J : RealStructure.Conjugation X} {M : X →L[ℂ] X}
    (hJ : J.CommutesWith M) (r : ℝ) :
    J.CommutesWith (RieszProjection.rieszProj M r) ∧
      J.CommutesWith (1 - RieszProjection.rieszProj M r) :=
  ⟨hJ.rieszProj_commutesWith r, hJ.one_sub_rieszProj_commutesWith r⟩

end E9

end UnforcedLeray.ExternalInputs
