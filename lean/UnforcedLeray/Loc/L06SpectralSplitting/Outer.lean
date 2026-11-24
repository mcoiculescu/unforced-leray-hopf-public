import UnforcedLeray.Loc.L06SpectralSplitting.Complexify
import UnforcedLeray.Blueprint.Localization.Linear
import UnforcedLeray.Infra.AnalyticFredholm
import UnforcedLeray.Infra.FiniteRankApprox
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The exterior spectrum of a real operator with a Calkin bound

`paper/main.tex`, lines 341-351 (blueprint unit B0716): "the essential spectral radius of `𝓜`
is at most `e^{-𝒯/4}` … finitely many spectral points outside each circle of radius larger than
`e^{-𝒯/4}`, all of finite algebraic multiplicity". The hypothesis is the real, Calkin-free form
`CalkinBound M 𝒯` of step L5 (`Blueprint/Localization/Linear.lean`): `Mⁿ` lies within
`C e^{-n𝒯/4}` of a compact operator.

## Main results
* `isApproximable_cx`: the complexification of a compact operator on a real Hilbert space is a
  norm limit of finite-rank complex operators (`Infra/FiniteRankApprox`);
* `finite_outer_spectrum`: for `r > e^{-𝒯/4}` the spectrum of the complexified operator
  `cx M` meets `{|z| ≥ r}` in a finite set. Proof: `(cx M)ⁿ = cx(Mⁿ - K) + cx K` with
  `‖cx(Mⁿ - K)‖ < rⁿ` for large `n`; the analytic Fredholm corollary
  `finite_spectrum_add_inter` (`Infra/AnalyticFredholm`) and `zⁿ ∈ spec((cx M)ⁿ)`;
* `finiteDimensional_range_of_isCompactOperator`: a compact idempotent has finite rank;
* `finiteDimensional_range_of_calkin`: an idempotent `P₊` commuting with `M`, on whose range `M`
  has a left inverse `N` with bounded powers, has finite rank. Proof:
  `P₊ = Nⁿ Mⁿ P₊ = Nⁿ(Mⁿ - K)P₊ + NⁿKP₊` and `‖Nⁿ(Mⁿ - K)‖ < 1` for large `n`, so
  `P₊ = (1 - Nⁿ(Mⁿ - K))⁻¹ NⁿKP₊` is compact. This is the "finite algebraic multiplicity" of
  line 351 in the form step L6 needs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter
open scoped NNReal ENNReal

namespace UnforcedLeray.Loc.L06

open UnforcedLeray.Infra.AnalyticFredholm UnforcedLeray.Blueprint Cx

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The complexification of a compact operator on a real Hilbert space is approximable by
complex finite-rank operators. -/
theorem isApproximable_cx {K : E →L[ℝ] E} (hK : IsCompactOperator K) :
    IsApproximable (cx K) := by
  rw [isApproximable_iff]
  intro ε hε
  obtain ⟨F, hF, hKF⟩ := UnforcedLeray.Infra.FiniteRankApprox.exists_finiteRank_norm_sub_lt hK hε
  refine ⟨cx F, isFiniteRank_cx hF, ?_⟩
  rw [← cx_sub]
  exact (norm_cx_le _).trans_lt hKF

/-- The spectral radius of an operator on `Cx E` is at most its norm (no `NormOneClass`
needed: `‖1‖ ≤ 1`). -/
theorem spectralRadius_le_nnnorm_cx [CompleteSpace E] (T : Cx E →L[ℂ] Cx E) :
    spectralRadius ℂ T ≤ ‖T‖₊ := by
  refine iSup₂_le fun k hk => ?_
  have h := spectrum.subset_closedBall_norm_mul T hk
  rw [Metric.mem_closedBall, dist_zero_right] at h
  have h1 : ‖(1 : Cx E →L[ℂ] Cx E)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ (Cx E)‖ ≤ 1)
  have hk' : ‖k‖ ≤ ‖T‖ :=
    h.trans (by nlinarith [norm_nonneg T, norm_nonneg (1 : Cx E →L[ℂ] Cx E)])
  exact ENNReal.coe_le_coe.2 (by rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]; exact hk')

/-- **Finite exterior spectrum** (`paper/main.tex`, lines 348-351; unit B0716). If `Mⁿ` is within
`C e^{-n𝒯/4}` of a compact operator for every `n`, then for every `r > e^{-𝒯/4}` the spectrum of
the complexification `cx M` has finitely many points with `|z| ≥ r`. -/
theorem finite_outer_spectrum [CompleteSpace E] {M : E →L[ℝ] E} {period : ℝ}
    (hM : CalkinBound M period) {r : ℝ} (hr : Real.exp (-(period / 4)) < r) :
    (spectrum ℂ (cx M) ∩ {z : ℂ | r ≤ ‖z‖}).Finite := by
  obtain ⟨C, hC⟩ := hM
  have hr0 : 0 < r := (Real.exp_pos _).trans hr
  set a := r * Real.exp (period / 4) with ha_def
  have ha : 1 < a := by
    have h1 : Real.exp (-(period / 4)) * Real.exp (period / 4) = 1 := by
      rw [← Real.exp_add]; simp
    calc (1 : ℝ) = Real.exp (-(period / 4)) * Real.exp (period / 4) := h1.symm
      _ < r * Real.exp (period / 4) := mul_lt_mul_of_pos_right hr (Real.exp_pos _)
  obtain ⟨N, hN⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt ha).eventually_gt_atTop C).exists_forall_of_atTop
  set n := N + 1 with hn_def
  have hn : 0 < n := Nat.succ_pos N
  have hCn : C < a ^ n := hN n (Nat.le_succ N)
  obtain ⟨K, hK, hMK⟩ := hC n
  -- `rⁿ = aⁿ e^{-n𝒯/4}`
  have hrn : a ^ n * Real.exp (-((n : ℝ) * period / 4)) = r ^ n := by
    rw [ha_def, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    have : (n : ℝ) * (period / 4) + -((n : ℝ) * period / 4) = 0 := by ring
    rw [this, Real.exp_zero, mul_one]
  have hsmall : ‖cx (M ^ n - K)‖ < r ^ n := by
    calc ‖cx (M ^ n - K)‖ ≤ ‖M ^ n - K‖ := norm_cx_le _
      _ ≤ C * Real.exp (-((n : ℝ) * period / 4)) := hMK
      _ < a ^ n * Real.exp (-((n : ℝ) * period / 4)) :=
          mul_lt_mul_of_pos_right hCn (Real.exp_pos _)
      _ = r ^ n := hrn
  set x := ‖cx (M ^ n - K)‖ with hx_def
  set q : ℝ≥0 := ((x + r ^ n) / 2).toNNReal with hq_def
  have hq : (q : ℝ) = (x + r ^ n) / 2 := Real.coe_toNNReal _ (by positivity)
  have hA : spectralRadius ℂ (cx (M ^ n - K)) < q := by
    refine (spectralRadius_le_nnnorm_cx _).trans_lt (ENNReal.coe_lt_coe.2 ?_)
    rw [← NNReal.coe_lt_coe, coe_nnnorm, hq]
    linarith
  have hqr : (q : ℝ) < r ^ n := by rw [hq]; linarith
  have hfin := finite_spectrum_add_inter hA (isApproximable_cx hK) hqr
  have hsum : cx (M ^ n - K) + cx K = cx M ^ n := by rw [← cx_add, sub_add_cancel, cx_pow]
  rw [hsum] at hfin
  refine (hfin.biUnion fun w _ => (Polynomial.nthRoots n w).toFinset.finite_toSet).subset ?_
  rintro z ⟨hz, hzr⟩
  refine mem_iUnion₂.2 ⟨z ^ n, ⟨spectrum.pow_mem_pow (cx M) n hz, ?_⟩, ?_⟩
  · show r ^ n ≤ ‖z ^ n‖
    rw [norm_pow]
    exact pow_le_pow_left₀ hr0.le hzr n
  · rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]

/-- **A compact idempotent has finite rank** (Riesz: the closed unit ball of its range is
compact). -/
theorem finiteDimensional_range_of_isCompactOperator {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {P : F →L[ℝ] F} (hP : IsCompactOperator P) (hPP : P * P = P) :
    FiniteDimensional ℝ (LinearMap.range (P : F →ₗ[ℝ] F)) := by
  set V := LinearMap.range (P : F →ₗ[ℝ] F)
  have hfix : ∀ x : F, x ∈ V ↔ P x = x := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      change (P * P) y = P y
      rw [hPP]
    · intro h
      exact ⟨x, h⟩
  refine FiniteDimensional.of_isCompact_closedBall₀ ℝ zero_lt_one ?_
  rw [Topology.IsInducing.subtypeVal.isCompact_iff]
  have hc : IsCompact (Metric.closedBall (0 : F) 1 ∩ {x | P x = x}) := by
    refine (IsCompactOperator.isCompact_closure_image_closedBall (f := (P : F →ₗ[ℝ] F)) hP 1)
      |>.of_isClosed_subset ?_ ?_
    · exact Metric.isClosed_closedBall.inter (isClosed_eq P.continuous continuous_id)
    · rintro x ⟨hx, hPx⟩
      exact subset_closure ⟨x, hx, hPx⟩
  convert hc using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, (hfix y).1 y.2⟩
    simpa using hy
  · rintro ⟨hx, hPx⟩
    refine ⟨⟨x, (hfix x).2 hPx⟩, ?_, rfl⟩
    simpa using hx

/-- **Finite rank of the exterior projection** (`paper/main.tex`, lines 349-351 and 359-360,
"`P₊ = I - P₋`, the finite-dimensional exterior projection"; units B0716, B1014). Let `P₊` be an
idempotent commuting with `M`, and `N` a left inverse of `M` on `P₊X` (`N M P₊ = P₊`) with
bounded powers. If `M` satisfies the Calkin bound with `𝒯 > 0`, then `P₊` has finite rank. -/
theorem finiteDimensional_range_of_calkin {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {M Pp N : F →L[ℝ] F} {period : ℝ} (hp : 0 < period)
    (hM : CalkinBound M period) (hidem : Pp * Pp = Pp) (hcomm : M * Pp = Pp * M)
    (hleft : N * (M * Pp) = Pp) (hNb : ∃ C : ℝ, ∀ n : ℕ, ‖N ^ n‖ ≤ C) :
    FiniteDimensional ℝ (LinearMap.range (Pp : F →ₗ[ℝ] F)) := by
  -- `Nⁿ Mⁿ P₊ = P₊`
  have hc : Commute M Pp := hcomm
  have hMP : ∀ n : ℕ, Pp * (M ^ n * Pp) = M ^ n * Pp := by
    intro n
    rw [← mul_assoc, ← (hc.pow_left n).eq, mul_assoc, hidem]
  have hstep : ∀ n : ℕ, N * (M ^ (n + 1) * Pp) = M ^ n * Pp := by
    intro n
    calc N * (M ^ (n + 1) * Pp) = N * (M * (Pp * (M ^ n * Pp))) := by
          rw [hMP, pow_succ', mul_assoc]
      _ = (N * (M * Pp)) * (M ^ n * Pp) := by simp only [mul_assoc]
      _ = M ^ n * Pp := by rw [hleft, hMP]
  have hpow : ∀ n : ℕ, N ^ n * (M ^ n * Pp) = Pp := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, hstep, ih]
  -- choose `n` with `‖Nⁿ (Mⁿ - K)‖ < 1`
  obtain ⟨C, hC⟩ := hM
  obtain ⟨CN, hCN⟩ := hNb
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0)
  set L := CN * max C 0 with hL
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * L / period)
  set t := (n : ℝ) * period / 4 with ht
  have htL : L < t := by
    rw [div_lt_iff₀ hp] at hn
    rw [ht]
    linarith
  have hLt : L * Real.exp (-t) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos t)]
    linarith [Real.add_one_le_exp t]
  obtain ⟨K, hK, hMK⟩ := hC n
  set D := N ^ n * (M ^ n - K) with hD_def
  have hD : ‖D‖ < 1 := by
    calc ‖D‖ ≤ ‖N ^ n‖ * ‖M ^ n - K‖ := norm_mul_le _ _
      _ ≤ CN * (max C 0 * Real.exp (-t)) := by
          refine mul_le_mul (hCN n) (hMK.trans ?_) (norm_nonneg _) hCN0
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ = L * Real.exp (-t) := by rw [hL, mul_assoc]
      _ < 1 := hLt
  have hres : (1 - D) * Pp = N ^ n * (K * Pp) := by
    have h := hpow n
    simp only [hD_def, sub_mul, mul_sub, one_mul, mul_assoc]
    rw [h]
    abel
  set u := Units.oneSub D hD
  have hPeq : Pp = ↑u⁻¹ * (N ^ n * (K * Pp)) := by
    calc Pp = (↑u⁻¹ * ↑u) * Pp := by rw [Units.inv_mul, one_mul]
      _ = ↑u⁻¹ * ((1 - D) * Pp) := by rw [mul_assoc, Units.val_oneSub]
      _ = ↑u⁻¹ * (N ^ n * (K * Pp)) := by rw [hres]
  have hcpt : IsCompactOperator (Pp : F → F) := by
    rw [hPeq]
    exact ((hK.comp_clm Pp).clm_comp _).clm_comp _
  exact finiteDimensional_range_of_isCompactOperator hcpt hidem

end UnforcedLeray.Loc.L06
