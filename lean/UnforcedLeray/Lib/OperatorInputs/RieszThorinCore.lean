import UnforcedLeray.Lib.OperatorInputs.StepFunctions
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Riesz–Thorin: the three-lines step on step functions (helpers for ExternalInputs E10)


Grafakos, *Classical Fourier Analysis*, Thm. 1.3.4; blueprint units B0529, B0534, B0544
(`paper/main.tex` 3827–3856, 5251–5262, 5636–5646).

Let `1 ≤ p₀, p₁ < ∞`, `θ ∈ [0, 1]` and `1/p = (1-θ)/p₀ + θ/p₁ < 1`. Let `T₀, T₁, T` be bounded
operators on `L^{p₀}, L^{p₁}, L^p` of an `F`-valued space (`F` a complex inner product space)
that agree on indicator atoms `1_A v` (`μ A < ∞`). For step functions `f = Σᵢ 1_{Aᵢ} vᵢ` and
`g = Σₖ 1_{Bₖ} wₖ` with disjoint steps and nonzero values, `core_bound`
(`RieszThorinBound.lean`) proves

  `|∫ ⟪g, T f⟫| ≤ ‖T₀‖^{1-θ} ‖T₁‖^θ ‖f‖_{L^p} ‖g‖_{L^{p'}}`,

with the norms written as `(Σᵢ ‖vᵢ‖^p μ(Aᵢ))^{1/p}` and `(Σₖ ‖wₖ‖^{p'} μ(Bₖ))^{1/p'}`.

Proof (Grafakos 1.3.4). With `s_j = 1/p_j`, `s = 1/p`, `α(z) = ((1-z)s₀ + z s₁)/s` and
`β(z) = ((1-z)(1-s₀) + z(1-s₁))/(1-s)`, put `f_z = Σᵢ ‖vᵢ‖^{α(z)-1} 1_{Aᵢ} vᵢ`,
`g_z = Σₖ ‖wₖ‖^{β(z)-1} 1_{Bₖ} wₖ` and

  `H(z) = Σᵢ Σₖ ‖vᵢ‖^{α(z)-1} ‖wₖ‖^{β(z)-1} ∫_{Bₖ} ⟪wₖ, Φᵢ⟫`,  `Φᵢ = T₀(1_{Aᵢ} vᵢ)`.

`H` is entire and bounded on the strip `0 ≤ Re z ≤ 1` (`differentiable_rtFun`,
`bddAbove_rtFun`). By the consistency of the three operators on atoms, `H(z) = ∫ ⟪g_z^*, T_j f_z⟫`
for `j = 0, 1`, where `g_z^*` has the conjugate coefficients (`rtFun_eq_integral`). On `Re z = j`,
Hölder (`enorm_integral_inner_stepFun_le`) and `‖T_j f_z‖ ≤ ‖T_j‖ ‖f_z‖` give
`|H(z)| ≤ ‖T_j‖ ‖f‖_p^{p/p_j} ‖g‖_{p'}^{p'/p_j'}`. Mathlib's Hadamard three-lines theorem
(`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`) bounds `|H(θ)|`,
and `H(θ) = ∫ ⟪g, T f⟫` because `α(θ) = β(θ) = 1`.

No `sorry`, no axioms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Complex
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.ExternalInputs

namespace RieszThorin

/-! ### The affine exponents -/

/-- The affine exponent `z ↦ ((1 - z) a + z b) / c`. -/
def affExp (a b c : ℝ) (z : ℂ) : ℂ := ((1 - z) * a + z * b) / c

theorem affExp_re (a b c : ℝ) (z : ℂ) :
    (affExp a b c z).re = ((1 - z.re) * a + z.re * b) / c := by
  simp [affExp]

theorem affExp_ofReal (a b c θ : ℝ) :
    affExp a b c (θ : ℂ) = ((((1 - θ) * a + θ * b) / c : ℝ) : ℂ) := by
  simp [affExp]

theorem differentiable_affExp (a b c : ℝ) : Differentiable ℂ (affExp a b c) := by
  unfold affExp
  fun_prop

theorem abs_affExp_re_sub_one_le {a b c : ℝ} (hc : 0 < c) {z : ℂ} (hz0 : 0 ≤ z.re)
    (hz1 : z.re ≤ 1) : |(affExp a b c z).re - 1| ≤ (|a| + |b|) / c + 1 := by
  rw [affExp_re]
  set x := z.re
  have h1 : |(1 - x) * a + x * b| ≤ |a| + |b| := by
    calc |(1 - x) * a + x * b| ≤ |(1 - x) * a| + |x * b| := abs_add_le _ _
      _ = (1 - x) * |a| + x * |b| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hz0]
      _ ≤ |a| + |b| := by nlinarith [abs_nonneg a, abs_nonneg b]
  calc |((1 - x) * a + x * b) / c - 1| ≤ |((1 - x) * a + x * b) / c| + |1| := abs_sub _ _
    _ = |(1 - x) * a + x * b| / c + 1 := by rw [abs_div, abs_of_pos hc, abs_one]
    _ ≤ (|a| + |b|) / c + 1 := by gcongr

theorem rpow_le_add_of_abs_le {r t K : ℝ} (hr : 0 < r) (ht : |t| ≤ K) :
    r ^ t ≤ r ^ K + r ^ (-K) := by
  rcases le_or_gt 1 r with h1 | h1
  · have : r ^ t ≤ r ^ K := Real.rpow_le_rpow_of_exponent_le h1 (le_of_abs_le ht)
    linarith [Real.rpow_nonneg hr.le (-K)]
  · have : r ^ t ≤ r ^ (-K) := Real.rpow_le_rpow_of_exponent_ge hr h1.le (neg_le_of_abs_le ht)
    linarith [Real.rpow_nonneg hr.le K]

/-! ### Norms of the analytic coefficients -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem norm_cpow_smul {v : F} (hv : v ≠ 0) (e : ℂ) :
    ‖((‖v‖ : ℂ) ^ (e - 1)) • v‖ = ‖v‖ ^ e.re := by
  have hr : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hr, sub_re, one_re,
    Real.rpow_sub_one hr.ne', div_mul_cancel₀ _ hr.ne']

theorem enorm_cpow_smul_rpow {v : F} (hv : v ≠ 0) (e : ℂ) (R : ℝ) :
    ‖((‖v‖ : ℂ) ^ (e - 1)) • v‖ₑ ^ R = ‖v‖ₑ ^ (e.re * R) := by
  have hr : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [← ofReal_norm, ← ofReal_norm, norm_cpow_smul hv,
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr _), ENNReal.ofReal_rpow_of_pos hr,
    ← Real.rpow_mul hr.le]

theorem enorm_conj_cpow_smul_rpow {w : F} (hw : w ≠ 0) (e : ℂ) (R : ℝ) :
    ‖(conj ((‖w‖ : ℂ) ^ (e - 1))) • w‖ₑ ^ R = ‖w‖ₑ ^ (e.re * R) := by
  rw [← enorm_cpow_smul_rpow hw e R, enorm_smul, enorm_smul]
  congr 2
  rw [← ofReal_norm, ← ofReal_norm, RCLike.norm_conj]

/-! ### The analytic function -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Riesz–Thorin function `H(z) = Σᵢ Σₖ rᵢ^{α(z)-1} ρₖ^{β(z)-1} cᵢₖ`. -/
def rtFun (r : ι → ℝ) (ρ : κ → ℝ) (c : ι → κ → ℂ) (α β : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ i, ∑ k, (r i : ℂ) ^ (α z - 1) * (ρ k : ℂ) ^ (β z - 1) * c i k

theorem differentiable_rtFun {r : ι → ℝ} {ρ : κ → ℝ} (hr : ∀ i, 0 < r i) (hρ : ∀ k, 0 < ρ k)
    (c : ι → κ → ℂ) {α β : ℂ → ℂ} (hα : Differentiable ℂ α) (hβ : Differentiable ℂ β) :
    Differentiable ℂ (rtFun r ρ c α β) := by
  intro z
  unfold rtFun
  refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun k _ => ?_
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) (differentiableAt_const _)
  · exact ((hα z).sub_const 1).const_cpow (Or.inl (ofReal_ne_zero.2 (hr i).ne'))
  · exact ((hβ z).sub_const 1).const_cpow (Or.inl (ofReal_ne_zero.2 (hρ k).ne'))

theorem bddAbove_rtFun {r : ι → ℝ} {ρ : κ → ℝ} (hr : ∀ i, 0 < r i) (hρ : ∀ k, 0 < ρ k)
    (c : ι → κ → ℂ) {α β : ℂ → ℂ} {K L : ℝ}
    (hα : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → |(α z).re - 1| ≤ K)
    (hβ : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → |(β z).re - 1| ≤ L) :
    BddAbove ((norm ∘ rtFun r ρ c α β) ''
      HadamardThreeLines.verticalClosedStrip 0 1) := by
  refine ⟨∑ i, ∑ k, (r i ^ K + r i ^ (-K)) * (ρ k ^ L + ρ k ^ (-L)) * ‖c i k‖, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : 0 ≤ z.re ∧ z.re ≤ 1 := hz
  simp only [Function.comp_apply, rtFun]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos (hr i),
    norm_cpow_eq_rpow_re_of_pos (hρ k), sub_re, sub_re, one_re]
  refine mul_le_mul_of_nonneg_right (mul_le_mul (rpow_le_add_of_abs_le (hr i) (hα z hz'.1 hz'.2))
    (rpow_le_add_of_abs_le (hρ k) (hβ z hz'.1 hz'.2)) (Real.rpow_nonneg (hρ k).le _)
    (add_nonneg (Real.rpow_nonneg (hr i).le _) (Real.rpow_nonneg (hr i).le _))) (norm_nonneg _)

/-! ### The integral representation -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `Σᵢ Σₖ aᵢ bₖ ∫_{Bₖ} ⟪wₖ, Φᵢ⟫ = ∫ ⟪Σₖ 1_{Bₖ} (conj bₖ) wₖ, Σᵢ aᵢ Φᵢ⟫`. -/
theorem sum_sum_eq_integral {B : κ → Set α} (hB : ∀ k, MeasurableSet (B k)) (w : κ → F)
    (Φ : ι → α → F) (hΦ : ∀ i k, IntegrableOn (Φ i) (B k) μ) (a : ι → ℂ) (b : κ → ℂ) :
    ∑ i, ∑ k, a i * b k * ∫ x in B k, ⟪w k, Φ i x⟫_ℂ ∂μ =
      ∫ x, ⟪stepFun B (fun k => conj (b k) • w k) x, ∑ i, a i • Φ i x⟫_ℂ ∂μ := by
  have hint : ∀ k, IntegrableOn (fun x => ∑ i, a i • Φ i x) (B k) μ := fun k =>
    integrable_finsetSum _ fun i _ => (hΦ i k).smul (a i)
  rw [integral_inner_stepFun hB _ hint, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : ∀ x, ⟪conj (b k) • w k, ∑ i, a i • Φ i x⟫_ℂ =
      ∑ i, b k * a i * ⟪w k, Φ i x⟫_ℂ := by
    intro x
    rw [inner_smul_left, RCLike.conj_conj, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right]
    ring
  simp_rw [h]
  rw [integral_finsetSum _ fun i _ => ((hΦ i k).const_inner (𝕜 := ℂ) (w k)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  ring

/-- **Endpoint estimate.** For a bounded operator `S` on `L^q` (`q = 1/s_q`) and functions `Ψᵢ`
representing `S(1_{Aᵢ} vᵢ)`, Hölder and the operator bound give
`‖∫ ⟪Σₖ 1_{Bₖ} w'ₖ, Σᵢ aᵢ Ψᵢ⟫‖ ≤ (Σₖ ‖w'ₖ‖^{q'} μ(Bₖ))^{1/q'} ‖S‖ (Σᵢ ‖aᵢ vᵢ‖^q μ(Aᵢ))^{1/q}`. -/
theorem endpoint_bound {q : ℝ≥0∞} [Fact (1 ≤ q)] {sq : ℝ} (hsq0 : 0 < sq) (hsq1 : sq < 1)
    (hq : q = ENNReal.ofReal sq⁻¹) (S : Lp F q μ →L[ℂ] Lp F q μ)
    {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i)) (hAμ : ∀ i, μ (A i) ≠ ∞)
    (hAd : Pairwise (Function.onFun Disjoint A)) (v : ι → F)
    {B : κ → Set α} (hB : ∀ k, MeasurableSet (B k)) (hBd : Pairwise (Function.onFun Disjoint B))
    (w' : κ → F) (Ψ : ι → α → F)
    (hΨ : ∀ i, Ψ i =ᵐ[μ] ⇑(S (indicatorConstLp q (hA i) (hAμ i) (v i)))) (a : ι → ℂ) :
    ‖∫ x, ⟪stepFun B w' x, ∑ i, a i • Ψ i x⟫_ℂ ∂μ‖ₑ ≤
      (∑ k, ‖w' k‖ₑ ^ (1 - sq)⁻¹ * μ (B k)) ^ (1 - sq) *
        (‖S‖ₑ * (∑ i, ‖a i • v i‖ₑ ^ sq⁻¹ * μ (A i)) ^ sq) := by
  have hPQ : (sq⁻¹).HolderConjugate (1 - sq)⁻¹ :=
    Real.HolderConjugate.inv_one_sub_inv hsq0 hsq1
  have hq0 : q ≠ 0 := by
    rw [hq, Ne, ENNReal.ofReal_eq_zero, not_le]; exact inv_pos.2 hsq0
  have hqt : q ≠ ∞ := by rw [hq]; exact ENNReal.ofReal_ne_top
  have hqr : q.toReal = sq⁻¹ := by rw [hq, ENNReal.toReal_ofReal (inv_pos.2 hsq0).le]
  have hφ : (fun x => ∑ i, a i • Ψ i x) =ᵐ[μ] ⇑(S (stepLp q A hA hAμ a v)) := by
    have hall : ∀ᵐ x ∂μ, ∀ i, Ψ i x = S (indicatorConstLp q (hA i) (hAμ i) (v i)) x :=
      ae_all_iff.2 hΨ
    filter_upwards [hall, coeFn_apply_stepLp S hA hAμ a v] with x h1 h2
    rw [h2]
    exact Finset.sum_congr rfl fun i _ => by rw [h1 i]
  have hmeas : AEStronglyMeasurable (fun x => ∑ i, a i • Ψ i x) μ :=
    (Lp.aestronglyMeasurable _).congr hφ.symm
  calc ‖∫ x, ⟪stepFun B w' x, ∑ i, a i • Ψ i x⟫_ℂ ∂μ‖ₑ
      ≤ (∑ k, ‖w' k‖ₑ ^ (1 - sq)⁻¹ * μ (B k)) ^ (1 / (1 - sq)⁻¹) *
          eLpNorm (fun x => ∑ i, a i • Ψ i x) (ENNReal.ofReal sq⁻¹) μ :=
        enorm_integral_inner_stepFun_le hB hBd w' hmeas hPQ
    _ = (∑ k, ‖w' k‖ₑ ^ (1 - sq)⁻¹ * μ (B k)) ^ (1 - sq) *
          ‖S (stepLp q A hA hAμ a v)‖ₑ := by
        rw [one_div, inv_inv, ← hq, eLpNorm_congr_ae hφ, Lp.enorm_def]
    _ ≤ (∑ k, ‖w' k‖ₑ ^ (1 - sq)⁻¹ * μ (B k)) ^ (1 - sq) *
          (‖S‖ₑ * ‖stepLp q A hA hAμ a v‖ₑ) := by
        gcongr
        exact S.le_opENorm _
    _ = _ := by
        rw [enorm_stepLp hq0 hqt hA hAμ hAd a v, hqr, one_div, inv_inv]

end RieszThorin

end UnforcedLeray.ExternalInputs
