import UnforcedLeray.Lib.CZL2.NewtonConv
import UnforcedLeray.Analysis.LerayProjection.GradientClosure
import NavierStokes.R3.ComparisonCutoffs
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Quadratic decay, L² membership and the closed gradient complement (INF01 L0)

Blueprint: INF01 (scoping note `INF01-CZ.md` §4.2, §5 targets T2 and T4); decision D5.

* `decayWeight y = (1 + |y|)⁻²` is square integrable on R³.
* A continuous function with `|Φ(y)| ≤ A|y|⁻²` far out is bounded by a multiple of
  `decayWeight`; the Newton-kernel pairing of a test has this decay.
* If `ψ` is smooth and `ψ`, `∇ψ` are bounded by a multiple of `decayWeight`, then `∇ψ`
  is an L² field orthogonal to every solenoidal L² field. The proof approximates `∇ψ`
  in L² by the test gradients `∇(χ_R ψ)` (cutoffs from
  `NavierStokes/R3/ComparisonCutoffs.lean`) and uses that the orthogonal complement
  is closed (`Leray.testGradient_mem_orthogonal`, `LerayProjection/Basic.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.RieszLp

open PressureAnalysis

/-- The weight `(1 + |y|)⁻²`, square integrable on R³. -/
def decayWeight (y : Space) : ℝ := ((1 + ‖y‖) ^ 2)⁻¹

theorem decayWeight_pos (y : Space) : 0 < decayWeight y := by
  unfold decayWeight; positivity

theorem continuous_decayWeight : Continuous decayWeight := by
  unfold decayWeight
  exact (continuous_const.add continuous_norm).pow 2 |>.inv₀
    fun y => pow_ne_zero 2 (ne_of_gt (add_pos_of_pos_of_nonneg one_pos (norm_nonneg y)))

theorem memLp_decayWeight : MemLp decayWeight 2 volume := by
  have hm : AEStronglyMeasurable decayWeight volume :=
    continuous_decayWeight.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have hi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) volume :=
    integrable_one_add_norm (by simp; norm_num)
  refine hi.congr (Eventually.of_forall fun y => ?_)
  have h1 : 0 < 1 + ‖y‖ := by positivity
  simp only [decayWeight]
  rw [Real.rpow_neg h1.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [inv_pow, ← pow_mul]

/-- Anything bounded in norm by a multiple of `decayWeight` is in L². -/
theorem memLp_two_of_norm_le {E : Type*} [NormedAddCommGroup E] {Φ : Space → E}
    (hΦ : AEStronglyMeasurable Φ volume) {M : ℝ} (h : ∀ y, ‖Φ y‖ ≤ M * decayWeight y) :
    MemLp Φ 2 volume := by
  refine (memLp_decayWeight.const_mul M).of_le hΦ (Eventually.of_forall fun y => ?_)
  exact (h y).trans (le_abs_self _) |>.trans_eq (Real.norm_eq_abs _).symm

/-- A continuous function with far-field bound `A |y|⁻²` is bounded by `M (1+|y|)⁻²`. -/
theorem exists_decay_bound {Φ : Space → ℝ} (hΦ : Continuous Φ) {r A : ℝ} (hr : 1 ≤ r)
    (hfar : ∀ y, r ≤ ‖y‖ → |Φ y| ≤ A * (‖y‖ ^ 2)⁻¹) :
    ∃ M, ∀ y, |Φ y| ≤ M * decayWeight y := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Space) r).exists_bound_of_continuousOn
    hΦ.continuousOn
  refine ⟨max B 0 * (1 + r) ^ 2 + 4 * max A 0, fun y => ?_⟩
  have hw := decayWeight_pos y
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hA0 : 0 ≤ max A 0 := le_max_right _ _
  by_cases hy : ‖y‖ ≤ r
  · have h1 : |Φ y| ≤ max B 0 := by
      rw [← Real.norm_eq_abs]
      exact (hB y (by simpa [mem_closedBall, dist_zero_right] using hy)).trans (le_max_left _ _)
    have h2 : 1 ≤ (1 + r) ^ 2 * decayWeight y := by
      unfold decayWeight
      rw [← div_eq_mul_inv, one_le_div (by positivity)]
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith [mul_nonneg hA0 hw.le]
  · push Not at hy
    have hy0 : 0 < ‖y‖ := by linarith
    have h1 := hfar y hy.le
    have h2 : A * (‖y‖ ^ 2)⁻¹ ≤ max A 0 * (‖y‖ ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have h3 : (‖y‖ ^ 2)⁻¹ ≤ 4 * decayWeight y := by
      unfold decayWeight
      have hsq : (1 + ‖y‖) ^ 2 ≤ 4 * ‖y‖ ^ 2 := by nlinarith
      calc (‖y‖ ^ 2)⁻¹ = 4 * (4 * ‖y‖ ^ 2)⁻¹ := by
            rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_mul]
        _ ≤ 4 * ((1 + ‖y‖) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hsq) (by norm_num)
    have h4 : 0 ≤ max B 0 * (1 + r) ^ 2 * decayWeight y := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hA0]

/-- The Newton-kernel pairing of a compact smooth test decays like `(1+|y|)⁻²`. -/
theorem newtonPair_decay (i : Fin 3) {f : Space → ℝ} (hf : IsSpatialTest f) :
    ∃ M, ∀ y, |newtonPair i f y| ≤ M * decayWeight y := by
  obtain ⟨ρ, hρ⟩ := hf.compact.isCompact.isBounded.subset_closedBall 0
  have hsupp : ∀ x, max ρ 1 < ‖x‖ → f x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hρ hmem
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_left ρ 1]
  have hcont : Continuous (newtonPair i f) := by
    have he : newtonPair i f = fun y => -newtonConv (spatialTestDerivative i f) y := by
      funext y; rw [newtonConv_partial hf i y, neg_neg]
    rw [he]
    exact (newtonConv_contDiff (hf.derivative i)).continuous.neg
  refine exists_decay_bound hcont (r := 2 * max ρ 1) (A := Real.pi⁻¹ * ∫ x, |f x|)
    (by linarith [le_max_right ρ 1]) fun y hy => ?_
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith [le_max_right ρ 1]
  have h := abs_newtonPair_le_of_far i hf.integrable hsupp hy hy0
  calc |newtonPair i f y| ≤ Real.pi⁻¹ * (‖y‖ ^ 2)⁻¹ * ∫ x, |f x| := h
    _ = Real.pi⁻¹ * (∫ x, |f x|) * (‖y‖ ^ 2)⁻¹ := by ring

/-- Dominated convergence in L² for sequences dominated by a fixed L² function. -/
theorem tendsto_eLpNorm_two_of_dominated {E : Type*} [NormedAddCommGroup E]
    {D : ℕ → Space → E} (hD : ∀ n, AEStronglyMeasurable (D n) volume)
    {B : Space → ℝ} (hB : MemLp B 2 volume) (hbound : ∀ n x, ‖D n x‖ ≤ B x)
    (hlim : ∀ x, Tendsto (fun n => ‖D n x‖) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (D n) 2 volume) atTop (𝓝 0) := by
  have hDm : ∀ n, MemLp (D n) 2 volume := fun n =>
    hB.of_le (hD n) (Eventually.of_forall fun x =>
      (hbound n x).trans ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm))
  have heq : ∀ n, eLpNorm (D n) 2 volume =
      ENNReal.ofReal ((∫ x, ‖D n x‖ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹) := fun n => by
    simpa using (hDm n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
  have hint : Tendsto (fun n => ∫ x, ‖D n x‖ ^ (2 : ℝ)) atTop (𝓝 0) := by
    have hBi : Integrable (fun x => ‖B x‖ ^ (2 : ℝ)) volume := by
      simpa using hB.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    have h := tendsto_integral_of_dominated_convergence (μ := volume)
      (F := fun n x => ‖D n x‖ ^ (2 : ℝ)) (f := fun _ => (0 : ℝ))
      (fun x => ‖B x‖ ^ (2 : ℝ))
      (fun n => ((hD n).norm.aemeasurable.pow_const (2 : ℝ)).aestronglyMeasurable)
      hBi
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact Real.rpow_le_rpow (norm_nonneg _)
          ((hbound n x).trans (le_abs_self _) |>.trans_eq (Real.norm_eq_abs _).symm)
          (by norm_num))
      (Eventually.of_forall fun x => by
        have := ((Real.continuous_rpow_const (q := 2) (by norm_num)).tendsto 0).comp (hlim x)
        simpa [Function.comp_def] using this)
    simpa using h
  have hc : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ (2 : ℝ)⁻¹)) (𝓝 0) (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.comp
      (Real.continuous_rpow_const (q := (2 : ℝ)⁻¹) (by norm_num))).tendsto 0
    simpa [Function.comp_def] using this
  simp_rw [heq]
  exact hc.comp hint

/-- The gradient field `∇ψ = Σᵢ ∂ᵢψ eᵢ` of a scalar function. -/
def gradField (ψ : Space → ℝ) : SpatialField :=
  fun x => ∑ i : Fin 3, spatialTestDerivative i ψ x • coordinateVector i

theorem norm_coordinateVector (i : Fin 3) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

theorem norm_sum_smul_coordinateVector_le (a : Fin 3 → ℝ) :
    ‖∑ i : Fin 3, a i • coordinateVector i‖ ≤ ∑ i : Fin 3, |a i| := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, norm_coordinateVector, mul_one, Real.norm_eq_abs]

theorem sum_smul_coordinateVector_apply (a : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i : Fin 3, a i • coordinateVector i) j = a j := by
  simp [coordinateVector, Pi.single_apply]

theorem continuous_gradField {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (gradField ψ) := by
  unfold gradField
  refine continuous_finsetSum _ fun i _ => ?_
  exact (contDiff_spatialTestDerivative hψ i).continuous.smul continuous_const

/-- Product rule for a coordinate derivative. -/
theorem spatialTestDerivative_mul {a b : Space → ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (i : Fin 3) (x : Space) :
    spatialTestDerivative i (fun y => a y * b y) x =
      a x * spatialTestDerivative i b x + b x * spatialTestDerivative i a x := by
  unfold spatialTestDerivative
  rw [fderiv_fun_mul ((ha.differentiable (by simp)).differentiableAt)
    ((hb.differentiable (by simp)).differentiableAt)]
  simp

/-- If `ψ` is smooth and `ψ`, `∇ψ` are bounded by `M (1+|y|)⁻²`, then `∇ψ ∈ L²`. -/
theorem memLp_gradField {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) {M : ℝ}
    (hdψ : ∀ i x, |spatialTestDerivative i ψ x| ≤ M * decayWeight x) :
    MemLp (gradField ψ) 2 volume := by
  refine memLp_two_of_norm_le (continuous_gradField hψ).aestronglyMeasurable
    (M := 3 * M) fun x => ?_
  refine (norm_sum_smul_coordinateVector_le _).trans ?_
  calc ∑ i : Fin 3, |spatialTestDerivative i ψ x| ≤ ∑ _i : Fin 3, M * decayWeight x :=
        Finset.sum_le_sum fun i _ => hdψ i x
    _ = 3 * M * decayWeight x := by simp; ring

/-- If `ψ` is smooth and `ψ`, `∇ψ` are bounded by `M (1+|y|)⁻²`, then `∇ψ` is orthogonal
to every solenoidal L² field: it is the L² limit of the test gradients `∇(χ_R ψ)`. -/
theorem toL2_gradField_mem_orthogonal {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) {M : ℝ}
    (hψb : ∀ x, |ψ x| ≤ M * decayWeight x)
    (hdψ : ∀ i x, |spatialTestDerivative i ψ x| ≤ M * decayWeight x) :
    toL2 (gradField ψ) ∈ Leray.solenoidalSubspaceᗮ := by
  open NavierStokesR3.ComparisonCutoffs in
  have hG := memLp_gradField hψ hdψ
  have hM : 0 ≤ M := by
    have h := (abs_nonneg (ψ 0)).trans (hψb 0)
    exact nonneg_of_mul_nonneg_left h (decayWeight_pos 0)
  set C := NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 with hCdef
  have hC : 0 < C := NavierStokesR3.ComparisonCutoffs.derivativeConstant_pos 1
  let χ : ℕ → Space → ℝ := fun n => NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1)
  have hR : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hχs : ∀ n, ContDiff ℝ ∞ (χ n) := fun n =>
    NavierStokesR3.ComparisonCutoffs.cutoff_smooth _
  let θ : ℕ → Space → ℝ := fun n x => χ n x * ψ x
  have hθ : ∀ n, IsSpatialTest (θ n) := fun n =>
    ⟨(hχs n).mul hψ,
      (NavierStokesR3.ComparisonCutoffs.cutoff_hasCompactSupport (hR n)).mul_right⟩
  -- derivative bound for the cutoffs
  have hdχ : ∀ n i x, |spatialTestDerivative i (χ n) x| ≤ C / ((n : ℝ) + 1) := by
    intro n i x
    have h1 := NavierStokesR3.ComparisonCutoffs.cutoff_fderiv_le (hR n) x
    have h2 := (fderiv ℝ (χ n) x).le_opNorm (coordinateVector i)
    rw [norm_coordinateVector, mul_one] at h2
    rw [← Real.norm_eq_abs]
    exact h2.trans h1
  -- the difference field
  let D : ℕ → Space → Space := fun n x =>
    ∑ i : Fin 3, ((χ n x - 1) * spatialTestDerivative i ψ x +
      ψ x * spatialTestDerivative i (χ n) x) • coordinateVector i
  have hDeq : ∀ n, (fun x => ∑ i : Fin 3, spatialTestDerivative i (θ n) x • coordinateVector i)
      - gradField ψ = D n := by
    intro n
    funext x
    simp only [Pi.sub_apply, gradField, D, ← Finset.sum_sub_distrib, ← sub_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show θ n = fun y => χ n y * ψ y from rfl, spatialTestDerivative_mul (hχs n) hψ]
    ring_nf
  have hDcont : ∀ n, Continuous (D n) := by
    intro n
    refine continuous_finsetSum _ fun i _ => ?_
    have hc : Continuous fun x => (χ n x - 1) * spatialTestDerivative i ψ x +
        ψ x * spatialTestDerivative i (χ n) x :=
      (((hχs n).continuous.sub continuous_const).mul
        (contDiff_spatialTestDerivative hψ i).continuous).add
        (hψ.continuous.mul (contDiff_spatialTestDerivative (hχs n) i).continuous)
    exact hc.smul continuous_const
  have hDb : ∀ n x, ‖D n x‖ ≤
      3 * M * decayWeight x * ((1 - χ n x) + C / ((n : ℝ) + 1)) := by
    intro n x
    refine (norm_sum_smul_coordinateVector_le _).trans ?_
    have hw := decayWeight_pos x
    have h01 := NavierStokesR3.ComparisonCutoffs.cutoff_mem_Icc ((n : ℝ) + 1) x
    calc ∑ i : Fin 3, |(χ n x - 1) * spatialTestDerivative i ψ x +
          ψ x * spatialTestDerivative i (χ n) x|
        ≤ ∑ _i : Fin 3, M * decayWeight x * ((1 - χ n x) + C / ((n : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_sub_comm, abs_of_nonneg (by linarith [h01.2] :
            (0 : ℝ) ≤ 1 - χ n x)]
          have e1 := mul_le_mul_of_nonneg_left (hdψ i x) (by linarith [h01.2] :
            (0 : ℝ) ≤ 1 - χ n x)
          have e2 := mul_le_mul (hψb x) (hdχ n i x) (abs_nonneg _) (by positivity)
          nlinarith
      _ = 3 * M * decayWeight x * ((1 - χ n x) + C / ((n : ℝ) + 1)) := by simp; ring
  have hDB : ∀ n x, ‖D n x‖ ≤ 3 * M * (1 + C) * decayWeight x := by
    intro n x
    refine (hDb n x).trans ?_
    have hw := decayWeight_pos x
    have h01 := NavierStokesR3.ComparisonCutoffs.cutoff_mem_Icc ((n : ℝ) + 1) x
    have hCn : C / ((n : ℝ) + 1) ≤ C := div_le_self hC.le (by linarith [hR n,
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have : (1 - χ n x) + C / ((n : ℝ) + 1) ≤ 1 + C := by linarith [h01.1]
    calc 3 * M * decayWeight x * ((1 - χ n x) + C / ((n : ℝ) + 1))
        ≤ 3 * M * decayWeight x * (1 + C) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 3 * M * (1 + C) * decayWeight x := by ring
  have hDlim : ∀ x, Tendsto (fun n => ‖D n x‖) atTop (𝓝 0) := by
    intro x
    have hev : ∀ᶠ n : ℕ in atTop, 1 - χ n x = 0 := by
      obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
      refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have : ‖x‖ ≤ (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp [χ, NavierStokesR3.ComparisonCutoffs.cutoff_eq_one (hR n) this]
    have h1 : Tendsto (fun n : ℕ => 1 - χ n x) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
    have h2 : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C
      simpa [div_eq_mul_inv] using this
    have h3 : Tendsto (fun n : ℕ => 3 * M * decayWeight x * ((1 - χ n x) + C / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
      simpa using (h1.add h2).const_mul (3 * M * decayWeight x)
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hDb n x) h3
  have hBm : MemLp (fun x => 3 * M * (1 + C) * decayWeight x) 2 volume :=
    memLp_decayWeight.const_mul _
  have hT := tendsto_eLpNorm_two_of_dominated (fun n => (hDcont n).aestronglyMeasurable)
    hBm hDB hDlim
  have hconv : Tendsto (fun n => Leray.testGradient (θ n) (hθ n)) atTop
      (𝓝 (toL2 (gradField ψ))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hT.congr fun n => ?_
    apply eLpNorm_congr_ae
    filter_upwards [Leray.coeFn_testGradient (θ n) (hθ n), coeFn_toL2 hG] with x h1 h2
    rw [Pi.sub_apply, h1, h2, ← hDeq n]
    rfl
  exact (Submodule.isClosed_orthogonal _).mem_of_tendsto hconv
    (Eventually.of_forall fun n => Leray.testGradient_mem_orthogonal (θ n) (hθ n))

end UnforcedLeray.RieszLp
