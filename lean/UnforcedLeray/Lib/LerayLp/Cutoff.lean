import UnforcedLeray.Lib.LerayLp.Duality

/-!
# Cutoff limits for solenoidal fields against decaying gradients (INF01 T15, helper)


§5, Level 2, in the restricted form of §4.8: "`P = id` on solenoidal fields. Use duality:
`⟨𝔓f, g⟩ = ⟨f, g⟩ + ⟨f, ∇ψ⟩` with `ψ = N ∗ div g = O(|x|⁻²)`, and the cutoff error is
`‖ψ∇χ_R‖_{p'} ≲ R^{-3/p} → 0`." Manuscript use: unit B0797 (eq:ward:W2.6,
`paper/main.tex` lines 11539–11560) and unit B0439 (lines 7364–7387, "surjectivity uses
`g = P_σ g` on `Y_{q,σ}`").

* `powWeight a x = (1 + |x|)^{-a}`, `memLp_powWeight`: in `L^s(R³)` when `a s > 3` (or `s = ∞`);
* `abs_spatialTestDerivative_cutoff_le`: `|∂ᵢχ_R(x)| ≤ 3C(1 + |x|)⁻¹` for `R ≥ 1` (the
  derivative of the cutoff of `NavierStokes/R3/ComparisonCutoffs.lean` lives in `R ≤ |x| ≤ 2R`);
* `integral_inner_gradField_eq_zero` (cutoff lemma): if `F` is distributionally solenoidal,
  `ψ` is smooth, and `|F||∇ψ|`, `|F||ψ|(1 + |x|)⁻¹` are integrable, then `∫ ⟨F, ∇ψ⟩ = 0`
  (dominated convergence for `∫ ⟨F, ∇(χ_n ψ)⟩ = 0`);
* `exists_decay_bound_three`, `lerayPotential_grad_decay`, `test_decay`: pointwise
  `(1 + |x|)⁻³` bounds for `∇(N ∗ div f)` and for compact tests;
* `integrable_inner_of_memLp`, `integrable_norm_mul_of_memLp`: Hölder in the form used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.RieszLp

/-! ### Power weights -/

/-- The weight `(1 + |x|)^{-a}`. -/
def powWeight (a : ℝ) (x : Space) : ℝ := (1 + ‖x‖) ^ (-a)

theorem powWeight_pos (a : ℝ) (x : Space) : 0 < powWeight a x :=
  Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 + ‖x‖) _

theorem powWeight_nonneg (a : ℝ) (x : Space) : 0 ≤ powWeight a x := (powWeight_pos a x).le

theorem continuous_powWeight (a : ℝ) : Continuous (powWeight a) :=
  (continuous_const.add continuous_norm).rpow_const fun x =>
    Or.inl (by positivity : (0 : ℝ) < 1 + ‖x‖).ne'

theorem powWeight_natCast (n : ℕ) (x : Space) : powWeight n x = ((1 + ‖x‖) ^ n)⁻¹ := by
  rw [powWeight, Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem powWeight_le_one {a : ℝ} (ha : 0 ≤ a) (x : Space) : powWeight a x ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by linarith)

/-- `(1 + |x|)^{-a} ∈ L^s(R³)` when `s = ∞` or `a s > 3`. -/
theorem memLp_powWeight {a : ℝ} (ha : 0 ≤ a) {s : ℝ≥0∞} (hs0 : s ≠ 0)
    (hcond : s = ⊤ ∨ 3 < a * s.toReal) : MemLp (powWeight a) s volume := by
  rcases hcond with rfl | h
  · refine memLp_top_of_bound (continuous_powWeight a).aestronglyMeasurable 1
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (powWeight_nonneg a x)]
    exact powWeight_le_one ha x
  · have hs : s ≠ ⊤ := by
      rintro rfl
      simp at h
      linarith
    rw [← integrable_norm_rpow_iff (continuous_powWeight a).aestronglyMeasurable hs0 hs]
    have hdim : ((Module.finrank ℝ Space : ℕ) : ℝ) < a * s.toReal := by
      rw [finrank_euclideanSpace_fin]
      exact_mod_cast h
    refine (integrable_one_add_norm (μ := volume) hdim).congr (Eventually.of_forall fun x => ?_)
    show (1 + ‖x‖) ^ (-(a * s.toReal)) = ‖powWeight a x‖ ^ s.toReal
    rw [Real.norm_of_nonneg (powWeight_nonneg a x), powWeight,
      ← Real.rpow_mul (by positivity)]
    ring_nf

/-! ### Hölder -/

/-- Hölder: `‖f‖ w` is integrable for `f ∈ L^p`, `w ∈ L^q`. -/
theorem integrable_norm_mul_of_memLp {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] {E : Type*}
    [NormedAddCommGroup E] {f : Space → E} {w : Space → ℝ} (hf : MemLp f p volume)
    (hw : MemLp w q volume) : Integrable (fun x => ‖f x‖ * w x) volume :=
  hf.norm.integrable_mul hw

/-- Hölder for the pointwise inner product of `f ∈ L^p` and `g ∈ L^q`. -/
theorem integrable_inner_of_memLp {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    {f g : SpatialField} (hf : MemLp f p volume) (hg : MemLp g q volume) :
    Integrable (fun x => inner ℝ (f x) (g x)) volume := by
  refine (hf.norm.integrable_mul hg.norm).mono' (hf.1.inner hg.1)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

/-- The inner product with a gradient field in coordinates. -/
theorem inner_gradField (v : Space) (φ : Space → ℝ) (x : Space) :
    inner ℝ v (gradField φ x) = ∑ i : Fin 3, v i * spatialTestDerivative i φ x := by
  rw [real_inner_comm]
  exact Leray.gradient_inner φ x v

theorem abs_spatialTestDerivative_le_norm_gradField (φ : Space → ℝ) (x : Space) (i : Fin 3) :
    |spatialTestDerivative i φ x| ≤ ‖gradField φ x‖ := by
  rw [← gradField_apply, ← Real.norm_eq_abs]
  exact PiLp.norm_apply_le _ i

/-! ### The cutoffs -/

open NavierStokesR3.ComparisonCutoffs in
theorem spatialTestDerivative_cutoff_of_lt {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ < R)
    (i : Fin 3) : spatialTestDerivative i (cutoff R) x = 0 := by
  have h : cutoff R =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact cutoff_eq_one hR (le_of_lt hy)
  unfold spatialTestDerivative
  rw [h.fderiv_eq]
  simp

open NavierStokesR3.ComparisonCutoffs in
theorem spatialTestDerivative_cutoff_of_gt {R : ℝ} (hR : 0 < R) {x : Space}
    (hx : 2 * R < ‖x‖) (i : Fin 3) : spatialTestDerivative i (cutoff R) x = 0 := by
  have h : cutoff R =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact cutoff_eq_zero hR (le_of_lt hy)
  unfold spatialTestDerivative
  rw [h.fderiv_eq]
  simp

open NavierStokesR3.ComparisonCutoffs in
/-- Inside the ball of radius `R`, `∂ᵢ(χ_R ψ) = ∂ᵢψ`. -/
theorem spatialTestDerivative_cutoff_mul_of_lt {R : ℝ} (hR : 0 < R) {x : Space}
    (hx : ‖x‖ < R) (ψ : Space → ℝ) (i : Fin 3) :
    spatialTestDerivative i (fun y => cutoff R y * ψ y) x = spatialTestDerivative i ψ x := by
  have h : (fun y => cutoff R y * ψ y) =ᶠ[𝓝 x] ψ := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    rw [cutoff_eq_one hR (le_of_lt hy), one_mul]
  unfold spatialTestDerivative
  rw [h.fderiv_eq]

open NavierStokesR3.ComparisonCutoffs in
/-- `|∂ᵢχ_R(x)| ≤ 3C(1 + |x|)⁻¹` for `R ≥ 1`, with `C = derivativeConstant 1`. -/
theorem abs_spatialTestDerivative_cutoff_le {R : ℝ} (hR : 1 ≤ R) (x : Space) (i : Fin 3) :
    |spatialTestDerivative i (cutoff R) x| ≤ 3 * derivativeConstant 1 * (1 + ‖x‖)⁻¹ := by
  have hR0 : 0 < R := by linarith
  have hC := derivativeConstant_pos 1
  have hpos : 0 < 1 + ‖x‖ := by positivity
  by_cases h : spatialTestDerivative i (cutoff R) x = 0
  · rw [h, abs_zero]
    positivity
  have h1 : R ≤ ‖x‖ := not_lt.1 fun h' => h (spatialTestDerivative_cutoff_of_lt hR0 h' i)
  have h2 : ‖x‖ ≤ 2 * R := not_lt.1 fun h' => h (spatialTestDerivative_cutoff_of_gt hR0 h' i)
  have hb : |spatialTestDerivative i (cutoff R) x| ≤ derivativeConstant 1 / R := by
    have e1 := cutoff_fderiv_le hR0 x
    have e2 := (fderiv ℝ (cutoff R) x).le_opNorm (coordinateVector i)
    rw [norm_coordinateVector, mul_one] at e2
    rw [← Real.norm_eq_abs]
    exact e2.trans e1
  refine hb.trans ?_
  rw [div_le_iff₀ hR0]
  calc derivativeConstant 1 = 3 * derivativeConstant 1 * (1 + ‖x‖)⁻¹ * ((1 + ‖x‖) / 3) := by
        field_simp
    _ ≤ 3 * derivativeConstant 1 * (1 + ‖x‖)⁻¹ * R := by
        gcongr
        linarith

/-! ### The cutoff lemma -/

open NavierStokesR3.ComparisonCutoffs in
/-- **Cutoff lemma.** If `F` is distributionally solenoidal, `ψ` is smooth and both
`|F||∇ψ|` and `|F||ψ|(1 + |x|)⁻¹` are integrable, then `∫ ⟨F, ∇ψ⟩ = 0`. Proof: `∫ ⟨F, ∇(χ_n ψ)⟩ = 0`
for the cutoffs `χ_n = χ_{n+1}`, `|∇(χ_n ψ)| ≤ 3|∇ψ| + 9C|ψ|(1 + |x|)⁻¹`, and
`∇(χ_n ψ)(x) = ∇ψ(x)` once `n + 1 > |x|`; dominated convergence. -/
theorem integral_inner_gradField_eq_zero {F : SpatialField} (hF : IsSolenoidal F)
    (hFm : AEStronglyMeasurable F volume) {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (h1 : Integrable (fun x => ‖F x‖ * ‖gradField ψ x‖) volume)
    (h2 : Integrable (fun x => ‖F x‖ * |ψ x| * (1 + ‖x‖)⁻¹) volume) :
    ∫ x, inner ℝ (F x) (gradField ψ x) = 0 := by
  set C := derivativeConstant 1 with hCdef
  have hC : 0 < C := derivativeConstant_pos 1
  let χ : ℕ → Space → ℝ := fun n => cutoff ((n : ℝ) + 1)
  have hR1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hR : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by linarith [hR1 n]
  have hχs : ∀ n, ContDiff ℝ ∞ (χ n) := fun n => cutoff_smooth _
  let θ : ℕ → Space → ℝ := fun n x => χ n x * ψ x
  have hθ : ∀ n, IsSpatialTest (θ n) := fun n =>
    ⟨(hχs n).mul hψ, (cutoff_hasCompactSupport (hR n)).mul_right⟩
  have hzero : ∀ n, ∫ x, inner ℝ (F x) (gradField (θ n) x) = 0 := by
    intro n
    rw [← hF.identity (θ n) (hθ n)]
    exact integral_congr_ae (Eventually.of_forall fun x => inner_gradField (F x) (θ n) x)
  have hcomp : ∀ n x i, |spatialTestDerivative i (θ n) x| ≤
      ‖gradField ψ x‖ + |ψ x| * (3 * C * (1 + ‖x‖)⁻¹) := by
    intro n x i
    rw [show θ n = fun y => χ n y * ψ y from rfl, spatialTestDerivative_mul (hχs n) hψ]
    have hχ01 := cutoff_mem_Icc ((n : ℝ) + 1) x
    have hχabs : |χ n x| ≤ 1 := by
      rw [abs_of_nonneg hχ01.1]
      exact hχ01.2
    have hdψ := abs_spatialTestDerivative_le_norm_gradField ψ x i
    have hdχ := abs_spatialTestDerivative_cutoff_le (hR1 n) x i
    calc |χ n x * spatialTestDerivative i ψ x + ψ x * spatialTestDerivative i (χ n) x|
        ≤ |χ n x| * |spatialTestDerivative i ψ x| +
            |ψ x| * |spatialTestDerivative i (χ n) x| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ 1 * ‖gradField ψ x‖ + |ψ x| * (3 * C * (1 + ‖x‖)⁻¹) := by
          gcongr
      _ = ‖gradField ψ x‖ + |ψ x| * (3 * C * (1 + ‖x‖)⁻¹) := by ring
  have hbound : ∀ n x, ‖inner ℝ (F x) (gradField (θ n) x)‖ ≤
      ‖F x‖ * (3 * (‖gradField ψ x‖ + |ψ x| * (3 * C * (1 + ‖x‖)⁻¹))) := by
    intro n x
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine (norm_sum_smul_coordinateVector_le _).trans ?_
    calc ∑ i : Fin 3, |spatialTestDerivative i (θ n) x|
        ≤ ∑ _i : Fin 3, (‖gradField ψ x‖ + |ψ x| * (3 * C * (1 + ‖x‖)⁻¹)) :=
          Finset.sum_le_sum fun i _ => hcomp n x i
      _ = 3 * (‖gradField ψ x‖ + |ψ x| * (3 * C * (1 + ‖x‖)⁻¹)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hBint : Integrable (fun x =>
      ‖F x‖ * (3 * (‖gradField ψ x‖ + |ψ x| * (3 * C * (1 + ‖x‖)⁻¹)))) volume := by
    refine ((h1.const_mul 3).add (h2.const_mul (9 * C))).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hlim : ∀ x, Tendsto (fun n => inner ℝ (F x) (gradField (θ n) x)) atTop
      (𝓝 (inner ℝ (F x) (gradField ψ x))) := by
    intro x
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hx : ‖x‖ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have e : gradField (θ n) x = gradField ψ x := by
      unfold gradField
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show θ n = fun y => cutoff ((n : ℝ) + 1) y * ψ y from rfl,
        spatialTestDerivative_cutoff_mul_of_lt (hR n) hx]
    show inner ℝ (F x) (gradField ψ x) = inner ℝ (F x) (gradField (θ n) x)
    rw [e]
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => inner ℝ (F x) (gradField (θ n) x)) volume :=
    fun n => hFm.inner (continuous_gradField ((hχs n).mul hψ)).aestronglyMeasurable
  have hT := tendsto_integral_of_dominated_convergence _ hmeas hBint
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  simp_rw [hzero] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

/-! ### Pointwise `(1 + |x|)⁻³` bounds -/

/-- A continuous function with far-field bound `A|y|⁻³` is bounded by `M(1 + |y|)⁻³`. -/
theorem exists_decay_bound_three {Φ : Space → ℝ} (hΦ : Continuous Φ) {r A : ℝ} (hr : 1 ≤ r)
    (hfar : ∀ y, r ≤ ‖y‖ → |Φ y| ≤ A * ‖y‖ ^ (-3 : ℝ)) :
    ∃ M, ∀ y, |Φ y| ≤ M * powWeight 3 y := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Space) r).exists_bound_of_continuousOn
    hΦ.continuousOn
  refine ⟨max B 0 * (1 + r) ^ 3 + 8 * max A 0, fun y => ?_⟩
  have hw : powWeight 3 y = ((1 + ‖y‖) ^ 3)⁻¹ := by exact_mod_cast powWeight_natCast 3 y
  have hw0 : 0 < powWeight 3 y := powWeight_pos 3 y
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hA0 : 0 ≤ max A 0 := le_max_right _ _
  by_cases hy : ‖y‖ ≤ r
  · have h1 : |Φ y| ≤ max B 0 := by
      rw [← Real.norm_eq_abs]
      exact (hB y (by simpa [mem_closedBall, dist_zero_right] using hy)).trans (le_max_left _ _)
    have h2 : 1 ≤ (1 + r) ^ 3 * powWeight 3 y := by
      rw [hw, ← div_eq_mul_inv, one_le_div (by positivity)]
      exact pow_le_pow_left₀ (by positivity) (by linarith) 3
    nlinarith [mul_nonneg hA0 hw0.le]
  · push Not at hy
    have hy0 : 0 < ‖y‖ := by linarith
    have h1 := hfar y hy.le
    have e : ‖y‖ ^ (-3 : ℝ) = (‖y‖ ^ 3)⁻¹ := by
      rw [Real.rpow_neg hy0.le]
      norm_cast
    rw [e] at h1
    have h2 : A * (‖y‖ ^ 3)⁻¹ ≤ max A 0 * (‖y‖ ^ 3)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have h3 : (‖y‖ ^ 3)⁻¹ ≤ 8 * powWeight 3 y := by
      rw [hw]
      have hcube : (1 + ‖y‖) ^ 3 ≤ 8 * ‖y‖ ^ 3 := by
        have : 1 + ‖y‖ ≤ 2 * ‖y‖ := by linarith
        calc (1 + ‖y‖) ^ 3 ≤ (2 * ‖y‖) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
          _ = 8 * ‖y‖ ^ 3 := by ring
      calc (‖y‖ ^ 3)⁻¹ = 8 * (8 * ‖y‖ ^ 3)⁻¹ := by
            rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (8 : ℝ) ≠ 0), one_mul]
        _ ≤ 8 * ((1 + ‖y‖) ^ 3)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hcube) (by norm_num)
    have h4 : 0 ≤ max B 0 * (1 + r) ^ 3 * powWeight 3 y := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hA0]

/-- A compact smooth test is bounded by a multiple of `(1 + |y|)⁻³`. -/
theorem test_decay {g : Space → ℝ} (hg : IsSpatialTest g) :
    ∃ M, ∀ y, |g y| ≤ M * powWeight 3 y := by
  obtain ⟨ρ, hρ⟩ := hg.compact.isCompact.isBounded.subset_closedBall 0
  refine exists_decay_bound_three hg.continuous (r := max 1 (ρ + 1)) (A := 0)
    (le_max_left _ _) fun y hy => ?_
  have hgy : g y = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hρ hmem
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_right 1 (ρ + 1)]
  rw [hgy, abs_zero, zero_mul]

/-- `∇(N ∗ div f)` is bounded by a multiple of `(1 + |y|)⁻³` (componentwise). -/
theorem lerayPotential_grad_decay {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j)) :
    ∃ M, ∀ i y, |spatialTestDerivative i (lerayPotential f) y| ≤ M * powWeight 3 y := by
  have hψ : ContDiff ℝ ∞ (lerayPotential f) := lerayPotential_contDiff hf
  have hdec := fun i k => rieszPairTest_decay (hf k) i k
  choose C R hCR using hdec
  have hi : ∀ i : Fin 3, ∃ M, ∀ y, |spatialTestDerivative i (lerayPotential f) y| ≤
      M * powWeight 3 y := by
    intro i
    refine exists_decay_bound_three
      (PressureAnalysis.contDiff_spatialTestDerivative hψ i).continuous
      (r := 1 + ∑ k : Fin 3, |R i k|) (A := ∑ k : Fin 3, |C i k|)
      (by linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => abs_nonneg (R i k)])
      fun y hy => ?_
    rw [spatialTestDerivative_lerayPotential_eq_sum hf i y]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    have hRk : R i k ≤ ‖y‖ := by
      have h1 : R i k ≤ |R i k| := le_abs_self _
      have h2 : |R i k| ≤ ∑ k : Fin 3, |R i k| :=
        Finset.single_le_sum (f := fun k => |R i k|) (fun k _ => abs_nonneg _)
          (Finset.mem_univ k)
      linarith
    refine (hCR i k y hRk).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (norm_nonneg y) _)
  choose M hM using hi
  refine ⟨∑ i : Fin 3, |M i|, fun i y => (hM i y).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (powWeight_nonneg 3 y)
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |M i|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ i))

end UnforcedLeray.RieszLp
