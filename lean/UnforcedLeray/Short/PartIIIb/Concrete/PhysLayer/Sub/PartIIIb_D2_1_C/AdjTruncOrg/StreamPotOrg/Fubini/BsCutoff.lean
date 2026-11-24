import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs

/-!
# Cutoff orthogonality (BSCutoff)

Source `the November 2 reference manuscript` lines 1351-1362.
A solenoidal slice `f ∈ L²` is orthogonal to `∇g` for smooth `g` with decay
`|g| ≤ C/(1+|z|)`, `|∇g| ≤ C/(1+|z|²)`: test with `χ_R g`, where `χ_R` is a radial cutoff
of scale `R`, and let `R → ∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem bsDotL_comm (a b : CVec3) : dotL a b = dotL b a := by
  simp only [dotL_apply, mul_comm]

theorem bsDotL_bound (a b : CVec3) :
    ‖dotL a b‖ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖a‖ * ‖b‖ :=
  ContinuousLinearMap.le_opNorm₂ dotL a b

/-- A function that is constant near `y` has zero spatial gradient at `y`. -/
theorem bsGradS_eq_zero_of_eventually {φ : Space → ℂ} {y : Space} {c : ℂ}
    (h : φ =ᶠ[𝓝 y] fun _ => c) : bsGradS φ y = 0 := by
  have hf : fderiv ℝ φ y = 0 := by
    rw [h.fderiv_eq]
    simp
  unfold bsGradS
  rw [hf]
  ext j
  simp

/-- Product rule for the spatial gradient. -/
theorem bsGradS_mul {χ g : Space → ℂ} {y : Space} (hχ : DifferentiableAt ℝ χ y)
    (hg : DifferentiableAt ℝ g y) :
    bsGradS (fun z => χ z * g z) y = χ y • bsGradS g y + g y • bsGradS χ y := by
  unfold bsGradS
  rw [fderiv_fun_mul hχ hg]
  ext j
  simp [smul_eq_mul]

/-- Chain rule for a dilation `z ↦ c • z`. -/
theorem bsGradS_comp_smul (φ : Space → ℂ) (c : ℝ) (y : Space)
    (hφ : DifferentiableAt ℝ φ (c • y)) :
    bsGradS (fun z => φ (c • z)) y = ((c : ℝ) : ℂ) • bsGradS φ (c • y) := by
  have hL : HasFDerivAt (fun z : Space => c • z) (c • ContinuousLinearMap.id ℝ Space) y := by
    exact ((ContinuousLinearMap.id ℝ Space).hasFDerivAt).const_smul c
  have hcomp := hφ.hasFDerivAt.comp y hL
  unfold bsGradS
  ext j
  have hj := congrArg (fun L : Space →L[ℝ] ℂ => L (EuclideanSpace.single j (1 : ℝ))) hcomp.fderiv
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul] at hj
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [show (fun z : Space => φ (c • z)) = φ ∘ (fun z : Space => c • z) from rfl, hj]
  simp [Complex.real_smul]

/-- The fixed radial bump: `1` on the unit ball, supported in the ball of radius `2`. -/
def bsBump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The complex-valued fixed bump. -/
def bsBumpC (z : Space) : ℂ := ((bsBump z : ℝ) : ℂ)

theorem bsBumpC_contDiff : ContDiff ℝ ∞ bsBumpC :=
  Complex.ofRealCLM.contDiff.comp bsBump.contDiff

theorem bsBumpC_differentiable (z : Space) : DifferentiableAt ℝ bsBumpC z :=
  (bsBumpC_contDiff.differentiable (by simp)) z

theorem bsBumpC_one {z : Space} (h : ‖z‖ ≤ 1) : bsBumpC z = 1 := by
  have hz : z ∈ Metric.closedBall (0 : Space) bsBump.rIn := by
    show z ∈ Metric.closedBall (0 : Space) 1
    simpa using h
  simp [bsBumpC, bsBump.one_of_mem_closedBall hz]

theorem bsBumpC_zero {z : Space} (h : 2 ≤ ‖z‖) : bsBumpC z = 0 := by
  have hz : bsBump.rOut ≤ dist z 0 := by
    show (2 : ℝ) ≤ dist z 0
    simpa using h
  simp [bsBumpC, bsBump.zero_of_le_dist hz]

theorem bsBumpC_norm_le (z : Space) : ‖bsBumpC z‖ ≤ 1 := by
  rw [bsBumpC, Complex.norm_real, Real.norm_of_nonneg bsBump.nonneg]
  exact bsBump.le_one

theorem bsBumpC_hasCompactSupport : HasCompactSupport bsBumpC :=
  bsBump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)

theorem bsGradS_bump_inner {w : Space} (h : ‖w‖ < 1) : bsGradS bsBumpC w = 0 := by
  apply bsGradS_eq_zero_of_eventually (c := 1)
  have hopen : IsOpen {x : Space | ‖x‖ < 1} := isOpen_lt continuous_norm continuous_const
  exact Filter.eventually_of_mem (hopen.mem_nhds h) (fun x hx => bsBumpC_one (le_of_lt hx))

theorem bsGradS_bump_outer {w : Space} (h : 2 < ‖w‖) : bsGradS bsBumpC w = 0 := by
  apply bsGradS_eq_zero_of_eventually (c := 0)
  have hopen : IsOpen {x : Space | 2 < ‖x‖} := isOpen_lt continuous_const continuous_norm
  exact Filter.eventually_of_mem (hopen.mem_nhds h) (fun x hx => bsBumpC_zero (le_of_lt hx))

theorem bsGradS_bump_bounded : ∃ M : ℝ, ∀ w : Space, ‖bsGradS bsBumpC w‖ ≤ M := by
  have hfd : Continuous (fun w : Space => fderiv ℝ bsBumpC w) :=
    bsBumpC_contDiff.continuous_fderiv (by simp)
  have hcont : Continuous (bsGradS bsBumpC) := by
    unfold bsGradS
    refine (PiLp.continuous_toLp 2 _).comp ?_
    exact continuous_pi fun j => hfd.clm_apply continuous_const
  have hsupp : HasCompactSupport (bsGradS bsBumpC) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) 2) ?_
    intro w hw
    apply bsGradS_bump_outer
    have : ¬ ‖w‖ ≤ 2 := by simpa using hw
    exact lt_of_not_ge this
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hsupp
  exact ⟨M, hM⟩

/-- The scaled cutoff `χ_R(z) = ψ(z / R)`. -/
def bsCut (R : ℝ) : Space → ℂ := fun z => bsBumpC ((R⁻¹ : ℝ) • z)

theorem bsCut_contDiff (R : ℝ) : ContDiff ℝ ∞ (bsCut R) :=
  bsBumpC_contDiff.comp (contDiff_id.const_smul (R⁻¹ : ℝ))

theorem bsCut_differentiable (R : ℝ) (z : Space) : DifferentiableAt ℝ (bsCut R) z :=
  (bsCut_contDiff R).differentiable (by simp) z

theorem bsCut_hasCompactSupport {R : ℝ} (hR : 0 < R) : HasCompactSupport (bsCut R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * R)) ?_
  intro z hz
  apply bsBumpC_zero
  have h1 : 2 * R < ‖z‖ := lt_of_not_ge (by simpa using hz)
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  rw [inv_mul_eq_div, le_div_iff₀ hR]
  linarith

theorem bsCut_one {R : ℝ} (hR : 0 < R) {z : Space} (h : ‖z‖ ≤ R) : bsCut R z = 1 := by
  apply bsBumpC_one
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  rw [inv_mul_le_iff₀ hR]
  linarith

theorem bsCut_norm_le (R : ℝ) (z : Space) : ‖bsCut R z‖ ≤ 1 :=
  bsBumpC_norm_le _

theorem bsGradS_cut_inner {R : ℝ} (hR : 0 < R) {z : Space} (h : ‖z‖ < R) :
    bsGradS (bsCut R) z = 0 := by
  unfold bsCut
  rw [bsGradS_comp_smul bsBumpC (R⁻¹) z (bsBumpC_differentiable _), bsGradS_bump_inner]
  · simp
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
    rw [inv_mul_lt_iff₀ hR]
    linarith

theorem bsGradS_cut_outer {R : ℝ} (hR : 0 < R) {z : Space} (h : 2 * R < ‖z‖) :
    bsGradS (bsCut R) z = 0 := by
  unfold bsCut
  rw [bsGradS_comp_smul bsBumpC (R⁻¹) z (bsBumpC_differentiable _), bsGradS_bump_outer]
  · simp
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
    rw [← div_eq_inv_mul, lt_div_iff₀ hR]
    linarith

theorem bsGradS_cut_bound {M : ℝ} (hM : ∀ w : Space, ‖bsGradS bsBumpC w‖ ≤ M) {R : ℝ}
    (hR : 0 < R) (z : Space) : ‖bsGradS (bsCut R) z‖ ≤ R⁻¹ * M := by
  unfold bsCut
  rw [bsGradS_comp_smul bsBumpC (R⁻¹) z (bsBumpC_differentiable _), norm_smul,
    Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  exact mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.2 hR.le)

/-- Spatial gradient of a `C^∞` function is continuous. -/
theorem bsGradS_continuous {φ : Space → ℂ} (hφ : ContDiff ℝ ∞ φ) : Continuous (bsGradS φ) := by
  have hfd : Continuous (fun w : Space => fderiv ℝ φ w) := hφ.continuous_fderiv (by simp)
  unfold bsGradS
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => hfd.clm_apply continuous_const)

/-- `(1+|z|²)⁻¹ ∈ L²(ℝ³)`. -/
theorem bsDecay_memLp : MemLp (fun z : Space => (1 + ‖z‖ ^ 2)⁻¹) 2 volume := by
  have hcont : Continuous (fun z : Space => (1 + ‖z‖ ^ 2)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop) (fun z => by positivity)
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  have hint : Integrable (fun z : Space => (1 + ‖z‖) ^ (-(4 : ℝ))) volume := by
    apply integrable_one_add_norm
    rw [finrank_euclideanSpace_fin]
    norm_num
  refine Integrable.mono' (hint.const_mul 4) (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  have hs0 : 0 ≤ ‖z‖ := norm_nonneg z
  have h1 : (1 + ‖z‖) ^ 2 ≤ 2 * (1 + ‖z‖ ^ 2) := by nlinarith [sq_nonneg (‖z‖ - 1)]
  have h2 : ((1 + ‖z‖) ^ 2) ^ 2 ≤ (2 * (1 + ‖z‖ ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have e : ‖(1 + ‖z‖ ^ 2)⁻¹‖ ^ 2 = ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
  rw [e, Real.norm_of_nonneg (by positivity), show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (by positivity), Real.rpow_natCast]
  have key : ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ ≤ 4 * ((1 + ‖z‖) ^ 4)⁻¹ := by
    rw [show 4 * ((1 + ‖z‖) ^ 4)⁻¹ = 4 / (1 + ‖z‖) ^ 4 by ring,
      show ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ = 1 / (1 + ‖z‖ ^ 2) ^ 2 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h2]
  simpa using key

/-- Hölder bound on a ball: `∫_{B_{2R}} |f| ≤ ‖f‖_{L²} |B_{2R}|^{1/2}`. -/
theorem bsL1Ball {f : Space → CVec3} (hf : MemLp f 2 volume) {R : ℝ} (hR : 0 < R) :
    ∫ z, ‖f z‖ * (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)) z ≤
      Real.sqrt (∫ z, ‖f z‖ ^ 2) *
        Real.sqrt ((2 * R) ^ 3 * (volume (Metric.ball (0 : Space) 1)).toReal) := by
  set Ind := (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)) with hInd
  have hs : MeasurableSet (Metric.closedBall (0 : Space) (2 * R)) := measurableSet_closedBall
  have hf2 : MemLp (fun z => ‖f z‖) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact hf.norm
  have hI2 : MemLp Ind (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact memLp_indicator_const 2 hs (1 : ℝ) (Or.inr (measure_closedBall_lt_top).ne)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun z => norm_nonneg (f z))
    (Filter.Eventually.of_forall fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z) hf2 hI2
  have hfnorm : ∫ z, ‖f z‖ ^ (2 : ℝ) = ∫ z, ‖f z‖ ^ 2 := by
    simp only [Real.rpow_two]
  have hInd2 : ∫ z, Ind z ^ (2 : ℝ) = (volume (Metric.closedBall (0 : Space) (2 * R))).toReal := by
    have e : (fun z => Ind z ^ (2 : ℝ)) = Ind := by
      funext z
      rw [Real.rpow_two]
      by_cases hz : z ∈ Metric.closedBall (0 : Space) (2 * R)
      · simp [hInd, Set.indicator_of_mem hz]
      · simp [hInd, Set.indicator_of_notMem hz]
    rw [e, hInd, integral_indicator_const _ hs]
    simp [measureReal_def]
  have hvol : (volume (Metric.closedBall (0 : Space) (2 * R))).toReal =
      (2 * R) ^ 3 * (volume (Metric.ball (0 : Space) 1)).toReal := by
    rw [Measure.addHaar_closedBall volume 0 (by positivity : (0 : ℝ) ≤ 2 * R),
      finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  calc ∫ z, ‖f z‖ * Ind z ≤ (∫ z, ‖f z‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ z, Ind z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hCS
    _ = Real.sqrt (∫ z, ‖f z‖ ^ 2) *
        Real.sqrt ((2 * R) ^ 3 * (volume (Metric.ball (0 : Space) 1)).toReal) := by
      rw [hfnorm, hInd2, hvol, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- The square-root identity `√((2R)³ V) = R √R √(8V)`. -/
theorem bsSqrt_identity {R V : ℝ} (hR : 0 < R) (hV : 0 ≤ V) :
    Real.sqrt ((2 * R) ^ 3 * V) = R * Real.sqrt R * Real.sqrt (8 * V) := by
  have hsq : (R * Real.sqrt R) ^ 2 = R ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hR.le]
    ring
  rw [show (2 * R) ^ 3 * V = (R * Real.sqrt R) ^ 2 * (8 * V) by rw [hsq]; ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- Pointwise bound for the cutoff term `g · dotL (∇χ_R) f`. -/
theorem bsT2_bound (g : Space → ℂ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ z, ‖g z‖ ≤ c * (1 + ‖z‖)⁻¹) (f : Space → CVec3) {K : ℝ} (hK0 : 0 ≤ K)
    (hbil : ∀ a b : CVec3, ‖dotL a b‖ ≤ K * ‖a‖ * ‖b‖) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ w : Space, ‖bsGradS bsBumpC w‖ ≤ M) {R : ℝ} (hR : 0 < R) (y : Space) :
    ‖g y * dotL (bsGradS (bsCut R) y) (f y)‖ ≤
      (c * R⁻¹) * (K * (R⁻¹ * M)) *
        (‖f y‖ * (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)) y) := by
  have hRHS : 0 ≤ (c * R⁻¹) * (K * (R⁻¹ * M)) *
      (‖f y‖ * (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)) y) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg hc0 (inv_nonneg.2 hR.le))
      (mul_nonneg hK0 (mul_nonneg (inv_nonneg.2 hR.le) hM0))) (mul_nonneg (norm_nonneg _) ?_)
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) y
  by_cases h1 : ‖y‖ < R
  · rw [bsGradS_cut_inner hR h1, map_zero, ContinuousLinearMap.zero_apply, mul_zero, norm_zero]
    exact hRHS
  by_cases h2 : 2 * R < ‖y‖
  · rw [bsGradS_cut_outer hR h2, map_zero, ContinuousLinearMap.zero_apply, mul_zero, norm_zero]
    exact hRHS
  push_neg at h1 h2
  have hmem : y ∈ Metric.closedBall (0 : Space) (2 * R) := by
    rw [mem_closedBall_zero_iff]
    exact h2
  rw [Set.indicator_of_mem hmem, mul_one, norm_mul]
  have hg1 : ‖g y‖ ≤ c * R⁻¹ := by
    refine le_trans (hc y) ?_
    refine mul_le_mul_of_nonneg_left ?_ hc0
    apply inv_anti₀ hR
    linarith [norm_nonneg y]
  have hd1 : ‖dotL (bsGradS (bsCut R) y) (f y)‖ ≤ K * (R⁻¹ * M) * ‖f y‖ := by
    refine le_trans (hbil _ _) ?_
    have hK' := bsGradS_cut_bound hM hR y
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK' hK0) (norm_nonneg _)
  calc ‖g y‖ * ‖dotL (bsGradS (bsCut R) y) (f y)‖
      ≤ (c * R⁻¹) * (K * (R⁻¹ * M) * ‖f y‖) :=
        mul_le_mul hg1 hd1 (norm_nonneg _) (mul_nonneg hc0 (inv_nonneg.2 hR.le))
    _ = c * R⁻¹ * (K * (R⁻¹ * M)) * ‖f y‖ := by ring

/-- **Cutoff orthogonality** (source 1351-1362). -/
theorem bsCutoff : BSCutoff := by
  intro f hf hsol g hg C hgb hGb
  obtain ⟨M0, hM0⟩ := bsGradS_bump_bounded
  set M : ℝ := max M0 0 with hMdef
  have hM : ∀ w : Space, ‖bsGradS bsBumpC w‖ ≤ M := fun w => le_trans (hM0 w) (le_max_left _ _)
  have hM0nn : 0 ≤ M := le_max_right _ _
  set K : ℝ := ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact norm_nonneg (dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)
  have hbil : ∀ a b : CVec3, ‖dotL a b‖ ≤ K * ‖a‖ * ‖b‖ := fun a b => bsDotL_bound a b
  set c : ℝ := |C| with hcdef
  have hcnn : 0 ≤ c := abs_nonneg C
  have hgb' : ∀ z, ‖g z‖ ≤ c * (1 + ‖z‖)⁻¹ := fun z =>
    le_trans (hgb z) (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hGb' : ∀ z, ‖bsGradS g z‖ ≤ c * (1 + ‖z‖ ^ 2)⁻¹ := fun z =>
    le_trans (hGb z) (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hgC : ContDiff ℝ ∞ g := hg
  have hgdiff : ∀ y, DifferentiableAt ℝ g y := fun y => (hgC.differentiable (by simp)) y
  have hG_cont : Continuous (bsGradS g) := bsGradS_continuous hgC
  have hprod : Integrable (fun z : Space => ‖f z‖ * (1 + ‖z‖ ^ 2)⁻¹) volume :=
    MemLp.integrable_mul hf.norm bsDecay_memLp
  have hBmeas : AEStronglyMeasurable (fun z => dotL (bsGradS g z) (f z)) volume :=
    ContinuousLinearMap.aestronglyMeasurable_comp₂ dotL hG_cont.aestronglyMeasurable
      hf.aestronglyMeasurable
  have hBint : Integrable (fun z => dotL (bsGradS g z) (f z)) volume := by
    refine Integrable.mono' (hprod.const_mul (K * c)) hBmeas (Filter.Eventually.of_forall fun z => ?_)
    calc ‖dotL (bsGradS g z) (f z)‖ ≤ K * ‖bsGradS g z‖ * ‖f z‖ := hbil _ _
      _ ≤ K * (c * (1 + ‖z‖ ^ 2)⁻¹) * ‖f z‖ := by
          gcongr
          exact hGb' z
      _ = (K * c) * (‖f z‖ * (1 + ‖z‖ ^ 2)⁻¹) := by ring
  have hBeq : ∫ z, dotL (f z) (bsGradS g z) = ∫ z, dotL (bsGradS g z) (f z) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => bsDotL_comm _ _)
  rw [hBeq]
  -- the identity for each scale `R > 0`
  have hid : ∀ R : ℝ, 0 < R →
      (∫ z, bsCut R z * dotL (bsGradS g z) (f z)) +
        ∫ z, g z * dotL (bsGradS (bsCut R) z) (f z) = 0 := by
    intro R hR
    have hφ : ContDiff ℝ ∞ (fun z => bsCut R z * g z) := (bsCut_contDiff R).mul hgC
    have hφc : HasCompactSupport (fun z => bsCut R z * g z) :=
      (bsCut_hasCompactSupport hR).mul_right
    have h0 := hsol (fun z => bsCut R z * g z) hφ hφc
    have hsplit : ∀ y, dotL (bsGradS (fun z => bsCut R z * g z) y) (f y)
        = bsCut R y * dotL (bsGradS g y) (f y) + g y * dotL (bsGradS (bsCut R) y) (f y) := by
      intro y
      rw [bsGradS_mul (bsCut_differentiable R y) (hgdiff y)]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply, smul_apply, smul_eq_mul]
    have hint1 : Integrable (fun y => bsCut R y * dotL (bsGradS g y) (f y)) volume := by
      refine Integrable.mono' hBint.norm
        ((bsCut_contDiff R).continuous.aestronglyMeasurable.mul hBmeas)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (bsCut_norm_le R y)
    have hT2meas : AEStronglyMeasurable (fun y => g y * dotL (bsGradS (bsCut R) y) (f y)) volume :=
      hgC.continuous.aestronglyMeasurable.mul
        (ContinuousLinearMap.aestronglyMeasurable_comp₂ dotL
          (bsGradS_continuous (bsCut_contDiff R)).aestronglyMeasurable
          hf.aestronglyMeasurable)
    have hT2int : Integrable (fun y => g y * dotL (bsGradS (bsCut R) y) (f y)) volume := by
      have hind : MemLp ((Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)))
          2 volume :=
        memLp_indicator_const 2 measurableSet_closedBall (1 : ℝ)
          (Or.inr (measure_closedBall_lt_top).ne)
      have hbd : Integrable (fun y : Space => (c * R⁻¹) * (K * (R⁻¹ * M)) *
          (‖f y‖ * (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)) y)) volume :=
        ((MemLp.integrable_mul hf.norm hind).const_mul _)
      refine Integrable.mono' hbd hT2meas (Filter.Eventually.of_forall fun y => ?_)
      exact bsT2_bound g hcnn hgb' f hKnn hbil hM0nn hM hR y
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)] at h0
    rw [integral_add hint1 hT2int] at h0
    exact h0
  -- the cutoff term tends to the full integral
  have hDCT : Tendsto (fun R : ℝ => ∫ z, bsCut R z * dotL (bsGradS g z) (f z)) atTop
      (𝓝 (∫ z, dotL (bsGradS g z) (f z))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖dotL (bsGradS g z) (f z)‖)
      (Filter.Eventually.of_forall fun R =>
        (bsCut_contDiff R).continuous.aestronglyMeasurable.mul hBmeas)
      (Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun z => ?_)
      hBint.norm ?_
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (bsCut_norm_le R z)
    · refine Filter.Eventually.of_forall fun z => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (‖z‖ + 1)] with R hR
      have hR0 : 0 < R := by linarith [norm_nonneg z]
      rw [bsCut_one hR0 (by linarith), one_mul]
  -- the error term tends to zero
  have hS : Tendsto (fun R : ℝ => Real.sqrt R) atTop atTop := by
    simpa [Real.sqrt_eq_rpow] using tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  set S : ℝ := ∫ z, ‖f z‖ ^ 2 with hSdef
  set V : ℝ := (volume (Metric.ball (0 : Space) 1)).toReal with hVdef
  set A : ℝ := c * K * M * Real.sqrt S * Real.sqrt (8 * V) with hAdef
  have hB2 : Tendsto (fun R : ℝ => ∫ z, g z * dotL (bsGradS (bsCut R) z) (f z)) atTop (𝓝 0) := by
    have hA : Tendsto (fun R : ℝ => A * (Real.sqrt R)⁻¹) atTop (𝓝 0) := by
      simpa using (hS.inv_tendsto_atTop).const_mul A
    refine squeeze_zero_norm' ?_ hA
    filter_upwards [eventually_gt_atTop 0] with R hR
    have hT2int : Integrable (fun y => g y * dotL (bsGradS (bsCut R) y) (f y)) volume := by
      have hT2meas : AEStronglyMeasurable (fun y => g y * dotL (bsGradS (bsCut R) y) (f y)) volume :=
        hgC.continuous.aestronglyMeasurable.mul
          (ContinuousLinearMap.aestronglyMeasurable_comp₂ dotL
            (bsGradS_continuous (bsCut_contDiff R)).aestronglyMeasurable
            hf.aestronglyMeasurable)
      have hind : MemLp ((Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)))
          2 volume :=
        memLp_indicator_const 2 measurableSet_closedBall (1 : ℝ)
          (Or.inr (measure_closedBall_lt_top).ne)
      have hbd : Integrable (fun y : Space => (c * R⁻¹) * (K * (R⁻¹ * M)) *
          (‖f y‖ * (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)) y)) volume :=
        ((MemLp.integrable_mul hf.norm hind).const_mul _)
      refine Integrable.mono' hbd hT2meas (Filter.Eventually.of_forall fun y => ?_)
      exact bsT2_bound g hcnn hgb' f hKnn hbil hM0nn hM hR y
    have hT2norm := hT2int.norm
    have hind : MemLp ((Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)))
        2 volume :=
      memLp_indicator_const 2 measurableSet_closedBall (1 : ℝ)
        (Or.inr (measure_closedBall_lt_top).ne)
    have hbd : Integrable (fun y : Space => (c * R⁻¹) * (K * (R⁻¹ * M)) *
        (‖f y‖ * (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)) y)) volume :=
      ((MemLp.integrable_mul hf.norm hind).const_mul _)
    calc ‖∫ z, g z * dotL (bsGradS (bsCut R) z) (f z)‖
        ≤ ∫ z, ‖g z * dotL (bsGradS (bsCut R) z) (f z)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, (c * R⁻¹) * (K * (R⁻¹ * M)) *
          (‖f z‖ * (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)) z) :=
          integral_mono hT2norm hbd (fun z => bsT2_bound g hcnn hgb' f hKnn hbil hM0nn hM hR z)
      _ = (c * R⁻¹) * (K * (R⁻¹ * M)) *
          ∫ z, ‖f z‖ * (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => (1 : ℝ)) z := by
          rw [integral_const_mul]
      _ ≤ (c * R⁻¹) * (K * (R⁻¹ * M)) *
          (Real.sqrt S * Real.sqrt ((2 * R) ^ 3 * V)) :=
          mul_le_mul_of_nonneg_left (bsL1Ball hf hR)
            (mul_nonneg (mul_nonneg hcnn (inv_nonneg.2 hR.le))
              (mul_nonneg hKnn (mul_nonneg (inv_nonneg.2 hR.le) hM0nn)))
      _ = A * (Real.sqrt R)⁻¹ := by
          rw [bsSqrt_identity hR (by positivity), hAdef]
          have hkey : R⁻¹ * Real.sqrt R = (Real.sqrt R)⁻¹ := by
            have hs : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
            field_simp
            exact (Real.sq_sqrt hR.le)
          have hkey2 : R⁻¹ * R⁻¹ * (R * Real.sqrt R) = R⁻¹ * Real.sqrt R := by
            field_simp
          calc c * R⁻¹ * (K * (R⁻¹ * M)) * (Real.sqrt S * (R * Real.sqrt R * Real.sqrt (8 * V)))
              = (c * K * M * Real.sqrt S * Real.sqrt (8 * V)) *
                  (R⁻¹ * R⁻¹ * (R * Real.sqrt R)) := by ring
            _ = (c * K * M * Real.sqrt S * Real.sqrt (8 * V)) * (R⁻¹ * Real.sqrt R) := by
                rw [hkey2]
            _ = _ := by rw [hkey]
  have hA0 : Tendsto (fun R : ℝ => ∫ z, bsCut R z * dotL (bsGradS g z) (f z)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun R : ℝ => -(∫ z, g z * dotL (bsGradS (bsCut R) z) (f z))) atTop
        (𝓝 0) := by
      simpa using hB2.neg
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    have := hid R hR
    show -(∫ z, g z * dotL (bsGradS (bsCut R) z) (f z)) = ∫ z, bsCut R z * dotL (bsGradS g z) (f z)
    exact (eq_neg_of_add_eq_zero_left this).symm
  exact tendsto_nhds_unique hDCT hA0

end UnforcedLeray.Short.PartIIIb.Concrete
