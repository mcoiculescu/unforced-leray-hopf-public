import UnforcedLeray.Lib.PhaseTrace.Dilation
import UnforcedLeray.Lib.PhaseTrace.Periodize
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Chart tests: spatial tests transported along the comoving chart (block 2F, INF14 T6)

The strong phase trace (tex 7609–7621, unit B0434) says that the comoving pullback
`V(t) = w(τ₀ + t, e^{-t/2} ·)` has weak derivative the pullback of `T₀w`, and that this
"follows by changing variables in distributional tests". This file supplies those tests.
For a time profile `φ`, a spatial test `ψ` and a vector `e ∈ ℂ³`, the chart test is

  `chartTest τ₀ φ ψ e (τ, y) = φ(σ) e^{3σ/2} ψ(e^{σ/2} y) e`,   `σ = τ - τ₀`.

* `driftT_chartTest`: its transpose drift is `chartTest τ₀ (-φ') ψ e`: the drift
  `-∂_τ + ½ y·∇ + 3/2` of `T₀ᵗ` (tex 7318, `driftT`) annihilates `e^{3σ/2} ψ(e^{σ/2} y)`
  and falls on `φ` alone;
* `pairing_chartTest`: changing variables `x = e^{σ/2} y` (`dx = e^{3σ/2} dy`),
  `∫ chartTest(τ₀ + σ, y) · g(y) dy = φ(σ) ∫ ψ(x) e · (dil σ g)(x) dx`;
* `exists_ell`, `eq_zero_of_ell`: the functionals `g ↦ ∫ ψ(x) e · g(x) dx` (`ψ` smooth with
  compact support, `e ∈ ℂ³`) are continuous on `L^q` and separate points.

Status: infrastructure for `Lib/PhaseTrace.lean`; no manuscript unit is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseTrace

open UnforcedLeray.PhaseSpace

/-- The scalar profile of the chart test. -/
def chartScalar (τ₀ : ℝ) (φ : ℝ → ℝ) (ψ : Space → ℝ) (p : ℝ × Space) : ℝ :=
  φ (p.1 - τ₀) * Real.exp (3 * (p.1 - τ₀) / 2) * ψ (Real.exp ((p.1 - τ₀) / 2) • p.2)

/-- **Chart test** `φ(τ - τ₀) e^{3(τ-τ₀)/2} ψ(e^{(τ-τ₀)/2} y) e`. -/
def chartTest (τ₀ : ℝ) (φ : ℝ → ℝ) (ψ : Space → ℝ) (e : CVec3) (p : ℝ × Space) : CVec3 :=
  chartScalar τ₀ φ ψ p • e

/-! ### Calculus -/

/-- A directional derivative read off from the derivative along the line `s ↦ p + s v`. -/
theorem fderiv_apply_of_hasDerivAt {g : ℝ × Space → ℝ} {p v : ℝ × Space}
    (hg : DifferentiableAt ℝ g p) {D : ℝ} (h : HasDerivAt (fun s : ℝ => g (p + s • v)) D 0) :
    fderiv ℝ g p v = D := by
  have hline : HasDerivAt (fun s : ℝ => p + s • v) ((1 : ℝ) • v) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add p
  have h2 := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  rw [one_smul] at h2
  exact h2.unique h

theorem hasDerivAt_chart_time {φ : ℝ → ℝ} {ψ : Space → ℝ} (hφ : Differentiable ℝ φ)
    (hψ : Differentiable ℝ ψ) (σ : ℝ) (y : Space) :
    HasDerivAt (fun σ => φ σ * Real.exp (3 * σ / 2) * ψ (Real.exp (σ / 2) • y))
      (deriv φ σ * Real.exp (3 * σ / 2) * ψ (Real.exp (σ / 2) • y) +
        φ σ * Real.exp (3 * σ / 2) * (3 / 2) * ψ (Real.exp (σ / 2) • y) +
        φ σ * Real.exp (3 * σ / 2) * (Real.exp (σ / 2) * (1 / 2)) *
          fderiv ℝ ψ (Real.exp (σ / 2) • y) y) σ := by
  have h1 : HasDerivAt φ (deriv φ σ) σ := (hφ σ).hasDerivAt
  have h2 : HasDerivAt (fun σ => Real.exp (3 * σ / 2)) (Real.exp (3 * σ / 2) * (3 * 1 / 2)) σ :=
    (((hasDerivAt_id' σ).const_mul 3).div_const 2).exp
  have h3 : HasDerivAt (fun σ => Real.exp (σ / 2) • y) ((Real.exp (σ / 2) * (1 / 2)) • y) σ :=
    ((hasDerivAt_id' σ).div_const 2).exp.smul_const y
  have h4 : HasDerivAt (fun σ => ψ (Real.exp (σ / 2) • y))
      (fderiv ℝ ψ (Real.exp (σ / 2) • y) ((Real.exp (σ / 2) * (1 / 2)) • y)) σ :=
    (hψ _).hasFDerivAt.comp_hasDerivAt σ h3
  refine ((h1.mul h2).mul h4).congr_deriv ?_
  rw [map_smul, smul_eq_mul]
  simp only [Pi.mul_apply]
  ring

theorem hasDerivAt_chart_space {ψ : Space → ℝ} (hψ : Differentiable ℝ ψ) (c b : ℝ)
    (y v : Space) :
    HasDerivAt (fun s : ℝ => c * ψ (b • (y + s • v))) (c * (b * fderiv ℝ ψ (b • y) v)) 0 := by
  have hl : HasDerivAt (fun s : ℝ => b • (y + s • v)) (b • ((1 : ℝ) • v)) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add y).const_smul b
  have h4 := (hψ (b • y)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  refine (h4.const_mul c).congr_deriv ?_
  rw [one_smul, map_smul, smul_eq_mul]

variable {τ₀ : ℝ} {φ : ℝ → ℝ} {ψ : Space → ℝ}

theorem contDiff_chartScalar (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (chartScalar τ₀ φ ψ) := by
  unfold chartScalar
  have hs : ContDiff ℝ ∞ (fun p : ℝ × Space => p.1 - τ₀) := contDiff_fst.sub contDiff_const
  refine ((hφ.comp hs).mul ?_).mul (hψ.comp ?_)
  · exact Real.contDiff_exp.comp ((contDiff_const.mul hs).div_const 2)
  · exact (Real.contDiff_exp.comp (hs.div_const 2)).smul contDiff_snd

theorem fderiv_chartScalar_time (hφ : Differentiable ℝ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hφs : ContDiff ℝ ∞ φ) (p : ℝ × Space) :
    fderiv ℝ (chartScalar τ₀ φ ψ) p (1, 0) =
      deriv φ (p.1 - τ₀) * Real.exp (3 * (p.1 - τ₀) / 2) *
          ψ (Real.exp ((p.1 - τ₀) / 2) • p.2) +
        φ (p.1 - τ₀) * Real.exp (3 * (p.1 - τ₀) / 2) * (3 / 2) *
          ψ (Real.exp ((p.1 - τ₀) / 2) • p.2) +
        φ (p.1 - τ₀) * Real.exp (3 * (p.1 - τ₀) / 2) * (Real.exp ((p.1 - τ₀) / 2) * (1 / 2)) *
          fderiv ℝ ψ (Real.exp ((p.1 - τ₀) / 2) • p.2) p.2 := by
  refine fderiv_apply_of_hasDerivAt
    (((contDiff_chartScalar hφs hψ).differentiable (by simp)) p) ?_
  have h := hasDerivAt_chart_time hφ (hψ.differentiable (by simp)) (p.1 - τ₀) p.2
  have h' := HasDerivAt.comp_const_add (p.1 - τ₀) 0 (by rw [add_zero]; exact h)
  refine h'.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [chartScalar, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_one,
    smul_zero, add_zero]
  ring_nf

theorem fderiv_chartScalar_space (hφs : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (p : ℝ × Space) (v : Space) :
    fderiv ℝ (chartScalar τ₀ φ ψ) p (0, v) =
      φ (p.1 - τ₀) * Real.exp (3 * (p.1 - τ₀) / 2) *
        (Real.exp ((p.1 - τ₀) / 2) * fderiv ℝ ψ (Real.exp ((p.1 - τ₀) / 2) • p.2) v) := by
  refine fderiv_apply_of_hasDerivAt
    (((contDiff_chartScalar hφs hψ).differentiable (by simp)) p) ?_
  have h := hasDerivAt_chart_space (hψ.differentiable (by simp))
    (φ (p.1 - τ₀) * Real.exp (3 * (p.1 - τ₀) / 2)) (Real.exp ((p.1 - τ₀) / 2)) p.2 v
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [chartScalar, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_zero, add_zero]

theorem sum_smul_coordinateVector (v : Space) : ∑ j : Fin 3, v j • coordinateVector j = v := by
  ext i
  simp [coordinateVector, Pi.single_apply]

/-- **The transpose drift of a chart test** falls on the time profile:
`driftT (chartTest τ₀ φ ψ e) = chartTest τ₀ (-φ') ψ e`. -/
theorem driftT_chartTest (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (e : CVec3) :
    driftT (chartTest τ₀ φ ψ e) = chartTest τ₀ (fun σ => -deriv φ σ) ψ e := by
  funext p
  have hd : DifferentiableAt ℝ (chartScalar τ₀ φ ψ) p :=
    ((contDiff_chartScalar hφ hψ).differentiable (by simp)) p
  have hF : fderiv ℝ (chartTest τ₀ φ ψ e) p = (fderiv ℝ (chartScalar τ₀ φ ψ) p).smulRight e :=
    fderiv_smul_const hd e
  have ht := fderiv_chartScalar_time (τ₀ := τ₀) (hφ.differentiable (by simp)) hψ hφ p
  have hsp : ∀ j : Fin 3, fderiv ℝ (chartScalar τ₀ φ ψ) p (0, coordinateVector j) =
      φ (p.1 - τ₀) * Real.exp (3 * (p.1 - τ₀) / 2) *
        (Real.exp ((p.1 - τ₀) / 2) *
          fderiv ℝ ψ (Real.exp ((p.1 - τ₀) / 2) • p.2) (coordinateVector j)) :=
    fun j => fderiv_chartScalar_space hφ hψ p _
  have hrad : ∑ j : Fin 3, p.2 j * (φ (p.1 - τ₀) * Real.exp (3 * (p.1 - τ₀) / 2) *
      (Real.exp ((p.1 - τ₀) / 2) *
        fderiv ℝ ψ (Real.exp ((p.1 - τ₀) / 2) • p.2) (coordinateVector j))) =
      φ (p.1 - τ₀) * Real.exp (3 * (p.1 - τ₀) / 2) * (Real.exp ((p.1 - τ₀) / 2) *
        fderiv ℝ ψ (Real.exp ((p.1 - τ₀) / 2) • p.2) p.2) := by
    have hsum := congrArg (fderiv ℝ ψ (Real.exp ((p.1 - τ₀) / 2) • p.2))
      (sum_smul_coordinateVector p.2)
    rw [map_sum] at hsum
    simp only [map_smul, smul_eq_mul] at hsum
    rw [← hsum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [driftT, dτ, radialT, dy, hF, ContinuousLinearMap.smulRight_apply, ht, hsp,
    chartTest, chartScalar, smul_smul, ← Finset.sum_smul]
  rw [hrad, ← neg_smul, ← add_smul, ← add_smul]
  congr 1
  ring

/-! ### Supports -/

theorem exists_bound_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E] {F' : Type*}
    [Zero F'] {f : E → F'} (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R < ‖x‖ → f x = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall (0 : E)
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  by_contra hne
  have h1 := hR (subset_tsupport f hne)
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  linarith [le_max_left R 0]

theorem timeSupp_chartTest {M : ℝ} (hM : ∀ σ, M < |σ| → φ σ = 0) (e : CVec3) :
    TimeSupp (τ₀ - M) (τ₀ + M) (chartTest τ₀ φ ψ e) := by
  intro τ y hτ
  have h : M < |τ - τ₀| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hτ
    rw [lt_abs]
    rcases hτ with h | h
    · right; linarith
    · left; linarith
  simp [chartTest, chartScalar, hM _ h]

/-- A chart test with smooth compactly supported `φ, ψ` is smooth with bounded spatial
support (`IsPhaseTest 0`). -/
theorem isPhaseTest_chartTest (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (e : CVec3) :
    IsPhaseTest 0 (chartTest τ₀ φ ψ e) where
  smooth := (contDiff_chartScalar hφ hψ).smul contDiff_const
  periodic τ y := by simp
  bounded_support := by
    obtain ⟨M, hM0, hM⟩ := exists_bound_of_hasCompactSupport hφc
    obtain ⟨R, hR0, hR⟩ := exists_bound_of_hasCompactSupport hψc
    refine ⟨R * Real.exp (M / 2), fun τ y hy => ?_⟩
    by_cases hσ : M < ‖τ - τ₀‖
    · simp [chartTest, chartScalar, hM _ hσ]
    · have hσ' : -M ≤ τ - τ₀ := by
        rw [Real.norm_eq_abs, not_lt, abs_le] at hσ; exact hσ.1
      have hz : R < ‖Real.exp ((τ - τ₀) / 2) • y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
        have h1 : Real.exp (-M / 2) ≤ Real.exp ((τ - τ₀) / 2) :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : Real.exp (-M / 2) * Real.exp (M / 2) = 1 := by
          rw [← Real.exp_add, show -M / 2 + M / 2 = 0 by ring, Real.exp_zero]
        have h3 : R < Real.exp (-M / 2) * ‖y‖ := by
          calc R = Real.exp (-M / 2) * (R * Real.exp (M / 2)) := by
                rw [mul_comm R, ← mul_assoc, h2, one_mul]
            _ < Real.exp (-M / 2) * ‖y‖ := by gcongr
        calc R < Real.exp (-M / 2) * ‖y‖ := h3
          _ ≤ Real.exp ((τ - τ₀) / 2) * ‖y‖ := by gcongr
      simp [chartTest, chartScalar, hR _ hz]

/-! ### The pairing of a chart test, by change of variables -/

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- `∫ chartTest(τ₀ + σ, y) · g(y) dy = φ(σ) ∫ ψ(x) e · (dil σ g)(x) dx` (`x = e^{σ/2} y`). -/
theorem pairing_chartTest (e : CVec3) (σ : ℝ) (g : Lp CVec3 q (volume : Measure Space)) :
    ∫ y, dotL (chartTest τ₀ φ ψ e (τ₀ + σ, y)) ((g : Space → CVec3) y) =
      φ σ • ∫ x, ψ x • dotL e ((dil CVec3 q σ g : Space → CVec3) x) := by
  have hsub : τ₀ + σ - τ₀ = σ := by ring
  have hpt : ∀ y, dotL (chartTest τ₀ φ ψ e (τ₀ + σ, y)) ((g : Space → CVec3) y) =
      (φ σ * Real.exp (3 * σ / 2)) •
        (ψ (Real.exp (σ / 2) • y) • dotL e ((g : Space → CVec3) y)) := by
    intro y
    simp only [chartTest, chartScalar, hsub]
    rw [ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.smul_apply, smul_smul]
  simp_rw [hpt]
  rw [integral_smul]
  set K : Space → ℂ := fun x => ψ x • dotL e ((g : Space → CVec3) (dilScale σ • x)) with hK
  have hy1 : ∀ y : Space, dilScale σ • Real.exp (σ / 2) • y = y := by
    intro y
    rw [smul_smul, dilScale, ← Real.exp_add, show -σ / 2 + σ / 2 = 0 by ring, Real.exp_zero,
      one_smul]
  have hKcomp : ∀ y, ψ (Real.exp (σ / 2) • y) • dotL e ((g : Space → CVec3) y) =
      K (Real.exp (σ / 2) • y) := by
    intro y
    show _ = ψ (Real.exp (σ / 2) • y) •
      dotL e ((g : Space → CVec3) (dilScale σ • Real.exp (σ / 2) • y))
    rw [hy1]
  simp_rw [hKcomp]
  rw [Measure.integral_comp_smul (volume : Measure Space) K (Real.exp (σ / 2))]
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  have hint : ∫ x, K x = ∫ x, ψ x • dotL e ((dil CVec3 q σ g : Space → CVec3) x) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_dil σ g] with x hx
    rw [hK, hx]
  rw [hint, hdim, smul_smul]
  congr 1
  rw [abs_of_pos (by positivity), ← Real.exp_nat_mul, ← Real.exp_neg, mul_assoc,
    ← Real.exp_add]
  have : 3 * σ / 2 + -((3 : ℕ) * (σ / 2)) = 0 := by push_cast; ring
  rw [this, Real.exp_zero, mul_one]

/-! ### The separating functionals -/

omit [Fact (1 ≤ q)] in
theorem memLp_testVec (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (e : CVec3)
    (r : ℝ≥0∞) : MemLp (fun x => ψ x • e) r (volume : Measure Space) :=
  (hψ.smul continuous_const).memLp_of_hasCompactSupport (hψc.smul_right)

/-- The functional `g ↦ ∫ ψ(x) e · g(x) dx` is continuous on `L^q`. -/
theorem exists_ell (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (e : CVec3) :
    ∃ L : Lp CVec3 q (volume : Measure Space) →L[ℝ] ℂ,
      ∀ g, L g = ∫ x, ψ x • dotL e ((g : Space → CVec3) x) := by
  refine ⟨((innerPair q) ((memLp_testVec hψ hψc e (conjExp q)).toLp _)).restrictScalars ℝ,
    fun g => ?_⟩
  rw [ContinuousLinearMap.coe_restrictScalars', innerPair_apply]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_testVec hψ hψc e (conjExp q))] with x hx
  rw [hx, ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.smul_apply]

/-- The functionals `g ↦ ∫ ψ(x) e · g(x) dx` separate points of `L^q(ℝ³; ℂ³)`. -/
theorem eq_zero_of_ell (g : Lp CVec3 q (volume : Measure Space))
    (h : ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ e : CVec3,
      ∫ x, ψ x • dotL e ((g : Space → CVec3) x) = 0) : g = 0 := by
  have hloc : LocallyIntegrable (g : Space → CVec3) volume :=
    (Lp.memLp g).locallyIntegrable Fact.out
  have hzero : ∀ᵐ x ∂(volume : Measure Space), (g : Space → CVec3) x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun ψ hψ hψc => ?_
    have hint : Integrable (fun x => ψ x • (g : Space → CVec3) x) :=
      hloc.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    ext i
    have h1 := h ψ hψ hψc (EuclideanSpace.single i 1)
    have hcomp : ∀ x, ψ x • dotL (EuclideanSpace.single i 1) ((g : Space → CVec3) x) =
        (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ) (ψ x • (g : Space → CVec3) x) := by
      intro x
      simp [dotL_apply]
    simp_rw [hcomp] at h1
    rw [ContinuousLinearMap.integral_comp_comm _ hint] at h1
    simpa using h1
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr hzero

end UnforcedLeray.PhaseTrace
