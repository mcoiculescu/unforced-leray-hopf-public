import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral
import UnforcedLeray.Loc.L09CompactDatum.Vector
import UnforcedLeray.Analysis.Pressure.HeatTest

/-!
# L9 helper: the properties of `u_dss` used for the compact datum

Helper of `Loc/L09CompactDatum.lean` (step L9, `paper/main.tex` lines 430–461, blueprint
units B0717–B0720). `DSSField q u` collects what step L9 uses of the background profile:
smoothness off zero, the DSS law with factor `q = e^{𝒯/2} > 1` (`loc:eq:dss`, line 154),
`|u(x)| ≤ C|x|^{-1}` (line 155), distributional solenoidality across zero, `𝒪`-invariance
and nonvanishing (line 152). `dssField_of_exact` derives it from `IsExactBackground`.

Proved here:
* the DSS law iterated in both directions;
* `‖Dⁿu(y)‖ ≤ Mₙ` for `|y| ≥ 1` and every `n` (DSS rescaling of a compact annulus; the
  package states bounds only for `n ≤ 4`, the heat smoothing of the defect needs all `n`);
* `g u(y) = u(gy)` for `y ≠ 0`, from the a.e. invariance and continuity off zero;
* `div u = 0` pointwise off zero, from the distributional identity (Mathlib's
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`);
* nonzero values of `u` arbitrarily close to zero (line 452: "the DSS law rescales every
  point into that neighborhood").
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.L09

open UnforcedLeray.Blueprint

/-- The properties of `u_dss` used by step L9 (lines 152–156), with DSS factor `q = e^{𝒯/2}`. -/
structure DSSField (q : ℝ) (u : SpatialField) : Prop where
  one_lt : 1 < q
  smooth : ContDiffOn ℝ ∞ u {0}ᶜ
  dss : ∀ x : Space, x ≠ 0 → u (q • x) = q⁻¹ • u x
  bound : ∃ C : ℝ, ∀ x : Space, x ≠ 0 → ‖u x‖ * ‖x‖ ≤ C
  solenoidal : IsSolenoidal u
  symmetric : IsAxisymmetricNoSwirl u
  nonzero : ∃ x : Space, x ≠ 0 ∧ u x ≠ 0

/-- A package background gives a `DSSField` with `q = e^{𝒯/2}`. -/
theorem dssField_of_exact {B : BackgroundCore} (hB : IsExactBackground B) :
    DSSField (Real.exp (B.period / 2)) B.udss where
  one_lt := Real.one_lt_exp_iff.mpr (by have := hB.period_pos; positivity)
  smooth := hB.udss_smooth
  dss := fun x hx => by rw [hB.udss_dss x hx, Real.exp_neg]
  bound := by
    obtain ⟨C, hC⟩ := hB.udss_bounds 0 (by norm_num)
    exact ⟨C, fun x hx => by simpa [norm_iteratedFDeriv_zero] using hC x hx⟩
  solenoidal := hB.udss_solenoidal
  symmetric := hB.udss_symmetric
  nonzero := hB.udss_nonzero

variable {q : ℝ} {u : SpatialField}

namespace DSSField

theorem pos (hu : DSSField q u) : 0 < q := lt_trans one_pos hu.one_lt

theorem continuousOn (hu : DSSField q u) : ContinuousOn u {0}ᶜ := hu.smooth.continuousOn

theorem dss_pow (hu : DSSField q u) (m : ℕ) {x : Space} (hx : x ≠ 0) :
    u (q ^ m • x) = (q ^ m)⁻¹ • u x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hq := hu.pos
    have hx' : q ^ m • x ≠ 0 := smul_ne_zero (pow_ne_zero _ hq.ne') hx
    rw [pow_succ', mul_smul, hu.dss _ hx', ih, smul_smul, ← mul_inv]

theorem dss_inv_pow (hu : DSSField q u) (m : ℕ) {x : Space} (hx : x ≠ 0) :
    u ((q ^ m)⁻¹ • x) = q ^ m • u x := by
  have hq := pow_pos hu.pos m
  have hx' : (q ^ m)⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero hq.ne') hx
  have h := hu.dss_pow m hx'
  rw [smul_smul, mul_inv_cancel₀ hq.ne', one_smul] at h
  rw [h, smul_smul, mul_inv_cancel₀ hq.ne', one_smul]

theorem dss_inv (hu : DSSField q u) {x : Space} (hx : x ≠ 0) : u (q⁻¹ • x) = q • u x := by
  simpa using hu.dss_inv_pow 1 hx

/-- Nonzero values arbitrarily close to zero (line 452). -/
theorem exists_small_ne_zero (hu : DSSField q u) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ y : Space, y ≠ 0 ∧ ‖y‖ < ρ ∧ u y ≠ 0 := by
  obtain ⟨x, hx, hux⟩ := hu.nonzero
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (‖x‖ / ρ) hu.one_lt
  have hqm := pow_pos hu.pos m
  refine ⟨(q ^ m)⁻¹ • x, smul_ne_zero (inv_ne_zero hqm.ne') hx, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hqm.le), inv_mul_lt_iff₀ hqm]
    rw [div_lt_iff₀ hρ] at hm
    linarith
  · rw [hu.dss_inv_pow m hx]
    exact smul_ne_zero hqm.ne' hux

/-- `‖Dⁿu(y)‖ ≤ Mₙ` for `|y| ≥ 1`, every order `n`. -/
theorem iteratedFDeriv_bounded_far (hu : DSSField q u) (n : ℕ) :
    ∃ M : ℝ, ∀ y : Space, 1 ≤ ‖y‖ → ‖iteratedFDeriv ℝ n u y‖ ≤ M := by
  have hq := hu.pos
  set K : Set Space := {y | 1 ≤ ‖y‖ ∧ ‖y‖ ≤ q} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : Space) q).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro y hy; simpa [Metric.mem_closedBall, dist_zero_right] using hy.2
  have hK0 : K ⊆ {0}ᶜ := by
    intro y hy h0
    rw [mem_singleton_iff] at h0
    have := hy.1
    rw [h0, norm_zero] at this
    linarith
  have hcont : ContinuousOn (iteratedFDeriv ℝ n u) {0}ᶜ :=
    ContinuousOn.continuousOn_iteratedFDeriv hu.smooth isOpen_compl_singleton
      (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hK0)
  refine ⟨M, fun y hy => ?_⟩
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near hy hu.one_lt
  have hqm := pow_pos hq m
  set a : ℝ := (q ^ m)⁻¹ with ha
  have ha0 : 0 < a := inv_pos.mpr hqm
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hu.one_lt.le)
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  have hloc : u =ᶠ[𝓝 y] fun w => a • u (a • w) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hy0] with w hw
    rw [ha, hu.dss_inv_pow m hw, smul_smul, inv_mul_cancel₀ hqm.ne', one_smul]
  have hD : iteratedFDeriv ℝ n u y = (a * a ^ n) • iteratedFDeriv ℝ n u (a • y) := by
    rw [(hloc.iteratedFDeriv ℝ n).eq_of_nhds, Kernels.iteratedFDeriv_comp_smul]
  have hz : a • y ∈ K := by
    have hn : ‖a • y‖ = ‖y‖ / q ^ m := by
      rw [norm_smul, Real.norm_of_nonneg ha0.le, ha, inv_mul_eq_div]
    refine ⟨?_, ?_⟩
    · rw [hn, le_div_iff₀ hqm, one_mul]; exact hm1
    · rw [hn, div_le_iff₀ hqm, ← pow_succ']; exact hm2.le
  rw [hD, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ hz)
  calc a * a ^ n * ‖iteratedFDeriv ℝ n u (a • y)‖ ≤ 1 * M := by
        apply mul_le_mul _ (hM _ hz) (norm_nonneg _) zero_le_one
        calc a * a ^ n ≤ 1 * 1 := mul_le_mul ha1 (pow_le_one₀ ha0.le ha1) (by positivity)
              zero_le_one
          _ = 1 := one_mul 1
    _ = M := one_mul M

/-- Pointwise `𝒪`-equivariance off zero. -/
theorem map_isometry (hu : DSSField q u) {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g)
    {y : Space} (hy : y ≠ 0) : u (g y) = g (u y) := by
  have hU : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hc1 : ContinuousOn (fun x => g (u (g.symm x))) {0}ᶜ := by
    refine g.continuous.comp_continuousOn (hu.continuousOn.comp g.symm.continuous.continuousOn ?_)
    intro x hx hx0
    exact hx (by simpa using congrArg g hx0)
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae (hu.symmetric g hg)) hU hc1 hu.continuousOn
  have hgy : g y ∈ ({0}ᶜ : Set Space) := by
    intro h; exact hy (by simpa using h)
  have := heq hgy
  simp only [LinearIsometryEquiv.symm_apply_apply] at this
  exact this.symm

/-- A globally smooth field equal to `u` near every point of norm `> r`. -/
theorem exists_smooth_eq_far (hu : DSSField q u) {r : ℝ} (hr : 0 < r) :
    ∃ v : SpatialField, ContDiff ℝ ∞ v ∧ ∀ y : Space, r < ‖y‖ → v =ᶠ[𝓝 y] u := by
  let b : ContDiffBump (0 : Space) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨fun z => (1 - b z) • u z, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z = 0
    · have hloc : (fun z => (1 - b z) • u z) =ᶠ[𝓝 z] fun _ => (0 : Space) := by
        filter_upwards [Metric.ball_mem_nhds z (show 0 < r / 4 by positivity)] with w hw
        rw [hz] at hw
        have : b w = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hloc
    · exact (contDiffAt_const.sub b.contDiff.contDiffAt).smul
        (hu.smooth.contDiffAt (isOpen_compl_singleton.mem_nhds hz))
  · intro y hy
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
      (show r / 2 < ‖y‖ by linarith)] with w hw
    have : b w = 0 := b.zero_of_le_dist (by
      show r / 2 ≤ dist w 0
      rw [dist_zero_right]; exact le_of_lt hw)
    simp [this]

theorem fderiv_coord {f : SpatialField} {x : Space} (hf : DifferentiableAt ℝ f x) (i : Fin 3)
    (v : Space) : fderiv ℝ (fun z => f z i) x v = fderiv ℝ f x v i := by
  have h := ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt (x := f x)).comp x
    hf.hasFDerivAt
  rw [show (fun z => f z i) = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ f from rfl, h.fderiv]
  simp

/-- **Pointwise solenoidality off zero.** -/
theorem div_eq_zero (hu : DSSField q u) {y : Space} (hy : y ≠ 0) :
    ∑ j : Fin 3, fderiv ℝ u y (coordinateVector j) j = 0 := by
  set g : Space → ℝ := fun z => ∑ j : Fin 3, fderiv ℝ u z (coordinateVector j) j with hgdef
  have hU : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hfd : ContinuousOn (fun z => fderiv ℝ u z) {0}ᶜ :=
    hu.smooth.continuousOn_fderiv_of_isOpen hU (by simp)
  have hg : ContinuousOn g {0}ᶜ := by
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_continuousOn
      ((ContinuousLinearMap.apply ℝ Space (coordinateVector j)).continuous.comp_continuousOn hfd)
  have hint : ∀ φ : Space → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ {0}ᶜ →
      ∫ x, φ x • g x = 0 := by
    intro φ hφs hφc hφU
    have hT : IsSpatialTest φ := ⟨hφs, hφc⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isClosed_tsupport φ).isOpen_compl 0
      (fun h => hφU h rfl)
    have hfar : ∀ z ∈ tsupport φ, ε / 2 < ‖z‖ := by
      intro z hz
      by_contra hlt
      rw [not_lt] at hlt
      exact hball (by rw [Metric.mem_ball, dist_zero_right]; linarith) hz
    obtain ⟨v, hv, hvu⟩ := hu.exists_smooth_eq_far (show 0 < ε / 2 by positivity)
    have hvcomp : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z => v z i) := fun i =>
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hv
    have hzero : ∀ z, z ∉ tsupport φ → ∀ i, spatialTestDerivative i φ z = 0 := by
      intro z hz i
      have : fderiv ℝ φ z = 0 := by
        by_contra h
        exact hz (support_fderiv_subset ℝ h)
      simp [spatialTestDerivative, this]
    -- the integrand of the solenoidality identity does not see the modification
    have hA : (fun x => ∑ i : Fin 3, v x i * spatialTestDerivative i φ x) =
        fun x => ∑ i : Fin 3, u x i * spatialTestDerivative i φ x := by
      funext z
      by_cases hz : z ∈ tsupport φ
      · rw [(hvu z (hfar z hz)).eq_of_nhds]
      · simp [hzero z hz]
    have hB : (fun x => φ x • g x) =
        fun x => ∑ i : Fin 3, spatialTestDerivative i (fun z => v z i) x * φ x := by
      funext z
      by_cases hz : z ∈ tsupport φ
      · have hloc := hvu z (hfar z hz)
        have hdv : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
        simp only [hgdef, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [spatialTestDerivative, fderiv_coord hdv, hloc.fderiv_eq, mul_comm]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    have hI1 : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        Integrable (fun x => spatialTestDerivative i (fun z => v z i) x * φ x) := by
      intro i _
      exact ((PressureAnalysis.contDiff_spatialTestDerivative (hvcomp i) i).continuous.mul
        hφs.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have hI2 : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        Integrable (fun x => v x i * spatialTestDerivative i φ x) := by
      intro i _
      exact ((hvcomp i).continuous.mul (hT.derivative i).smooth.continuous).integrable_of_hasCompactSupport
        (hT.derivative i).compact.mul_left
    rw [hB, integral_finsetSum _ hI1]
    have hibp : ∀ i : Fin 3, (∫ x, spatialTestDerivative i (fun z => v z i) x * φ x) =
        -(∫ x, v x i * spatialTestDerivative i φ x) := fun i =>
      PressureAnalysis.integral_partial_mul_test (hvcomp i) hT i
    simp_rw [hibp]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ hI2, hA, hu.solenoidal.identity φ hT,
      neg_zero]
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hg.locallyIntegrableOn hU.measurableSet) hint
  have heq : EqOn g 0 {0}ᶜ :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr hae) hU hg continuousOn_const
  exact heq hy

end DSSField

end UnforcedLeray.L09
