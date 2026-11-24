import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_2
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Helper for `PartII-b:F2/2/2`: Smooth `η`-cutoffs on the cylinder

Defines `etaCut R x = etaBump (x.2 / R)` (`R > 0`) and proves:
- `B0579.IsCylTest c (etaCut R)` and `B0579.IsCylTest c (fun x => etaCut R x * E x)` for smooth
  `c`-periodic `E`;
- Uniform `O(1/R)` derivative and Laplacian bounds for `R ≥ 1`;
- Dominated convergence `∫_{cell c} w(x) etaCut R x → ∫_{cell c} w(x)` as `R → ∞` for
  `w ∈ L¹(cell c)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.ZeroCircAux

/-- Standard 1D bump equal to `1` on `[-1, 1]` and `0` outside `(-2, 2)`. -/
def etaBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- Planar `η`-cutoff `θ_R(q, η) = etaBump (η / R)`. -/
def etaCut (R : ℝ) (x : B0579.Plane) : ℝ := etaBump (x.2 / R)

theorem etaCut_nonneg (R : ℝ) (x : B0579.Plane) : 0 ≤ etaCut R x :=
  etaBump.nonneg

theorem etaCut_le_one (R : ℝ) (x : B0579.Plane) : etaCut R x ≤ 1 :=
  etaBump.le_one

theorem etaCut_eq_one {R : ℝ} (hR : 0 < R) {x : B0579.Plane} (hx : |x.2| ≤ R) :
    etaCut R x = 1 := by
  unfold etaCut
  apply etaBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hR]
  change |x.2| / R ≤ 1
  exact (div_le_one hR).2 hx

theorem etaCut_eq_zero {R : ℝ} (hR : 0 < R) {x : B0579.Plane} (hx : 2 * R ≤ |x.2|) :
    etaCut R x = 0 := by
  unfold etaCut
  apply etaBump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hR, le_div_iff₀ hR]
  exact hx

theorem contDiff_etaCut (R : ℝ) : ContDiff ℝ ∞ (etaCut R) :=
  etaBump.contDiff.comp (contDiff_snd.div_const R)

theorem continuous_etaCut (R : ℝ) : Continuous (etaCut R) :=
  (contDiff_etaCut R).continuous

theorem isCylTest_etaCut (c : ℝ) {R : ℝ} (hR : 0 < R) : B0579.IsCylTest c (etaCut R) where
  smooth := contDiff_etaCut R
  periodic _ := rfl
  band := ⟨2 * R, fun _ hx => etaCut_eq_zero hR hx.le⟩

theorem isCylTest_etaCut_mul {c R : ℝ} (hR : 0 < R) {E : B0579.Plane → ℝ}
    (hE_sm : ContDiff ℝ ∞ E) (hE_per : ∀ x : B0579.Plane, E (x.1 + c, x.2) = E x) :
    B0579.IsCylTest c (fun x => etaCut R x * E x) where
  smooth := (contDiff_etaCut R).mul hE_sm
  periodic x := by simp only [etaCut, hE_per x]
  band := ⟨2 * R, fun x hx => by rw [etaCut_eq_zero hR hx.le, zero_mul]⟩

/-- Convert `B0579.IsCylTest` to `UnforcedLeray.Sob.IsCylTest`. -/
theorem toSobCylTest {c : ℝ} {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    UnforcedLeray.Sob.IsCylTest c φ := by
  obtain ⟨M, hM⟩ := hφ.band
  refine ⟨hφ.smooth, fun x => ?_, ⟨M + 1, fun x hx => hM x (by linarith)⟩⟩
  have h1 : x + ((c, 0) : B0579.Plane) = (x.1 + c, x.2) := by ext <;> simp
  rw [h1]
  exact hφ.periodic x

/-- Chain rule for `x ↦ g (x.2 / R)` under `B0579.pd`. -/
private theorem pd_comp_snd_div {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (R : ℝ) (x : B0579.Plane) :
    B0579.pd 0 (fun z : B0579.Plane => g (z.2 / R)) x = 0 ∧
    B0579.pd 1 (fun z : B0579.Plane => g (z.2 / R)) x = R⁻¹ * deriv g (x.2 / R) := by
  let L : B0579.Plane →L[ℝ] ℝ := R⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hfun : (fun z : B0579.Plane => g (z.2 / R)) = fun z => g (L z) := by
    funext z
    simp [L, div_eq_inv_mul]
  have hd_g : HasDerivAt g (deriv g (L x)) (L x) :=
    ((hg.differentiable (by simp)) (L x)).hasDerivAt
  have hfd : HasFDerivAt (fun z : B0579.Plane => g (L z))
      ((deriv g (L x)) • L) x :=
    hd_g.comp_hasFDerivAt x L.hasFDerivAt
  rw [hfun]
  unfold B0579.pd
  rw [hfd.fderiv]
  refine ⟨?_, ?_⟩
  · simp [L, B0579.dir]
  · simp [L, B0579.dir, div_eq_inv_mul, mul_comm]

theorem pd_zero_etaCut (R : ℝ) (x : B0579.Plane) : B0579.pd 0 (etaCut R) x = 0 :=
  (pd_comp_snd_div etaBump.contDiff R x).1

theorem pd_one_etaCut (R : ℝ) (x : B0579.Plane) :
    B0579.pd 1 (etaCut R) x = R⁻¹ * deriv etaBump (x.2 / R) :=
  (pd_comp_snd_div etaBump.contDiff R x).2

theorem lapP_etaCut (R : ℝ) (x : B0579.Plane) :
    lapP (etaCut R) x = (R⁻¹) ^ 2 * deriv (deriv etaBump) (x.2 / R) := by
  unfold lapP
  have h0 : B0579.pd 0 (etaCut R) = fun _ => 0 := funext (pd_zero_etaCut R)
  have h1 : B0579.pd 1 (etaCut R) = fun z => R⁻¹ * deriv etaBump (z.2 / R) :=
    funext (pd_one_etaCut R)
  have hd_bump : ContDiff ℝ ∞ (deriv etaBump) :=
    (contDiff_infty_iff_deriv.1 etaBump.contDiff).2
  have h00 : B0579.pd 0 (B0579.pd 0 (etaCut R)) x = 0 := by
    rw [h0]
    simp [B0579.pd]
  have h11 : B0579.pd 1 (B0579.pd 1 (etaCut R)) x =
      R⁻¹ * (R⁻¹ * deriv (deriv etaBump) (x.2 / R)) := by
    rw [h1]
    unfold B0579.pd
    have hdiff : DifferentiableAt ℝ (fun z : B0579.Plane => deriv etaBump (z.2 / R)) x :=
      ((hd_bump.comp (contDiff_snd.div_const R)).differentiable (by simp)) x
    rw [fderiv_const_mul hdiff]
    simp only [smul_apply, smul_eq_mul]
    congr 1
    exact (pd_comp_snd_div hd_bump R x).2
  rw [h00, h11]
  ring

/-- Global uniform bound on `|deriv etaBump|` and `|deriv (deriv etaBump)|`. -/
theorem exists_etaBump_deriv_bound :
    ∃ C_B : ℝ, 0 ≤ C_B ∧
      (∀ y : ℝ, |deriv etaBump y| ≤ C_B) ∧
      (∀ y : ℝ, |deriv (deriv etaBump) y| ≤ C_B) := by
  have hd1 : ContDiff ℝ ∞ (deriv etaBump) :=
    (contDiff_infty_iff_deriv.1 etaBump.contDiff).2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv etaBump)) :=
    (contDiff_infty_iff_deriv.1 hd1).2
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-2 : ℝ) 2) hd1.continuous.continuousOn
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-2 : ℝ) 2) hd2.continuous.continuousOn
  refine ⟨max (max C1 C2) 0, le_max_right _ _, fun y => ?_, fun y => ?_⟩
  · by_cases hy : |y| ≤ 2
    · have h := hC1 y (abs_le.1 hy)
      rw [Real.norm_eq_abs] at h
      exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
    · push Not at hy
      have hU : IsOpen {z : ℝ | 2 < |z|} :=
        isOpen_lt continuous_const continuous_abs
      have hev : (etaBump : ℝ → ℝ) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hU.mem_nhds hy] with z hz
        apply etaBump.zero_of_le_dist
        rw [Real.dist_eq, sub_zero]
        exact hz.le
      rw [hev.deriv_eq, deriv_const, abs_zero]
      exact le_max_right _ _
  · by_cases hy : |y| ≤ 2
    · have h := hC2 y (abs_le.1 hy)
      rw [Real.norm_eq_abs] at h
      exact h.trans ((le_max_right _ _).trans (le_max_left _ _))
    · push Not at hy
      have hU : IsOpen {z : ℝ | 2 < |z|} :=
        isOpen_lt continuous_const continuous_abs
      have hev1 : deriv (etaBump : ℝ → ℝ) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hU.mem_nhds hy] with z hz
        have hev0 : (etaBump : ℝ → ℝ) =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [hU.mem_nhds hz] with w hw
          apply etaBump.zero_of_le_dist
          rw [Real.dist_eq, sub_zero]
          exact hw.le
        rw [hev0.deriv_eq, deriv_const]
      rw [hev1.deriv_eq, deriv_const, abs_zero]
      exact le_max_right _ _

/-- Uniform `O(1/R)` derivative and Laplacian bounds on `etaCut R` for `R ≥ 1`. -/
theorem exists_etaCut_deriv_bound :
    ∃ C_B : ℝ, 0 ≤ C_B ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : B0579.Plane,
      B0579.pd 0 (etaCut R) x = 0 ∧
      |B0579.pd 1 (etaCut R) x| ≤ C_B / R ∧
      |lapP (etaCut R) x| ≤ C_B / R := by
  obtain ⟨C_B, hCB, hb1, hb2⟩ := exists_etaBump_deriv_bound
  refine ⟨C_B, hCB, fun R hR x => ⟨pd_zero_etaCut R x, ?_, ?_⟩⟩
  · have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
    rw [pd_one_etaCut, abs_mul, abs_of_pos (inv_pos.2 hR0), show C_B / R = R⁻¹ * C_B by ring]
    exact mul_le_mul_of_nonneg_left (hb1 _) (inv_nonneg.2 hR0.le)
  · have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
    have hinv_le1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
    have hsq_le : (R⁻¹) ^ 2 ≤ R⁻¹ := by
      rw [sq]
      exact mul_le_of_le_one_left (inv_nonneg.2 hR0.le) hinv_le1
    rw [lapP_etaCut, abs_mul, abs_of_pos (pow_pos (inv_pos.2 hR0) 2),
      show C_B / R = R⁻¹ * C_B by ring]
    exact mul_le_mul hsq_le (hb2 _) (abs_nonneg _) (inv_nonneg.2 hR0.le)

/-- Product rule for `etaCut R * E`. -/
theorem pd_etaCut_mul (R : ℝ) {E : B0579.Plane → ℝ} (hE : Differentiable ℝ E) (x : B0579.Plane) :
    B0579.pd 0 (fun z => etaCut R z * E z) x = etaCut R x * B0579.pd 0 E x ∧
    B0579.pd 1 (fun z => etaCut R z * E z) x =
      etaCut R x * B0579.pd 1 E x + B0579.pd 1 (etaCut R) x * E x := by
  have hcut : Differentiable ℝ (etaCut R) := (contDiff_etaCut R).differentiable (by simp)
  refine ⟨?_, ?_⟩
  · rw [B0579.pd_mul hcut hE 0 x, pd_zero_etaCut, zero_mul, zero_add]
  · rw [B0579.pd_mul hcut hE 1 x, add_comm]

/-- Dominated convergence: `∫_{cell c} w(x) etaCut R x → ∫_{cell c} w(x)` as `R → ∞`. -/
theorem tendsto_integral_mul_etaCut {c : ℝ} {w : B0579.Plane → ℝ}
    (hw : IntegrableOn w (B0579.cell c) volume) :
    Tendsto (fun R : ℝ => ∫ x in B0579.cell c, w x * etaCut R x) atTop
      (𝓝 (∫ x in B0579.cell c, w x)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖w x‖) ?_ ?_ hw.norm ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R _hR
    exact hw.aestronglyMeasurable.mul
      (continuous_etaCut R).aestronglyMeasurable.restrict
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R _hR
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_of_nonneg (etaCut_nonneg R x)]
    exact mul_le_of_le_one_right (norm_nonneg _) (etaCut_le_one R x)
  · refine Eventually.of_forall fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (|x.2| + 1)] with R hR
    have hR0 : 0 < R := by linarith [abs_nonneg x.2]
    rw [etaCut_eq_one hR0 (by linarith), mul_one]

end UnforcedLeray.Short.IIb.ZeroCircAux
