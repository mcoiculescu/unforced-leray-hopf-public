import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_2_1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Slicewise spatial integration by parts (helper of `PartII-b:S3/1/1/2/1/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523.

Copy of the slice integration-by-parts lemmas of
`HigherOrderPhaseDeriv/ProjectedEvolutionTower/PointwiseDeriv/WeakIBP.lean` (whose current build
fails on an ambiguous `realC_eq_ofReV`), with the name disambiguated.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.B0414 UnforcedLeray.Blueprint
  UnforcedLeray.RieszLp

namespace BaseRepIBP

open PointwiseDerivSub HigherPhaseSub ProjectedEvolutionSub PhaseDerivStepSub LerayPairSolAux

theorem hasCompactSupport_of_ball_zero {E : Type*} [Zero E] [TopologicalSpace E]
    {f : Space → E} (R : ℝ) (hR : ∀ y : Space, R < ‖y‖ → f y = 0) :
    HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) R)
    fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  exact hy (hR y (not_le.mp hlt))

/-- For any smooth `K : ℝ × Space → ℂ` vanishing outside `‖y‖ ≤ R` on slice `t`, the spatial
partial derivative `dy j K (t, y)` is integrable on `Space` and integrates to `0`. -/
theorem integral_slice_dy_eq_zero {K : ℝ × Space → ℂ} (hK : ContDiff ℝ ∞ K)
    {R : ℝ} (t : ℝ) (hR : ∀ y : Space, R < ‖y‖ → K (t, y) = 0) (j : Fin 3) :
    Integrable (fun y : Space => dy j K (t, y)) volume ∧
      ∫ y : Space, dy j K (t, y) = 0 := by
  have hd : Differentiable ℝ K := hK.differentiable (by simp)
  have hsl : ContDiff ℝ ∞ (fun y => K (t, y)) := hK.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (fun y => K (t, y)) := hasCompactSupport_of_ball_zero R hR
  have hpt : ∀ y : Space, dy j K (t, y) = fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) := by
    intro y
    have hcomp : HasFDerivAt (fun x : Space => K (t, x))
        ((fderiv ℝ K (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
      (hd (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
    change fderiv ℝ K (t, y) (0, coordinateVector j) = _
    rw [hcomp.fderiv]
    rfl
  simp_rw [hpt]
  have hcd : HasCompactSupport fun y => fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) :=
    hc.fderiv_apply ℝ (coordinateVector j)
  have hcont' : Continuous fun y => fderiv ℝ (fun x => K (t, x)) y (coordinateVector j) :=
    (hsl.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint : Integrable (fun y => fderiv ℝ (fun x => K (t, x)) y (coordinateVector j)) volume :=
    hcont'.integrable_of_hasCompactSupport hcd
  refine ⟨hint, ?_⟩
  have h0 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Space => (1 : ℂ)) (g := fun x => K (t, x)) (v := coordinateVector j)
    (by simp) (by simpa using hint)
    (by simpa using hsl.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _) (fun x _ => (hsl.differentiable (by simp)) x)
  simpa using h0

/-- Smoothness of `dotFn A B` when `A, B : ℝ × Space → CVec3` are `C^∞`. -/
theorem contDiff_dotFn {A B : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (dotFn A B) :=
  dotLR.isBoundedBilinearMap.contDiff.comp (hA.prodMk hB)

/-- Time-independent lift `(s, y) ↦ realC (F y)` of a spatial field `F : SpatialField`. -/
def constRealCLift (F : SpatialField) (p : ℝ × Space) : CVec3 :=
  realC (F p.2)

theorem contDiff_constRealCLift {F : SpatialField} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (constRealCLift F) := by
  have heq : constRealCLift F = fun p : ℝ × Space => ofReV (F p.2) := by
    funext p
    exact PointwiseDerivSub.realC_eq_ofReV (F p.2)
  rw [heq]
  exact ofReV.contDiff.comp (hF.comp contDiff_snd)

theorem hasFDerivAt_constRealCLift {F : SpatialField} (hF : ContDiff ℝ ∞ F) (p : ℝ × Space) :
    HasFDerivAt (constRealCLift F)
      ((ofReV.comp (fderiv ℝ F p.2)).comp (ContinuousLinearMap.snd ℝ ℝ Space)) p := by
  have heq : constRealCLift F = fun q : ℝ × Space => ofReV (F q.2) := by
    funext q
    exact PointwiseDerivSub.realC_eq_ofReV (F q.2)
  rw [heq]
  exact (ofReV.hasFDerivAt.comp p.2 ((hF.differentiable (by simp) p.2).hasFDerivAt)).comp
    p hasFDerivAt_snd

theorem dτ_constRealCLift {F : SpatialField} (hF : ContDiff ℝ ∞ F) (p : ℝ × Space) :
    dτ (constRealCLift F) p = 0 := by
  unfold dτ
  rw [(hasFDerivAt_constRealCLift hF p).fderiv]
  simp

theorem dy_constRealCLift {F : SpatialField} (hF : ContDiff ℝ ∞ F) (j : Fin 3) (p : ℝ × Space) :
    dy j (constRealCLift F) p = realC (spatialPartial j F p.2) := by
  unfold dy
  rw [(hasFDerivAt_constRealCLift hF p).fderiv]
  change ofReV (fderiv ℝ F p.2 (coordinateVector j)) = realC (spatialPartial j F p.2)
  rw [← PointwiseDerivSub.realC_eq_ofReV]
  rfl

theorem dy_dy_constRealCLift {F : SpatialField} (hF : ContDiff ℝ ∞ F) (j : Fin 3) (p : ℝ × Space) :
    dy j (dy j (constRealCLift F)) p =
      realC (dirSpatialJet F [EuclideanSpace.single j 1, EuclideanSpace.single j 1] p.2) := by
  have heq : dy j (constRealCLift F) = constRealCLift (spatialPartial j F) := by
    funext q
    exact dy_constRealCLift hF j q
  have hPj : ContDiff ℝ ∞ (spatialPartial j F) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hF [EuclideanSpace.single j 1]
  rw [heq, dy_constRealCLift hPj j p]
  rfl

theorem radialT_constRealCLift {F : SpatialField} (hF : ContDiff ℝ ∞ F) (p : ℝ × Space) :
    radialT (constRealCLift F) p = realC (spatialRadialDrift F p.2) := by
  unfold radialT
  simp_rw [dy_constRealCLift hF, PointwiseDerivSub.realC_eq_ofReV]
  rw [spatialRadialDrift_eq_sum_coord_spatialPartial F p.2, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ofReV.map_smul]

theorem lapT_constRealCLift {F : SpatialField} (hF : ContDiff ℝ ∞ F) (p : ℝ × Space) :
    lapT (constRealCLift F) p = realC (spatialLaplacian F p.2) := by
  unfold lapT spatialLaplacian
  simp_rw [dy_dy_constRealCLift hF, PointwiseDerivSub.realC_eq_ofReV]
  rw [← map_sum]

theorem L0_constRealCLift (ν : ℝ) {F : SpatialField} (hF : ContDiff ℝ ∞ F) (p : ℝ × Space) :
    L0 ν (constRealCLift F) p = -realC (spatialProjectedLin ν F p.2) := by
  unfold L0 T0 spatialProjectedLin spatialDiffReact
  rw [dτ_constRealCLift hF p, radialT_constRealCLift hF p, lapT_constRealCLift hF p]
  change (0 - (1 / 2 : ℝ) • realC (spatialRadialDrift F p.2)) -
      ν • realC (spatialLaplacian F p.2) - (1 / 2 : ℝ) • realC (F p.2) =
    -realC (((1 / 2 : ℝ) • spatialRadialDrift F +
      (ν • spatialLaplacian F + (1 / 2 : ℝ) • F)) p.2)
  simp only [Pi.add_apply, Pi.smul_apply, PointwiseDerivSub.realC_eq_ofReV, map_add, map_smul]
  module

/-- A spatial derivative of a field vanishing for `‖y‖ > R` vanishes there too. -/
theorem dy_eq_zero_of_bound {Φ : ℝ × Space → CVec3} {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → Φ (τ, y) = 0) (j : Fin 3) (τ : ℝ) (y : Space) (hy : R < ‖y‖) :
    dy j Φ (τ, y) = 0 := by
  have hev : Φ =ᶠ[𝓝 ((τ, y) : ℝ × Space)] fun _ => 0 := by
    have hopen : IsOpen {q : ℝ × Space | R < ‖q.2‖} :=
      isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
    filter_upwards [hopen.mem_nhds (show ((τ, y) : ℝ × Space) ∈ {q : ℝ × Space | R < ‖q.2‖}
      from hy)] with q hq
    exact hR q.1 q.2 hq
  simp [dy, hev.fderiv_eq]

/-- Continuity and compact support of `y ↦ dotL (Ψ (t, y)) (realC (F y))` for a phase test `Ψ`
and continuous spatial field `F`. -/
theorem integrable_slice_dotL_realC {P : ℝ} {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ)
    (t : ℝ) {F : SpatialField} (hF : Continuous F) :
    Integrable (fun y : Space => dotL (Ψ (t, y)) (realC (F y))) volume := by
  obtain ⟨R, hR⟩ := hΨ.bounded_support
  have hcont : Continuous (fun y : Space => dotL (Ψ (t, y)) (realC (F y))) := by
    have h1 : Continuous (fun y : Space => dotL (Ψ (t, y))) :=
      dotL.continuous.comp (hΨ.smooth.continuous.comp (Continuous.prodMk_right t))
    have h2 : Continuous (fun y : Space => realC (F y)) := by
      simp_rw [PointwiseDerivSub.realC_eq_ofReV]
      exact ofReV.continuous.comp hF
    exact h1.clm_apply h2
  have hcs : HasCompactSupport (fun y : Space => dotL (Ψ (t, y)) (realC (F y))) :=
    hasCompactSupport_of_ball_zero R fun y hy => by simp [hR t y hy]
  exact hcont.integrable_of_hasCompactSupport hcs

/-- Slicewise Laplacian integration by parts: `∫ ΔΦ(t, y) · F(y) dy = ∫ Φ(t, y) · ΔF(y) dy`. -/
theorem slice_integral_lapT_eq {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    (∫ y : Space, dotL (lapT Φ (t, y)) (realC (F y))) =
      ∫ y : Space, dotL (Φ (t, y)) (realC (spatialLaplacian F y)) := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  let u : ℝ × Space → CVec3 := constRealCLift F
  have hu : ContDiff ℝ ∞ u := contDiff_constRealCLift hF
  have hpt : ∀ (j : Fin 3) (q : ℝ × Space),
      dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) q =
        dotL (dy j (dy j Φ) q) (u q) - dotL (Φ q) (dy j (dy j u) q) := by
    intro j q
    have hd1 : Differentiable ℝ (dotFn (dy j Φ) u) :=
      (contDiff_dotFn (contDiff_dy hΦ.smooth j) hu).differentiable (by simp)
    have hd2 : Differentiable ℝ (dotFn Φ (dy j u)) :=
      (contDiff_dotFn hΦ.smooth (contDiff_dy hu j)).differentiable (by simp)
    have hsub : dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) q =
        dy j (dotFn (dy j Φ) u) q - dy j (dotFn Φ (dy j u)) q := by
      have he : (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) =
          dotFn (dy j Φ) u - dotFn Φ (dy j u) := rfl
      simp only [dy]
      rw [he, fderiv_sub (hd1 q) (hd2 q), ContinuousLinearMap.sub_apply]
    rw [hsub, dy_dotFn ((contDiff_dy hΦ.smooth j).differentiable (by simp))
      (hu.differentiable (by simp)) j q,
      dy_dotFn (hΦ.smooth.differentiable (by simp)) ((contDiff_dy hu j).differentiable (by simp))
        j q]
    ring
  have hN : ∀ j : Fin 3,
      Integrable (fun y : Space => dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) (t, y))
        volume ∧
        (∫ y : Space, dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) (t, y)) = 0 := by
    intro j
    have hK : ContDiff ℝ ∞ (fun p : ℝ × Space => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) :=
      (contDiff_dotFn (contDiff_dy hΦ.smooth j) hu).sub (contDiff_dotFn hΦ.smooth (contDiff_dy hu j))
    have hdyΦ : ∀ y : Space, R < ‖y‖ → dy j Φ (t, y) = 0 :=
      fun y hy => dy_eq_zero_of_bound hR j t y hy
    exact integral_slice_dy_eq_zero (R := R) hK t
      (fun y hy => by simp [dotFn, hR t y hy, hdyΦ y hy]) j
  have hdd : ∀ j : Fin 3, IsPhaseTest P (dy j (dy j Φ)) := fun j => (hΦ.dy j).dy j
  have hFlap : ∀ j : Fin 3, Continuous
      (dirSpatialJet F [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) := fun j =>
    (JointSmoothSub.contDiff_infty_dirSpatialJet hF _).continuous
  have hI1 : ∀ j : Fin 3, Integrable (fun y : Space => dotL (dy j (dy j Φ) (t, y)) (u (t, y))) :=
    fun j => integrable_slice_dotL_realC (hdd j) t hF.continuous
  have hI2 : ∀ j : Fin 3, Integrable (fun y : Space => dotL (Φ (t, y)) (dy j (dy j u) (t, y))) := by
    intro j
    have h := integrable_slice_dotL_realC hΦ t (hFlap j)
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [dy_dy_constRealCLift hF j (t, y)]
  have hj : ∀ j : Fin 3, ∫ y : Space, dotL (dy j (dy j Φ) (t, y)) (u (t, y)) =
      ∫ y : Space, dotL (Φ (t, y)) (dy j (dy j u) (t, y)) := by
    intro j
    have h0 := (hN j).2
    simp_rw [hpt j] at h0
    rw [integral_sub (hI1 j) (hI2 j)] at h0
    exact sub_eq_zero.1 h0
  have hL : (fun y : Space => dotL (lapT Φ (t, y)) (realC (F y))) =
      fun y => ∑ j : Fin 3, dotL (dy j (dy j Φ) (t, y)) (u (t, y)) := by
    funext y
    simp only [lapT, map_sum, ContinuousLinearMap.sum_apply]
    rfl
  have hR' : (fun y : Space => dotL (Φ (t, y)) (realC (spatialLaplacian F y))) =
      fun y => ∑ j : Fin 3, dotL (Φ (t, y)) (dy j (dy j u) (t, y)) := by
    funext y
    rw [← map_sum]
    have h := lapT_constRealCLift hF (t, y)
    simp only at h
    rw [← h]
    rfl
  rw [hL, hR', integral_finsetSum _ fun j _ => hI1 j, integral_finsetSum _ fun j _ => hI2 j]
  exact Finset.sum_congr rfl fun j _ => hj j

/-- Slicewise convection IBP: when `F : SpatialField` is smooth and solenoidal (`IsSolenoidal F`),
`∫ y, dotL (advT (fun x => realC (U₀ x.1 x.2)) Φ (t, y)) (realC (U₀ t y)) = -∫ y, dotL (Φ (t, y)) (realC (spatialConvect (U₀ t) (U₀ t) y))`. -/
theorem slice_integral_advT_eq_neg_spatialConvect {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) {U₀ : ℝ → SpatialField}
    (hU₀ : ∀ τ : ℝ, ContDiff ℝ ∞ (U₀ τ)) (hSol : ∀ τ : ℝ, IsSolenoidal (U₀ τ)) (t : ℝ) :
    (∫ y : Space, dotL (advT (fun x => realC (U₀ x.1 x.2)) Φ (t, y)) (realC (U₀ t y))) =
      -∫ y : Space, dotL (Φ (t, y)) (realC (spatialConvect (U₀ t) (U₀ t) y)) := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  let F : SpatialField := U₀ t
  have hF : ContDiff ℝ ∞ F := hU₀ t
  let u : ℝ × Space → CVec3 := constRealCLift F
  have hu : ContDiff ℝ ∞ u := contDiff_constRealCLift hF
  let φ : Space → ℂ := fun y => dotFn Φ u (t, y)
  have hφ_smooth : ContDiff ℝ ∞ φ :=
    (contDiff_dotFn hΦ.smooth hu).comp (contDiff_const.prodMk contDiff_id)
  have hφ_cs : HasCompactSupport φ :=
    hasCompactSupport_of_ball_zero R fun y hy => by simp [φ, dotFn, hR t y hy]
  let φ_re : Space → ℝ := fun y => (φ y).re
  let φ_im : Space → ℝ := fun y => (φ y).im
  have hφ_re : IsSpatialTest φ_re :=
    ⟨Complex.reCLM.contDiff.comp hφ_smooth, hφ_cs.comp_left Complex.reCLM.map_zero⟩
  have hφ_im : IsSpatialTest φ_im :=
    ⟨Complex.imCLM.contDiff.comp hφ_smooth, hφ_cs.comp_left Complex.imCLM.map_zero⟩
  have hφ_deriv : ∀ (j : Fin 3) (y : Space),
      dotL (dy j Φ (t, y)) (realC (F y)) + dotL (Φ (t, y)) (realC (spatialPartial j F y)) =
        ((spatialTestDerivative j φ_re y : ℝ) : ℂ) +
          Complex.I * ((spatialTestDerivative j φ_im y : ℝ) : ℂ) := by
    intro j y
    have hd_dot : dy j (dotFn Φ u) (t, y) =
        dotL (dy j Φ (t, y)) (realC (F y)) + dotL (Φ (t, y)) (realC (spatialPartial j F y)) := by
      rw [dy_dotFn (hΦ.smooth.differentiable (by simp)) (hu.differentiable (by simp)) j (t, y),
        dy_constRealCLift hF j (t, y)]
      rfl
    have hd_slice : dy j (dotFn Φ u) (t, y) = fderiv ℝ φ y (coordinateVector j) := by
      have hd : Differentiable ℝ (dotFn Φ u) :=
        (contDiff_dotFn hΦ.smooth hu).differentiable (by simp)
      have hcomp : HasFDerivAt φ
          ((fderiv ℝ (dotFn Φ u) (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
        (hd (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
      change fderiv ℝ (dotFn Φ u) (t, y) (0, coordinateVector j) = _
      rw [hcomp.fderiv]
      rfl
    have hd_re : spatialTestDerivative j φ_re y = (fderiv ℝ φ y (coordinateVector j)).re := by
      have hcomp : HasFDerivAt φ_re (Complex.reCLM.comp (fderiv ℝ φ y)) y :=
        Complex.reCLM.hasFDerivAt.comp y ((hφ_smooth.differentiable (by simp)) y).hasFDerivAt
      change fderiv ℝ φ_re y (coordinateVector j) = _
      rw [hcomp.fderiv]
      rfl
    have hd_im : spatialTestDerivative j φ_im y = (fderiv ℝ φ y (coordinateVector j)).im := by
      have hcomp : HasFDerivAt φ_im (Complex.imCLM.comp (fderiv ℝ φ y)) y :=
        Complex.imCLM.hasFDerivAt.comp y ((hφ_smooth.differentiable (by simp)) y).hasFDerivAt
      change fderiv ℝ φ_im y (coordinateVector j) = _
      rw [hcomp.fderiv]
      rfl
    rw [← hd_dot, hd_slice, hd_re, hd_im, mul_comm Complex.I]
    exact (Complex.re_add_im (fderiv ℝ φ y (coordinateVector j))).symm
  have hpt : ∀ y : Space,
      dotL (advT (fun x => realC (U₀ x.1 x.2)) Φ (t, y)) (realC (F y)) +
        dotL (Φ (t, y)) (realC (spatialConvect F F y)) =
      ((∑ j : Fin 3, F y j * spatialTestDerivative j φ_re y : ℝ) : ℂ) +
        Complex.I * ((∑ j : Fin 3, F y j * spatialTestDerivative j φ_im y : ℝ) : ℂ) := by
    intro y
    have hadv : dotL (advT (fun x => realC (U₀ x.1 x.2)) Φ (t, y)) (realC (F y)) =
        ∑ j : Fin 3, ((F y j : ℝ) : ℂ) * dotL (dy j Φ (t, y)) (realC (F y)) := by
      unfold advT
      rw [map_sum, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, realC_apply]
    have hconv : dotL (Φ (t, y)) (realC (spatialConvect F F y)) =
        ∑ j : Fin 3, ((F y j : ℝ) : ℂ) * dotL (Φ (t, y)) (realC (spatialPartial j F y)) := by
      rw [spatialConvect_eq_sum F F y, PointwiseDerivSub.realC_eq_ofReV, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ofReV.map_smul, ← PointwiseDerivSub.realC_eq_ofReV, ContinuousLinearMap.map_smul_of_tower,
        Complex.real_smul]
    rw [hadv, hconv, ← Finset.sum_add_distrib]
    simp_rw [← mul_add, hφ_deriv]
    push_cast
    simp only [Fin.sum_univ_three]
    ring
  have hint_adv : Integrable (fun y : Space =>
      dotL (advT (fun x => realC (U₀ x.1 x.2)) Φ (t, y)) (realC (F y))) volume := by
    have heq : (fun y : Space => dotL (advT (fun x => realC (U₀ x.1 x.2)) Φ (t, y)) (realC (F y))) =
        fun y : Space => ∑ j : Fin 3, ((F y j : ℝ) : ℂ) * dotL (dy j Φ (t, y)) (realC (F y)) := by
      funext y
      unfold advT
      rw [map_sum, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, realC_apply]
    rw [heq]
    refine integrable_finsetSum _ fun j _ => ?_
    have hFj : Continuous (fun y : Space => ((F y j : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous).comp hF.continuous)
    have hdy_cont : Continuous (fun y : Space => dotL (dy j Φ (t, y)) (realC (F y))) := by
      have h1 : Continuous (fun y : Space => dotL (dy j Φ (t, y))) :=
        dotL.continuous.comp (((hΦ.dy j).smooth.continuous).comp (Continuous.prodMk_right t))
      have h2 : Continuous (fun y : Space => realC (F y)) := by
        simp_rw [PointwiseDerivSub.realC_eq_ofReV]
        exact ofReV.continuous.comp hF.continuous
      exact h1.clm_apply h2
    have hcs : HasCompactSupport (fun y : Space => ((F y j : ℝ) : ℂ) * dotL (dy j Φ (t, y)) (realC (F y))) := by
      obtain ⟨R', hR'⟩ := (hΦ.dy j).bounded_support
      exact hasCompactSupport_of_ball_zero R' fun y hy => by simp [hR' t y hy]
    exact (hFj.mul hdy_cont).integrable_of_hasCompactSupport hcs
  have hint_conv : Integrable (fun y : Space => dotL (Φ (t, y)) (realC (spatialConvect F F y))) volume :=
    integrable_slice_dotL_realC hΦ t (contDiff_infty_spatialConvect hF hF).continuous
  have hint_re : Integrable (fun y : Space => ∑ j : Fin 3, F y j * spatialTestDerivative j φ_re y) volume :=
    (hSol t).integrable φ_re hφ_re
  have hint_im : Integrable (fun y : Space => ∑ j : Fin 3, F y j * spatialTestDerivative j φ_im y) volume :=
    (hSol t).integrable φ_im hφ_im
  have hsum_zero :
      (∫ y : Space, dotL (advT (fun x => realC (U₀ x.1 x.2)) Φ (t, y)) (realC (F y))) +
        (∫ y : Space, dotL (Φ (t, y)) (realC (spatialConvect F F y))) = 0 := by
    have hre : Integrable (fun y : Space =>
        ((∑ j : Fin 3, F y j * spatialTestDerivative j φ_re y : ℝ) : ℂ)) volume := by
      simpa using Complex.ofRealCLM.integrable_comp hint_re
    have him : Integrable (fun y : Space =>
        ((∑ j : Fin 3, F y j * spatialTestDerivative j φ_im y : ℝ) : ℂ)) volume := by
      simpa using Complex.ofRealCLM.integrable_comp hint_im
    rw [← integral_add hint_adv hint_conv, integral_congr_ae (ae_of_all _ hpt),
      integral_add hre (him.const_mul Complex.I), integral_const_mul, integral_complex_ofReal,
      integral_complex_ofReal, (hSol t).identity φ_re hφ_re, (hSol t).identity φ_im hφ_im]
    simp
  exact eq_neg_of_add_eq_zero_left hsum_zero

/-- On each slice `t : ℝ` of a solenoidal phase test `Φ`, pairing against `smoothConvectiveLeray U₀ U₀ t`
equals pairing against `spatialConvect (U₀ t) (U₀ t)`. -/
theorem slice_integral_smoothConvectiveLeray_eq {P : ℝ} {Φ : ℝ × Space → CVec3}
    (hΦ : IsSolTest P Φ) {U₀ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀) (t : ℝ) :
    (∫ y : Space, dotL (Φ (t, y)) (realC (smoothConvectiveLeray U₀ U₀ t y))) =
      ∫ y : Space, dotL (Φ (t, y)) (realC (spatialConvect (U₀ t) (U₀ t) y)) := by
  obtain ⟨hPh, hdiv⟩ := hΦ
  have hψs : ContDiff ℝ ∞ (fun y => Φ (t, y)) :=
    hPh.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hψc : HasCompactSupport (fun y => Φ (t, y)) := hPh.hasCompactSupport_slice t
  have hfd : ∀ (x v : Space), fderiv ℝ (fun y => Φ (t, y)) x v = fderiv ℝ Φ (t, x) (0, v) := by
    intro x v
    have hφd : HasFDerivAt Φ (fderiv ℝ Φ (t, x)) (t, x) :=
      (hPh.smooth.differentiable (by simp) (t, x)).hasFDerivAt
    have hψd : HasFDerivAt (fun y => Φ (t, y))
        ((fderiv ℝ Φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x :=
      hφd.comp x (hasFDerivAt_prodMk_right t x)
    rw [hψd.fderiv]
    rfl
  have hdiff : ∀ x : Space, DifferentiableAt ℝ (fun y => Φ (t, y)) x := fun x =>
    (hψs.differentiable (by simp)) x
  have hsa : IsSolenoidal (fun y => RieszLp.reV (Φ (t, y))) := by
    refine isSolenoidal_of_div_zero (RieszLp.reV.contDiff.comp hψs) (hψc.comp_left RieszLp.reV.map_zero) ?_
    intro x
    have hsum : ∑ j : Fin 3, fderiv ℝ (fun y => Φ (t, y)) x (coordinateVector j) j = 0 := by
      simp only [hfd]
      exact hdiv (t, x)
    have hr : ∀ i : Fin 3, fderiv ℝ (fun y => RieszLp.reV (Φ (t, y))) x (coordinateVector i) =
        RieszLp.reV (fderiv ℝ (fun y => Φ (t, y)) x (coordinateVector i)) := by
      intro i
      have hd2 : fderiv ℝ (fun y => RieszLp.reV (Φ (t, y))) x =
          RieszLp.reV.comp (fderiv ℝ (fun y => Φ (t, y)) x) :=
        (RieszLp.reV.hasFDerivAt.comp x (hdiff x).hasFDerivAt).fderiv
      rw [hd2]
      rfl
    simp only [hr, RieszLp.reV_apply]
    rw [← Complex.re_sum, hsum]
    simp
  have hsb : IsSolenoidal (fun y => RieszLp.imV (Φ (t, y))) := by
    refine isSolenoidal_of_div_zero (RieszLp.imV.contDiff.comp hψs) (hψc.comp_left RieszLp.imV.map_zero) ?_
    intro x
    have hsum : ∑ j : Fin 3, fderiv ℝ (fun y => Φ (t, y)) x (coordinateVector j) j = 0 := by
      simp only [hfd]
      exact hdiv (t, x)
    have hr : ∀ i : Fin 3, fderiv ℝ (fun y => RieszLp.imV (Φ (t, y))) x (coordinateVector i) =
        RieszLp.imV (fderiv ℝ (fun y => Φ (t, y)) x (coordinateVector i)) := by
      intro i
      have hd2 : fderiv ℝ (fun y => RieszLp.imV (Φ (t, y))) x =
          RieszLp.imV.comp (fderiv ℝ (fun y => Φ (t, y)) x) :=
        (RieszLp.imV.hasFDerivAt.comp x (hdiff x).hasFDerivAt).fderiv
      rw [hd2]
      rfl
    simp only [hr, RieszLp.imV_apply]
    rw [← Complex.im_sum, hsum]
    simp
  have hac : Continuous (fun y => RieszLp.reV (Φ (t, y))) := RieszLp.reV.continuous.comp hψs.continuous
  have hbc : Continuous (fun y => RieszLp.imV (Φ (t, y))) := RieszLp.imV.continuous.comp hψs.continuous
  have hacs : HasCompactSupport (fun y => RieszLp.reV (Φ (t, y))) := hψc.comp_left RieszLp.reV.map_zero
  have hbcs : HasCompactSupport (fun y => RieszLp.imV (Φ (t, y))) := hψc.comp_left RieszLp.imV.map_zero
  have hRa := PointwiseDerivSub.integral_inner_smoothConvectiveLeray_eq hac hacs hsa hU₀ hU₀ t
  have hRb := PointwiseDerivSub.integral_inner_smoothConvectiveLeray_eq hbc hbcs hsb hU₀ hU₀ t
  have hsplit : ∀ G : SpatialField, Continuous G →
      (∫ y : Space, dotL (Φ (t, y)) (realC (G y))) =
        ((∫ y : Space, inner ℝ (RieszLp.reV (Φ (t, y))) (G y) : ℝ) : ℂ) +
          Complex.I * ((∫ y : Space, inner ℝ (RieszLp.imV (Φ (t, y))) (G y) : ℝ) : ℂ) := by
    intro G hG
    have hinta : Integrable (fun y : Space => inner ℝ (RieszLp.reV (Φ (t, y))) (G y)) volume :=
      (hac.inner hG).integrable_of_hasCompactSupport (hacs.mono (by
        intro y hy
        simp only [Function.mem_support, ne_eq] at hy ⊢
        intro h0
        apply hy
        rw [h0, inner_zero_left]))
    have hintb : Integrable (fun y : Space => inner ℝ (RieszLp.imV (Φ (t, y))) (G y)) volume :=
      (hbc.inner hG).integrable_of_hasCompactSupport (hbcs.mono (by
        intro y hy
        simp only [Function.mem_support, ne_eq] at hy ⊢
        intro h0
        apply hy
        rw [h0, inner_zero_left]))
    have heq : (fun y : Space => dotL (Φ (t, y)) (realC (G y))) =
        fun y : Space => ((inner ℝ (RieszLp.reV (Φ (t, y))) (G y) : ℝ) : ℂ) +
          Complex.I * ((inner ℝ (RieszLp.imV (Φ (t, y))) (G y) : ℝ) : ℂ) := by
      funext y
      rw [PointwiseDerivSub.realC_eq_ofReV, dotL_ofReV_eq]
    have hre : Integrable (fun y : Space =>
        ((inner ℝ (RieszLp.reV (Φ (t, y))) (G y) : ℝ) : ℂ)) volume := by
      simpa using Complex.ofRealCLM.integrable_comp hinta
    have him : Integrable (fun y : Space =>
        ((inner ℝ (RieszLp.imV (Φ (t, y))) (G y) : ℝ) : ℂ)) volume := by
      simpa using Complex.ofRealCLM.integrable_comp hintb
    rw [heq, integral_add hre (him.const_mul Complex.I),
      integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  have hG1 : Continuous (smoothConvectiveLeray U₀ U₀ t) :=
    (SmoothLeraySliceSub.smoothLeraySlice_rep_and_memLp smoothLerayRepExists_proof
      (sliceFamily_spatialConvect hU₀ hU₀) t).1.choose_spec.1.continuous
  have hG2 : Continuous (spatialConvect (U₀ t) (U₀ t)) :=
    (contDiff_infty_spatialConvect (sliceFamily_contDiff_infty hU₀ t)
      (sliceFamily_contDiff_infty hU₀ t)).continuous
  rw [hsplit _ hG1, hsplit _ hG2, hRa, hRb]

end BaseRepIBP

end UnforcedLeray.Short.IIb

end
