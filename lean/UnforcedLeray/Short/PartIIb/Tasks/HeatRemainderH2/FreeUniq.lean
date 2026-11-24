import UnforcedLeray.Short.PartIIb.Sub.PartIIb_B3_2_1
import UnforcedLeray.Loc.L01Coefficient.HeatPeriodic
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation
import UnforcedLeray.Short.PartIIa.Tasks.F05HomogeneousUniqueness
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.YqOfFields
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.SmoothLeraySlice
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.LerayCont
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.BaseRep.IBP
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate.InletLp

/-!
# `PartII-b:B3/2/1/3`: Free similarity Duhamel uniqueness in `Y_{11/4}` (`FreeUniq.lean`)

Source of record: `the November 2 reference manuscript`, lines 2613-2629.

Proves `freeDuhamelUniquenessAe_proof : UnforcedLeray.Short.IIb.FreeDuhamelUniquenessAe`:
1. Lift `W = U - H_a` and `G_sm = -smoothConvectiveLeray U U` to `w, g_q : Yq P q0E` via
   `yqOfFields` (`q0E = 11/4`);
2. Establish the distributional equation `HasPhaseOp (fun Φ => (0 : ℂ) • Φ + L0T ν Φ) w g_q`
   by slicewise Lagrange integration by parts in `y` and 1D fundamental theorem of calculus on
   `(0, P]` using `P`-periodicity;
3. Conclude `w = Rm g_q` at `μ = 0` from `PartIIa.bodyResolvent_exists`,
   `PartIIa.bodyResolvent_solves`, and `PartIIa.bodyOp_uniqueness`;
4. Identify the `L²` Bochner Duhamel integral slicewise a.e. with the `L^{11/4}` Duhamel integral,
   and match the latter in `Yq P q0E` with `Rm g_q = w` via phase-test separation.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb.FreeUniqAux

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.B0414 UnforcedLeray.B0418
  UnforcedLeray.B0421 UnforcedLeray.Blueprint UnforcedLeray.RieszLp UnforcedLeray.PhaseTrace

/-! ## 1. Exponent facts at `q0E = 11 / 4` -/

theorem q0E_gt_one : 1 < q0E := by
  unfold q0E
  rw [UnforcedLeray.B0281.q0_eq, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

theorem q0E_lt_three : q0E < 3 := by
  unfold q0E
  rw [UnforcedLeray.B0281.q0_eq]
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by simp
  rw [h3]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

theorem q0E_ne_top : q0E ≠ ⊤ := ne_top_of_lt q0E_lt_three

theorem q0E_eq_eleven_fourths : q0E = (11 / 4 : ℝ≥0∞) := by
  unfold q0E
  rw [UnforcedLeray.B0281.q0_eq,
    ← UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet.eleven_fourths]

theorem gammaExp_q0E : gammaExp q0E = 1 / 22 := by
  unfold gammaExp q0E
  have h0 : (0 : ℝ) ≤ UnforcedLeray.B0281.q0 := by rw [UnforcedLeray.B0281.q0_eq]; norm_num
  rw [ENNReal.toReal_ofReal h0, UnforcedLeray.B0281.q0_eq]
  norm_num

theorem gammaR_q0E_pos : 0 < (0 : ℂ).re + UnforcedLeray.Short.PartIIa.gammaR q0E := by
  unfold UnforcedLeray.Short.PartIIa.gammaR q0E
  have h0 : (0 : ℝ) ≤ UnforcedLeray.B0281.q0 := by rw [UnforcedLeray.B0281.q0_eq]; norm_num
  simp only [Complex.zero_re, zero_add, ENNReal.toReal_ofReal h0]
  rw [UnforcedLeray.B0281.q0_eq]
  norm_num

/-! ## 2. `realC`, `L^{11/4}` interpolation (`L² ∩ L^∞`), and `IsInYr` lifting -/

theorem norm_realC (v : Space) : ‖realC v‖ = ‖v‖ := by
  rw [PointwiseDerivSub.realC_eq_ofReV]
  exact norm_ofReVLin v

theorem continuous_realC : Continuous (realC : Space → CVec3) := by
  have heq : (realC : Space → CVec3) = ofReV := funext PointwiseDerivSub.realC_eq_ofReV
  rw [heq]
  exact ofReV.continuous

theorem eLpNorm_realC_eq (f : SpatialField) (p : ℝ≥0∞) :
    eLpNorm (fun y => realC (f y)) p volume = eLpNorm f p volume :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_realC (f y))

/-- A continuous field bounded in `L²(ℝ³)` and `L^∞(ℝ³)` belongs to `L^{11/4}(ℝ³)` (`q0E`) with
uniform norm bound `max (max M₂ M_inf) 1` (`11/4 = 3/4 + 2`). -/
theorem memLp_q0E_of_l2_linfty {g : SpatialField} (hg : Continuous g)
    {M₂ M_inf : ℝ} (h2 : eLpNorm g 2 volume ≤ ENNReal.ofReal M₂)
    (hinf : ∀ y : Space, ‖g y‖ ≤ M_inf) :
    MemLp g q0E volume ∧
      eLpNorm g q0E volume ≤ ENNReal.ofReal (max (max M₂ M_inf) 1) := by
  set B : ℝ := max (max M₂ M_inf) 1
  have hB1 : 1 ≤ B := le_max_right _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hBM₂ : M₂ ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hBMinf : M_inf ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hpt : ∀ y : Space, ‖g y‖ₑ ≤ ENNReal.ofReal B := fun y => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hinf y).trans hBMinf)
  have hpt_pow : ∀ y : Space,
      ‖g y‖ₑ ^ (11 / 4 : ℝ) ≤ ENNReal.ofReal B ^ (3 / 4 : ℝ) * ‖g y‖ₑ ^ (2 : ℝ) := by
    intro y
    have he : (11 / 4 : ℝ) = 3 / 4 + 2 := by norm_num
    rw [he, ENNReal.rpow_add_of_nonneg (3 / 4) 2 (by norm_num) (by norm_num)]
    gcongr
    exact hpt y
  have hl2 : ∫⁻ y : Space, ‖g y‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal B ^ (2 : ℝ) := by
    have h2' : eLpNorm g 2 volume ≤ ENNReal.ofReal B :=
      h2.trans (ENNReal.ofReal_le_ofReal hBM₂)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top] at h2'
    have hto : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [hto] at h2'
    have hr := ENNReal.rpow_le_rpow h2' (by norm_num : (0 : ℝ) ≤ 2)
    rwa [one_div, ENNReal.rpow_inv_rpow (by norm_num : (2 : ℝ) ≠ 0)] at hr
  have hlint : ∫⁻ y : Space, ‖g y‖ₑ ^ (11 / 4 : ℝ) ≤ ENNReal.ofReal B ^ (11 / 4 : ℝ) := by
    calc ∫⁻ y : Space, ‖g y‖ₑ ^ (11 / 4 : ℝ)
        ≤ ∫⁻ y : Space, ENNReal.ofReal B ^ (3 / 4 : ℝ) * ‖g y‖ₑ ^ (2 : ℝ) :=
          lintegral_mono hpt_pow
      _ = ENNReal.ofReal B ^ (3 / 4 : ℝ) * ∫⁻ y : Space, ‖g y‖ₑ ^ (2 : ℝ) :=
          lintegral_const_mul _ (hg.measurable.enorm.pow_const 2)
      _ ≤ ENNReal.ofReal B ^ (3 / 4 : ℝ) * ENNReal.ofReal B ^ (2 : ℝ) := by gcongr
      _ = ENNReal.ofReal B ^ (11 / 4 : ℝ) := by
          rw [← ENNReal.rpow_add_of_nonneg (3 / 4) 2 (by norm_num) (by norm_num)]
          norm_num
  have hbd : eLpNorm g q0E volume ≤ ENNReal.ofReal B := by
    have hq0 : q0E ≠ 0 := (zero_lt_one.trans q0E_gt_one).ne'
    have hqr : q0E.toReal = 11 / 4 := by
      unfold q0E
      rw [ENNReal.toReal_ofReal (by rw [UnforcedLeray.B0281.q0_eq]; norm_num),
        UnforcedLeray.B0281.q0_eq]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 q0E_ne_top, hqr]
    calc (∫⁻ y : Space, ‖g y‖ₑ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ))
        ≤ (ENNReal.ofReal B ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) :=
          ENNReal.rpow_le_rpow hlint (by norm_num)
      _ = ENNReal.ofReal B := by
          rw [one_div, ENNReal.rpow_rpow_inv (by norm_num : (11 / 4 : ℝ) ≠ 0)]
  exact ⟨⟨hg.aestronglyMeasurable, lt_of_le_of_lt hbd ENNReal.ofReal_lt_top⟩, hbd⟩

/-- A jointly continuous `P`-periodic real slice family with uniform `L^{11/4}` slice norm bound
lifts via `realC` to `IsInYr P bgp`. -/
theorem isInYr_realC_of_slice {P B : ℝ} (hP : 0 < P) (hB : 0 ≤ B)
    {V : ℝ → SpatialField}
    (hV_cont : Continuous fun z : ℝ × Space => V z.1 z.2)
    (hV_per : Function.Periodic V P)
    (hV_bd : ∀ τ : ℝ, eLpNorm (V τ) q0E volume ≤ ENNReal.ofReal B) :
    IsInYr P bgp (fun z : ℝ × Space => realC (V z.1 z.2)) where
  periodic := Eventually.of_forall fun x => by
    simp only
    rw [congrFun (hV_per x.1) x.2]
  meas := (continuous_realC.comp hV_cont).aestronglyMeasurable
  finite := by
    have hle : phaseLpNorm P bgp (fun z : ℝ × Space => realC (V z.1 z.2)) ≤ ENNReal.ofReal B := by
      refine phaseLpNorm_bgp_le_of_slice hP hB fun τ => ?_
      rw [← q0E_eq_eleven_fourths, eLpNorm_realC_eq]
      exact hV_bd τ
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

/-! ## 3. Joint continuity of the similarity heat profile and its evolution terms -/

theorem spatialLaplacian_eq_vlap {F : SpatialField} (hF : ContDiff ℝ ∞ F) (y : Space) :
    spatialLaplacian F y = UnforcedLeray.Heat.vlap F y := by
  unfold spatialLaplacian dirSpatialJet UnforcedLeray.Heat.vlap
  refine Finset.sum_congr rfl fun j _ => ?_
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hc : DifferentiableAt ℝ (fderiv ℝ F) y :=
    ((hF2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  change fderiv ℝ (fun y' => fderiv ℝ F y' (EuclideanSpace.single j (1 : ℝ))) y
      (EuclideanSpace.single j (1 : ℝ)) =
    ((fderiv ℝ (fderiv ℝ F) y) (UnforcedLeray.coordinateVector j))
      (UnforcedLeray.coordinateVector j)
  rw [fderiv_clm_apply hc (differentiableAt_const (EuclideanSpace.single j (1 : ℝ)))]
  simp [UnforcedLeray.coordinateVector]

theorem continuous_heatProfile_joint {ν C : ℝ} (hν : 0 < ν) {a : SpatialField}
    (hu : UnforcedLeray.Heat.InvDistClass 2 C a) :
    Continuous fun z : ℝ × Space => UnforcedLeray.Blueprint.heatProfile ν a z.1 z.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, y₀⟩
  have hT : 0 < ν * Real.exp t₀ := mul_pos hν (Real.exp_pos t₀)
  have havg : ContinuousAt (fun p : ℝ × Space => UnforcedLeray.Heat.average p.1 a p.2)
      (ν * Real.exp t₀, Real.exp (t₀ / 2) • y₀) :=
    (hu.hasStrictFDerivAt_average_joint hT (Real.exp (t₀ / 2) • y₀)).continuousAt
  have hmap : Continuous (fun z : ℝ × Space => (ν * Real.exp z.1, Real.exp (z.1 / 2) • z.2)) :=
    (continuous_const.mul (Real.continuous_exp.comp continuous_fst)).prodMk
      ((Real.continuous_exp.comp (continuous_fst.div_const 2)).smul continuous_snd)
  have hcomp : ContinuousAt
      (fun z : ℝ × Space => UnforcedLeray.Heat.average (ν * Real.exp z.1) a (Real.exp (z.1 / 2) • z.2))
      (t₀, y₀) :=
    ContinuousAt.comp (g := fun p : ℝ × Space => UnforcedLeray.Heat.average p.1 a p.2)
      (f := fun z : ℝ × Space => (ν * Real.exp z.1, Real.exp (z.1 / 2) • z.2))
      havg hmap.continuousAt
  have hsc : ContinuousAt (fun z : ℝ × Space => Real.exp (z.1 / 2)) (t₀, y₀) :=
    (Real.continuous_exp.comp (continuous_fst.div_const 2)).continuousAt
  exact hsc.smul hcomp

theorem continuous_heatProfile_dt_joint {ν C : ℝ} (hν : 0 < ν) {a : SpatialField}
    (hu : UnforcedLeray.Heat.InvDistClass 2 C a) :
    Continuous fun z : ℝ × Space =>
      ν • UnforcedLeray.Heat.vlap (UnforcedLeray.Blueprint.heatProfile ν a z.1) z.2 +
        (1 / 2 : ℝ) • fderiv ℝ (UnforcedLeray.Blueprint.heatProfile ν a z.1) z.2 z.2 +
        (1 / 2 : ℝ) • UnforcedLeray.Blueprint.heatProfile ν a z.1 z.2 := by
  have hmap : Continuous (fun z : ℝ × Space => (ν * Real.exp z.1, Real.exp (z.1 / 2) • z.2)) :=
    (continuous_const.mul (Real.continuous_exp.comp continuous_fst)).prodMk
      ((Real.continuous_exp.comp (continuous_fst.div_const 2)).smul continuous_snd)
  have hsc : Continuous (fun z : ℝ × Space => Real.exp (z.1 / 2)) :=
    Real.continuous_exp.comp (continuous_fst.div_const 2)
  have hvlap : Continuous fun z : ℝ × Space =>
      UnforcedLeray.Heat.vlap (UnforcedLeray.Blueprint.heatProfile ν a z.1) z.2 := by
    have heq : (fun z : ℝ × Space =>
        UnforcedLeray.Heat.vlap (UnforcedLeray.Blueprint.heatProfile ν a z.1) z.2) =
        fun z => (Real.exp (z.1 / 2) * Real.exp (z.1 / 2) ^ 2) •
          UnforcedLeray.Heat.vlap (UnforcedLeray.Heat.average (ν * Real.exp z.1) a)
            (Real.exp (z.1 / 2) • z.2) := by
      funext ⟨t, y⟩
      exact UnforcedLeray.Heat.vlap_rescale
        (UnforcedLeray.Heat.average (ν * Real.exp t) a) (Real.exp (t / 2)) y
    rw [heq, continuous_iff_continuousAt]
    rintro ⟨t₀, y₀⟩
    have hT : 0 < ν * Real.exp t₀ := mul_pos hν (Real.exp_pos t₀)
    have hc1 : ContinuousAt
        (fun z : ℝ × Space =>
          UnforcedLeray.Heat.vlap (UnforcedLeray.Heat.average (ν * Real.exp z.1) a)
            (Real.exp (z.1 / 2) • z.2)) (t₀, y₀) :=
      ContinuousAt.comp
        (g := fun z : ℝ × Space => UnforcedLeray.Heat.vlap (UnforcedLeray.Heat.average z.1 a) z.2)
        (f := fun z : ℝ × Space => (ν * Real.exp z.1, Real.exp (z.1 / 2) • z.2))
        (hu.continuousAt_vlap_joint hT (Real.exp (t₀ / 2) • y₀)) hmap.continuousAt
    exact (hsc.mul (hsc.pow 2)).continuousAt.smul hc1
  have hfderiv : Continuous fun z : ℝ × Space =>
      fderiv ℝ (UnforcedLeray.Blueprint.heatProfile ν a z.1) z.2 z.2 := by
    have heq : (fun z : ℝ × Space =>
        fderiv ℝ (UnforcedLeray.Blueprint.heatProfile ν a z.1) z.2 z.2) =
        fun z => (Real.exp (z.1 / 2) * Real.exp (z.1 / 2)) •
          fderiv ℝ (UnforcedLeray.Heat.average (ν * Real.exp z.1) a)
            (Real.exp (z.1 / 2) • z.2) z.2 := by
      funext ⟨t, y⟩
      have hT : 0 < ν * Real.exp t := mul_pos hν (Real.exp_pos t)
      have hdiff : DifferentiableAt ℝ (UnforcedLeray.Heat.average (ν * Real.exp t) a)
          (Real.exp (t / 2) • y) :=
        ((UnforcedLeray.Heat.contDiff_two_average hu hT).differentiable two_ne_zero) _
      exact UnforcedLeray.Heat.fderiv_rescale_apply hdiff y
    rw [heq, continuous_iff_continuousAt]
    rintro ⟨t₀, y₀⟩
    have hT : 0 < ν * Real.exp t₀ := mul_pos hν (Real.exp_pos t₀)
    have hc1 : ContinuousAt
        (fun z : ℝ × Space =>
          fderiv ℝ (UnforcedLeray.Heat.average (ν * Real.exp z.1) a)
            (Real.exp (z.1 / 2) • z.2)) (t₀, y₀) :=
      ContinuousAt.comp
        (g := fun z : ℝ × Space => fderiv ℝ (UnforcedLeray.Heat.average z.1 a) z.2)
        (f := fun z : ℝ × Space => (ν * Real.exp z.1, Real.exp (z.1 / 2) • z.2))
        (hu.continuousAt_fderiv_joint hT (Real.exp (t₀ / 2) • y₀)) hmap.continuousAt
    exact (hsc.mul hsc).continuousAt.smul (hc1.clm_apply continuous_snd.continuousAt)
  exact ((hvlap.const_smul ν).add (hfderiv.const_smul (1 / 2 : ℝ))).add
    ((continuous_heatProfile_joint hν hu).const_smul (1 / 2 : ℝ))

/-! ## 4. Slicewise Lagrange IBP and period FTC for `L0T ν` -/

theorem slice_ibp_L0T {P : ℝ} (ν : ℝ) {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {F : SpatialField} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    (∫ y : Space, dotL (L0T ν Φ (t, y)) (realC (F y))) =
      -(∫ y : Space, dotL (dτ Φ (t, y)) (realC (F y))) -
        ∫ y : Space, dotL (Φ (t, y)) (realC (spatialProjectedLin ν F y)) := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  let u : ℝ × Space → CVec3 := BaseRepIBP.constRealCLift F
  have hu : ContDiff ℝ ∞ u := BaseRepIBP.contDiff_constRealCLift hF
  have hdΦ : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  let A : Fin 3 → ℝ × Space → ℂ := fun j p => ((p.2 j : ℝ) : ℂ) * dotFn Φ u p
  let B : Fin 3 → ℝ × Space → ℂ := fun j p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p
  have hA_cd : ∀ j : Fin 3, ContDiff ℝ ∞ (A j) := fun j => by
    have hc : ContDiff ℝ ∞ (fun p : ℝ × Space => ((p.2 j : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff).comp contDiff_snd)
    exact hc.mul (BaseRepIBP.contDiff_dotFn hΦ.smooth hu)
  have hB_cd : ∀ j : Fin 3, ContDiff ℝ ∞ (B j) := fun j =>
    (BaseRepIBP.contDiff_dotFn (contDiff_dy hΦ.smooth j) hu).sub
      (BaseRepIBP.contDiff_dotFn hΦ.smooth (contDiff_dy hu j))
  have hA_int : ∀ j : Fin 3,
      Integrable (fun y : Space => dy j (A j) (t, y)) volume ∧
        ∫ y : Space, dy j (A j) (t, y) = 0 := fun j =>
    BaseRepIBP.integral_slice_dy_eq_zero (R := R) (hA_cd j) t
      (fun y hy => by simp [A, dotFn, hR t y hy]) j
  have hB_int : ∀ j : Fin 3,
      Integrable (fun y : Space => dy j (B j) (t, y)) volume ∧
        ∫ y : Space, dy j (B j) (t, y) = 0 := fun j =>
    BaseRepIBP.integral_slice_dy_eq_zero (R := R) (hB_cd j) t
      (fun y hy => by
        have hdy : dy j Φ (t, y) = 0 := BaseRepIBP.dy_eq_zero_of_bound hR j t y hy
        simp [B, dotFn, hR t y hy, hdy]) j
  have hdτ_eq : ∀ y : Space, -dτ (dotFn Φ u) (t, y) = -dotL (dτ Φ (t, y)) (realC (F y)) := by
    intro y
    rw [dτ_dotFn hdΦ hdu (t, y), BaseRepIBP.dτ_constRealCLift hF (t, y), map_zero, add_zero]
    rfl
  have hL0_eq : ∀ y : Space, dotL (Φ (t, y)) (L0 ν u (t, y)) =
      -dotL (Φ (t, y)) (realC (spatialProjectedLin ν F y)) := by
    intro y
    rw [BaseRepIBP.L0_constRealCLift ν hF (t, y), map_neg]
  have hpt : ∀ y : Space,
      dotL (L0T ν Φ (t, y)) (realC (F y)) +
        dotL (Φ (t, y)) (realC (spatialProjectedLin ν F y)) =
      -dotL (dτ Φ (t, y)) (realC (F y)) +
        (1 / 2 : ℂ) * ∑ j : Fin 3, dy j (A j) (t, y) -
        (ν : ℂ) * ∑ j : Fin 3, dy j (B j) (t, y) := by
    intro y
    have hlag := lagrange_L0 ν hΦ.smooth hu (t, y)
    change dotL (L0T ν Φ (t, y)) (realC (F y)) - dotL (Φ (t, y)) (L0 ν u (t, y)) = _ at hlag
    rw [hL0_eq y, sub_neg_eq_add, hdτ_eq y] at hlag
    exact hlag
  have hI_L0T : Integrable (fun y : Space => dotL (L0T ν Φ (t, y)) (realC (F y))) volume :=
    BaseRepIBP.integrable_slice_dotL_realC (isPhaseTest_L0T hΦ ν) t hF.continuous
  have hI_proj : Integrable (fun y : Space =>
      dotL (Φ (t, y)) (realC (spatialProjectedLin ν F y))) volume :=
    BaseRepIBP.integrable_slice_dotL_realC hΦ t
      (HigherPhaseSub.contDiff_infty_spatialProjectedLin ν hF).continuous
  have hI_dτ : Integrable (fun y : Space => dotL (dτ Φ (t, y)) (realC (F y))) volume :=
    BaseRepIBP.integrable_slice_dotL_realC hΦ.dτ t hF.continuous
  have hI_sumA : Integrable (fun y : Space => ∑ j : Fin 3, dy j (A j) (t, y)) volume :=
    integrable_finsetSum Finset.univ fun j _ => (hA_int j).1
  have hI_sumB : Integrable (fun y : Space => ∑ j : Fin 3, dy j (B j) (t, y)) volume :=
    integrable_finsetSum Finset.univ fun j _ => (hB_int j).1
  have hsumA_zero : ∫ y : Space, (∑ j : Fin 3, dy j (A j) (t, y)) = 0 := by
    rw [integral_finsetSum Finset.univ fun j _ => (hA_int j).1]
    simp [(hA_int _).2]
  have hsumB_zero : ∫ y : Space, (∑ j : Fin 3, dy j (B j) (t, y)) = 0 := by
    rw [integral_finsetSum Finset.univ fun j _ => (hB_int j).1]
    simp [(hB_int _).2]
  have hI_dτ_neg : Integrable (fun y : Space => -dotL (dτ Φ (t, y)) (realC (F y))) volume :=
    hI_dτ.neg
  have hI_A' : Integrable (fun y : Space => (1 / 2 : ℂ) * ∑ j : Fin 3, dy j (A j) (t, y)) volume :=
    hI_sumA.const_mul (1 / 2 : ℂ)
  have hI_B' : Integrable (fun y : Space => (ν : ℂ) * ∑ j : Fin 3, dy j (B j) (t, y)) volume :=
    hI_sumB.const_mul (ν : ℂ)
  have hI_12 : Integrable (fun y : Space =>
      -dotL (dτ Φ (t, y)) (realC (F y)) + (1 / 2 : ℂ) * ∑ j : Fin 3, dy j (A j) (t, y)) volume :=
    hI_dτ_neg.add hI_A'
  have hcomb : (∫ y : Space, dotL (L0T ν Φ (t, y)) (realC (F y))) +
      (∫ y : Space, dotL (Φ (t, y)) (realC (spatialProjectedLin ν F y))) =
      -(∫ y : Space, dotL (dτ Φ (t, y)) (realC (F y))) := by
    rw [← integral_add hI_L0T hI_proj, integral_congr_ae (Eventually.of_forall hpt),
      integral_sub hI_12 hI_B', integral_add hI_dτ_neg hI_A',
      integral_neg, integral_const_mul, integral_const_mul, hsumA_zero, hsumB_zero]
    ring
  exact eq_sub_of_add_eq hcomb

/-- Period integration by parts on `(0, P]` for a jointly continuous `P`-periodic field `W` with
jointly continuous phase derivative `W_dt`. -/
theorem period_ibp_dτ {P : ℝ} (hP : 0 < P) {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {W W_dt : ℝ → SpatialField}
    (hW_cont : Continuous fun z : ℝ × Space => W z.1 z.2)
    (hWdt_cont : Continuous fun z : ℝ × Space => W_dt z.1 z.2)
    (hW_per : Function.Periodic W P)
    (hW_deriv : ∀ (t : ℝ) (y : Space), HasDerivAt (fun s => W s y) (W_dt t y) t) :
    (∫ t in Ioc (0 : ℝ) P, ∫ y : Space, dotL (dτ Φ (t, y)) (realC (W t y))) =
      -∫ t in Ioc (0 : ℝ) P, ∫ y : Space, dotL (Φ (t, y)) (realC (W_dt t y)) := by
  obtain ⟨R₁, hR₁⟩ := hΦ.bounded_support
  obtain ⟨R₂, hR₂⟩ := hΦ.dτ.bounded_support
  let R : ℝ := max R₁ R₂
  let K : Set Space := Metric.closedBall (0 : Space) R
  have hK_comp : IsCompact K := isCompact_closedBall (0 : Space) R
  have hR_Φ : ∀ (t : ℝ) (y : Space), y ∉ K → Φ (t, y) = 0 := by
    intro t y hy
    have hgt : R < ‖y‖ := by simpa [K, Metric.mem_closedBall, dist_zero_right, not_le] using hy
    exact hR₁ t y (lt_of_le_of_lt (le_max_left _ _) hgt)
  have hR_dτ : ∀ (t : ℝ) (y : Space), y ∉ K → dτ Φ (t, y) = 0 := by
    intro t y hy
    have hgt : R < ‖y‖ := by simpa [K, Metric.mem_closedBall, dist_zero_right, not_le] using hy
    exact hR₂ t y (lt_of_le_of_lt (le_max_right _ _) hgt)
  let F₁ : ℝ × Space → ℂ := fun z => dotL (dτ Φ z) (realC (W z.1 z.2))
  let F₂ : ℝ × Space → ℂ := fun z => dotL (Φ z) (realC (W_dt z.1 z.2))
  have hF₁_cont : Continuous F₁ :=
    (dotL.continuous.comp hΦ.dτ.smooth.continuous).clm_apply (continuous_realC.comp hW_cont)
  have hF₂_cont : Continuous F₂ :=
    (dotL.continuous.comp hΦ.smooth.continuous).clm_apply (continuous_realC.comp hWdt_cont)
  have hbox_comp : IsCompact (Icc (0 : ℝ) P ×ˢ K) := isCompact_Icc.prod hK_comp
  have hsub : Ioc (0 : ℝ) P ×ˢ K ⊆ Icc (0 : ℝ) P ×ˢ K :=
     Set.prod_mono Ioc_subset_Icc_self Subset.rfl
  have hmeas_prod :
      ((volume : Measure ℝ).restrict (Ioc 0 P)).prod ((volume : Measure Space).restrict K) =
        (volume : Measure (ℝ × Space)).restrict (Ioc 0 P ×ˢ K) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hF₁_int : Integrable F₁
      (((volume : Measure ℝ).restrict (Ioc 0 P)).prod ((volume : Measure Space).restrict K)) := by
    rw [hmeas_prod]
    exact (hF₁_cont.continuousOn.integrableOn_compact hbox_comp).mono_set hsub
  have hF₂_int : Integrable F₂
      (((volume : Measure ℝ).restrict (Ioc 0 P)).prod ((volume : Measure Space).restrict K)) := by
    rw [hmeas_prod]
    exact (hF₂_cont.continuousOn.integrableOn_compact hbox_comp).mono_set hsub
  have hsl₁ : ∀ t : ℝ, (∫ y : Space, F₁ (t, y)) = ∫ y in K, F₁ (t, y) := fun t =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp [F₁, hR_dτ t y hy]).symm
  have hsl₂ : ∀ t : ℝ, (∫ y : Space, F₂ (t, y)) = ∫ y in K, F₂ (t, y) := fun t =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp [F₂, hR_Φ t y hy]).symm
  have hftc_y : ∀ y : Space, (∫ t in Ioc (0 : ℝ) P, (F₁ (t, y) + F₂ (t, y))) = 0 := by
    intro y
    let g : ℝ → ℂ := fun t => dotL (Φ (t, y)) (realC (W t y))
    have hg_der : ∀ t : ℝ, HasDerivAt g (F₁ (t, y) + F₂ (t, y)) t := by
      intro t
      have hγ : HasFDerivAt (fun s : ℝ => (s, y))
          ((ContinuousLinearMap.id ℝ ℝ).prod 0) t :=
        (hasFDerivAt_id t).prodMk (hasFDerivAt_const y t)
      have hd1 : HasFDerivAt (fun s : ℝ => Φ (s, y))
          ((fderiv ℝ Φ (t, y)).comp ((ContinuousLinearMap.id ℝ ℝ).prod 0)) t :=
        (((hΦ.smooth.differentiable (by simp)) (t, y)).hasFDerivAt).comp t hγ
      have hW_fd : HasFDerivAt (fun s : ℝ => W s y)
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (W_dt t y)) t :=
        (hW_deriv t y).hasFDerivAt
      have hd2 : HasFDerivAt (fun s : ℝ => realC (W s y))
          (ofReV.comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (W_dt t y))) t := by
        have heq : (fun s : ℝ => realC (W s y)) = fun s => ofReV (W s y) :=
          funext fun s => PointwiseDerivSub.realC_eq_ofReV (W s y)
        rw [heq]
        exact ofReV.hasFDerivAt.comp t hW_fd
      have hbil := (dotLR.hasFDerivAt_of_bilinear hd1 hd2).hasDerivAt
      refine hbil.congr_deriv ?_
      change dotL (Φ (t, y)) (ofReV ((1 : ℝ) • W_dt t y)) +
          dotL (dτ Φ (t, y)) (realC (W t y)) =
        F₁ (t, y) + F₂ (t, y)
      rw [one_smul, ← PointwiseDerivSub.realC_eq_ofReV, add_comm]
    have hg_ii : IntervalIntegrable (fun t => F₁ (t, y) + F₂ (t, y)) volume 0 P :=
      ((hF₁_cont.add hF₂_cont).comp (Continuous.prodMk_left y)).intervalIntegrable 0 P
    rw [← intervalIntegral.integral_of_le hP.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg_der t) hg_ii]
    have hperΦ : Φ (P, y) = Φ (0, y) := by simpa using hΦ.periodic 0 y
    have hperW : W P y = W 0 y := by simpa using congrFun (hW_per 0) y
    simp [g, hperΦ, hperW]
  have hsum_zero :
      (∫ t in Ioc (0 : ℝ) P, ∫ y : Space, F₁ (t, y)) +
        (∫ t in Ioc (0 : ℝ) P, ∫ y : Space, F₂ (t, y)) = 0 := by
    simp_rw [hsl₁, hsl₂]
    rw [← integral_prod F₁ hF₁_int, ← integral_prod F₂ hF₂_int,
      ← integral_add hF₁_int hF₂_int]
    change (∫ z : ℝ × Space, (F₁ + F₂) z ∂
      (((volume : Measure ℝ).restrict (Ioc 0 P)).prod ((volume : Measure Space).restrict K))) = 0
    rw [integral_prod_symm _ (hF₁_int.add hF₂_int)]
    simp [Pi.add_apply, hftc_y]
  exact eq_neg_of_add_eq_zero_left hsum_zero

/-! ## 5. Semigroup Bochner integrals and slice identification -/

/-- Joint continuity of `(r, v) ↦ freeSemigroupLp hp ν (max r 0) v` on `ℝ × Lp Space p volume`
when `0 ≤ gammaExp p`. -/
theorem continuous_freeSemigroupLp_max {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {ν : ℝ} (hν : 0 < ν) (hγ : 0 ≤ gammaExp p) :
    Continuous fun z : ℝ × Lp Space p (volume : Measure Space) =>
      freeSemigroupLp hp ν (max z.1 0) z.2 := by
  have hnorm1 : ∀ r : ℝ, ‖freeSemigroupLp hp ν (max r 0)‖ ≤ 1 := by
    intro r
    refine (norm_freeSemigroupLp_le hp ν (max r 0)).trans ?_
    rw [Real.exp_le_one_iff]
    have hm : 0 ≤ max r 0 := le_max_right r 0
    nlinarith
  have hlip : ∀ r : ℝ, LipschitzWith 1 (fun v => freeSemigroupLp hp ν (max r 0) v) := by
    intro r
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    calc ‖freeSemigroupLp hp ν (max r 0) (u - v)‖
        ≤ ‖freeSemigroupLp hp ν (max r 0)‖ * ‖u - v‖ :=
          (freeSemigroupLp hp ν (max r 0)).le_opNorm (u - v)
      _ ≤ 1 * ‖u - v‖ := mul_le_mul_of_nonneg_right (hnorm1 r) (norm_nonneg _)
      _ = ‖u - v‖ := one_mul _
  have hcont_r : ∀ v : Lp Space p (volume : Measure Space),
      Continuous fun r : ℝ => freeSemigroupLp hp ν (max r 0) v := by
    intro v
    exact (continuousOn_freeSemigroupLp hp hν.le v).comp_continuous
      (continuous_id.max continuous_const) fun r => le_max_right r 0
  exact continuous_prod_of_continuous_lipschitzWith'
    (fun z : ℝ × Lp Space p (volume : Measure Space) => freeSemigroupLp hp ν (max z.1 0) z.2)
    1 hlip hcont_r

/-- `freeC` commutes with the real embedding `ofReV.compLpL`. -/
theorem freeC_ofReV_compLpL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (ν r : ℝ)
    (v : Lp Space p (volume : Measure Space)) :
    freeC hp ν r (ofReV.compLpL p volume v) =
      ofReV.compLpL p volume (freeSemigroupLp hp ν r v) := by
  rw [freeC, cx_apply, reV_ofReV_compLpL, imV_ofReV_compLpL, map_zero, map_zero, add_zero]

/-- Spatial test functional on `Lp Space p volume` matching `∫ ψ(y) u_i(y) dy`. -/
def realSpatialTestCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] {ψ : Space → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (i : Fin 3) :
    Lp Space p (volume : Measure Space) →L[ℝ] ℂ :=
  ((innerPair p ((memLp_spatialTest hψ hψc i (conjExp p)).toLp _)).restrictScalars ℝ).comp
    (ofReV.compLpL p volume)

theorem realSpatialTestCLM_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] {ψ : Space → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (i : Fin 3)
    (u : Lp Space p (volume : Measure Space)) :
    realSpatialTestCLM p hψ hψc i u = ∫ y : Space, (ψ y : ℂ) * ((u : SpatialField) y i : ℂ) := by
  unfold realSpatialTestCLM
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [innerPair_spatialTest hψ hψc i (ofReV.compLpL p volume u)]
  refine integral_congr_ae ?_
  filter_upwards [ofReV.coeFn_compLpL (p := p) (μ := (volume : Measure Space)) u] with y hy
  rw [hy]
  rfl

/-- Two spatial `Lp` elements (at exponents `2` and `q0E`) with equal smooth compactly supported
component integrals agree almost everywhere on `Space`. -/
theorem ae_eq_of_realSpatialTestCLM_eq
    (u₂ : L2Space) (uq : Lp Space q0E (volume : Measure Space))
    (heq : ∀ (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (i : Fin 3),
      realSpatialTestCLM 2 hψ hψc i u₂ = realSpatialTestCLM q0E hψ hψc i uq) :
    (u₂ : SpatialField) =ᵐ[volume] (uq : SpatialField) := by
  have hi : ∀ i : Fin 3,
      ∀ᵐ y : Space ∂volume, (u₂ : SpatialField) y i = (uq : SpatialField) y i := by
    intro i
    have hloc₂ : LocallyIntegrable (fun y : Space => (u₂ : SpatialField) y i) volume :=
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp_memLp' (Lp.memLp u₂)).locallyIntegrable
        (by norm_num)
    have hlocq : LocallyIntegrable (fun y : Space => (uq : SpatialField) y i) volume :=
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp_memLp' (Lp.memLp uq)).locallyIntegrable
        Fact.out
    have hzero : (fun y : Space => (u₂ : SpatialField) y i - (uq : SpatialField) y i)
        =ᵐ[volume] 0 := by
      refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc₂.sub hlocq) fun ψ hψ hψc => ?_
      have hc := congrArg Complex.re (heq ψ hψ hψc i)
      rw [realSpatialTestCLM_apply, realSpatialTestCLM_apply] at hc
      have hre : ∀ v : Space → ℝ,
          Complex.re (∫ y : Space, (ψ y : ℂ) * (v y : ℂ)) = ∫ y : Space, ψ y * v y := by
        intro v
        have hfun : (fun y : Space => (ψ y : ℂ) * (v y : ℂ)) =
            fun y => ((ψ y * v y : ℝ) : ℂ) := funext fun y => by push_cast; rfl
        rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
      rw [hre, hre] at hc
      have hint₂ : Integrable (fun y : Space => ψ y * (u₂ : SpatialField) y i) volume :=
        hloc₂.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
      have hintq : Integrable (fun y : Space => ψ y * (uq : SpatialField) y i) volume :=
        hlocq.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub hint₂ hintq, hc, sub_self]
    filter_upwards [hzero] with y hy
    exact sub_eq_zero.1 hy
  filter_upwards [ae_all_iff.2 hi] with y hy
  ext i
  exact hy i

/-- Joint continuity of `spatialProjectedLin ν (U τ - heatProfile ν a τ) y`. -/
theorem continuous_spatialProjectedLin_sub {ν C_a : ℝ} (hν : 0 < ν) {a : SpatialField}
    (hInv4 : UnforcedLeray.Heat.InvDistClass 4 C_a a)
    {U : ℝ → SpatialField} (hU_cd : ContDiff ℝ ∞ fun x : ℝ × Space => U x.1 x.2)
    (hU_fam : IsUniformSmoothL4SliceFamily U) :
    Continuous fun z : ℝ × Space =>
      spatialProjectedLin ν (fun y => U z.1 y - UnforcedLeray.Blueprint.heatProfile ν a z.1 y) z.2 := by
  have hInv2 : UnforcedLeray.Heat.InvDistClass 2 C_a a := hInv4.of_le (by norm_num)
  let H : ℝ → SpatialField := UnforcedLeray.Blueprint.heatProfile ν a
  let W : ℝ → SpatialField := fun τ y => U τ y - H τ y
  have hW_smooth : ∀ t : ℝ, ContDiff ℝ ∞ (W t) := fun t =>
    (HigherPhaseSub.sliceFamily_contDiff_infty hU_fam t).sub
      (UnforcedLeray.Heat.simHeat_contDiff hν hInv4.heatAdmissible t)
  have hW_cont : Continuous fun z : ℝ × Space => W z.1 z.2 :=
    hU_cd.continuous.sub (continuous_heatProfile_joint hν hInv2)
  have heq_p : (fun z : ℝ × Space => spatialProjectedLin ν (W z.1) z.2) =
      fun z => (1 / 2 : ℝ) •
          (fderiv ℝ (U z.1) z.2 z.2 - fderiv ℝ (H z.1) z.2 z.2) +
        (ν • (UnforcedLeray.Heat.vlap (U z.1) z.2 - UnforcedLeray.Heat.vlap (H z.1) z.2) +
          (1 / 2 : ℝ) • W z.1 z.2) := by
    funext ⟨t, y⟩
    have hUs : ContDiff ℝ 2 (U t) :=
      (HigherPhaseSub.sliceFamily_contDiff_infty hU_fam t).of_le (by simp)
    have hHs : ContDiff ℝ 2 (H t) :=
      (UnforcedLeray.Heat.simHeat_contDiff hν hInv4.heatAdmissible t).of_le (by simp)
    unfold spatialProjectedLin spatialDiffReact spatialRadialDrift
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [spatialLaplacian_eq_vlap (hW_smooth t) y]
    have hfd_sub : fderiv ℝ (W t) y y = fderiv ℝ (U t) y y - fderiv ℝ (H t) y y := by
      change fderiv ℝ (U t - H t) y y = _
      rw [fderiv_sub ((hUs.differentiable two_ne_zero) y)
        ((hHs.differentiable two_ne_zero) y), FunLike.coe_sub, Pi.sub_apply]
    have hvl_sub : UnforcedLeray.Heat.vlap (W t) y =
        UnforcedLeray.Heat.vlap (U t) y - UnforcedLeray.Heat.vlap (H t) y := by
      unfold UnforcedLeray.Heat.vlap
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      change iteratedFDeriv ℝ 2 (U t - H t) y _ = _
      rw [iteratedFDeriv_sub_apply hUs.contDiffAt hHs.contDiffAt]
      rfl
    rw [hfd_sub, hvl_sub]
  change Continuous fun z : ℝ × Space => spatialProjectedLin ν (W z.1) z.2
  rw [heq_p]
  have hUfd_c : Continuous (fun z : ℝ × Space => fderiv ℝ (U z.1) z.2 z.2) := by
    have he : (fun z : ℝ × Space => fderiv ℝ (U z.1) z.2 z.2) =
        fun z => fderiv ℝ (fun p : ℝ × Space => U p.1 p.2) z (0, z.2) := by
      funext ⟨t, y⟩
      dsimp only
      have hd1 := ((hU_cd.differentiable (by simp)) (t, y)).hasFDerivAt
      have hcomp : HasFDerivAt (fun y' : Space => U t y')
          ((fderiv ℝ (fun p : ℝ × Space => U p.1 p.2) (t, y)).comp
            (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
        hd1.comp y (hasFDerivAt_prodMk_right t y)
      rw [hcomp.fderiv]
      rfl
    rw [he]
    exact (hU_cd.continuous_fderiv (by simp)).clm_apply
      (continuous_const.prodMk continuous_snd)
  have hHfd_c : Continuous (fun z : ℝ × Space => fderiv ℝ (H z.1) z.2 z.2) := by
    have he : (fun z : ℝ × Space => fderiv ℝ (H z.1) z.2 z.2) =
        fun z => (Real.exp (z.1 / 2) * Real.exp (z.1 / 2)) •
          fderiv ℝ (UnforcedLeray.Heat.average (ν * Real.exp z.1) a)
            (Real.exp (z.1 / 2) • z.2) z.2 := by
      funext ⟨t, y⟩
      have hT : 0 < ν * Real.exp t := mul_pos hν (Real.exp_pos t)
      exact UnforcedLeray.Heat.fderiv_rescale_apply
        (((UnforcedLeray.Heat.contDiff_two_average hInv2 hT).differentiable two_ne_zero) _) y
    rw [he, continuous_iff_continuousAt]
    rintro ⟨t₀, y₀⟩
    have hT : 0 < ν * Real.exp t₀ := mul_pos hν (Real.exp_pos t₀)
    have hmap : Continuous (fun z : ℝ × Space =>
        (ν * Real.exp z.1, Real.exp (z.1 / 2) • z.2)) :=
      (continuous_const.mul (Real.continuous_exp.comp continuous_fst)).prodMk
        ((Real.continuous_exp.comp (continuous_fst.div_const 2)).smul continuous_snd)
    have hsc : Continuous (fun z : ℝ × Space => Real.exp (z.1 / 2)) :=
      Real.continuous_exp.comp (continuous_fst.div_const 2)
    exact (hsc.mul hsc).continuousAt.smul
      ((ContinuousAt.comp
        (g := fun z : ℝ × Space => fderiv ℝ (UnforcedLeray.Heat.average z.1 a) z.2)
        (f := fun z : ℝ × Space => (ν * Real.exp z.1, Real.exp (z.1 / 2) • z.2))
        (hInv2.continuousAt_fderiv_joint hT (Real.exp (t₀ / 2) • y₀))
        hmap.continuousAt).clm_apply continuous_snd.continuousAt)
  have hUvl_c : Continuous (fun z : ℝ × Space => UnforcedLeray.Heat.vlap (U z.1) z.2) := by
    have he : (fun z : ℝ × Space => UnforcedLeray.Heat.vlap (U z.1) z.2) =
        fun z => spatialLaplacian (U z.1) z.2 :=
      funext fun ⟨t, y⟩ =>
        (spatialLaplacian_eq_vlap (HigherPhaseSub.sliceFamily_contDiff_infty hU_fam t) y).symm
    rw [he]
    refine continuous_finsetSum Finset.univ fun j _ => ?_
    let v : Space := EuclideanSpace.single j (1 : ℝ)
    have he2 : (fun z : ℝ × Space => dirSpatialJet (U z.1) [v, v] z.2) =
        fun z => fderiv ℝ (fun p : ℝ × Space =>
          fderiv ℝ (fun q : ℝ × Space => U q.1 q.2) p (0, v)) z (0, v) := by
      funext ⟨t, y⟩
      dsimp only
      have hd0 : ContDiff ℝ ∞ (fun q : ℝ × Space => U q.1 q.2) := hU_cd
      have hd1 : ContDiff ℝ ∞ (fun p : ℝ × Space =>
          fderiv ℝ (fun q : ℝ × Space => U q.1 q.2) p (0, v)) :=
        (hd0.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      have hpt1 : (fun y' : Space => dirSpatialJet (U t) [v] y') =
          fun y' => fderiv ℝ (fun q : ℝ × Space => U q.1 q.2) (t, y') (0, v) := by
        funext y'
        have hcomp1 : HasFDerivAt (fun x : Space => U t x)
            ((fderiv ℝ (fun q : ℝ × Space => U q.1 q.2) (t, y')).comp
              (ContinuousLinearMap.inr ℝ ℝ Space)) y' :=
          (((hd0.differentiable (by simp)) (t, y')).hasFDerivAt).comp y'
            (hasFDerivAt_prodMk_right t y')
        change fderiv ℝ (fun x : Space => U t x) y' v = _
        rw [hcomp1.fderiv]
        rfl
      change fderiv ℝ (fun y' => dirSpatialJet (U t) [v] y') y v = _
      rw [hpt1]
      have hcomp2 : HasFDerivAt
          (fun y' : Space => fderiv ℝ (fun q : ℝ × Space => U q.1 q.2) (t, y') (0, v))
          ((fderiv ℝ (fun p : ℝ × Space =>
            fderiv ℝ (fun q : ℝ × Space => U q.1 q.2) p (0, v)) (t, y)).comp
            (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
        (((hd1.differentiable (by simp)) (t, y)).hasFDerivAt).comp y
          (hasFDerivAt_prodMk_right t y)
      rw [hcomp2.fderiv]
      rfl
    rw [he2]
    exact (((hU_cd.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous_fderiv
      (by simp)).clm_apply continuous_const
  have hHvl_c : Continuous (fun z : ℝ × Space => UnforcedLeray.Heat.vlap (H z.1) z.2) := by
    have he : (fun z : ℝ × Space => UnforcedLeray.Heat.vlap (H z.1) z.2) =
        fun z => (Real.exp (z.1 / 2) * Real.exp (z.1 / 2) ^ 2) •
          UnforcedLeray.Heat.vlap (UnforcedLeray.Heat.average (ν * Real.exp z.1) a)
            (Real.exp (z.1 / 2) • z.2) :=
      funext fun ⟨t, y⟩ => UnforcedLeray.Heat.vlap_rescale _ _ y
    rw [he, continuous_iff_continuousAt]
    rintro ⟨t₀, y₀⟩
    have hT : 0 < ν * Real.exp t₀ := mul_pos hν (Real.exp_pos t₀)
    have hmap : Continuous (fun z : ℝ × Space =>
        (ν * Real.exp z.1, Real.exp (z.1 / 2) • z.2)) :=
      (continuous_const.mul (Real.continuous_exp.comp continuous_fst)).prodMk
        ((Real.continuous_exp.comp (continuous_fst.div_const 2)).smul continuous_snd)
    have hsc : Continuous (fun z : ℝ × Space => Real.exp (z.1 / 2)) :=
      Real.continuous_exp.comp (continuous_fst.div_const 2)
    exact (hsc.mul (hsc.pow 2)).continuousAt.smul
      (ContinuousAt.comp
        (g := fun z : ℝ × Space => UnforcedLeray.Heat.vlap (UnforcedLeray.Heat.average z.1 a) z.2)
        (f := fun z : ℝ × Space => (ν * Real.exp z.1, Real.exp (z.1 / 2) • z.2))
        (hInv2.continuousAt_vlap_joint hT (Real.exp (t₀ / 2) • y₀))
        hmap.continuousAt)
  exact ((hUfd_c.sub hHfd_c).const_smul (1 / 2 : ℝ)).add
    (((hUvl_c.sub hHvl_c).const_smul ν).add (hW_cont.const_smul (1 / 2 : ℝ)))

/-- Construction of the `L^{11/4}` Duhamel integral `I_q` and slicewise a.e. identification with
the `L²` Duhamel integral. -/
theorem duhamel_lq_exists (ν P : ℝ) (hν : 0 < ν)
    (G_sm : ℝ → SpatialField)
    (hG_cont : Continuous fun z : ℝ × Space => G_sm z.1 z.2)
    (hG_per : Function.Periodic G_sm P)
    {MG : ℝ} (hMG_pos : 0 ≤ MG)
    (hG_q0 : ∀ τ : ℝ, MemLp (G_sm τ) q0E volume ∧
      eLpNorm (G_sm τ) q0E volume ≤ ENNReal.ofReal MG)
    (hG_mem2 : ∀ τ : ℝ, MemLp (G_sm τ) 2 volume)
    (G₂ : ℝ → L2Space) {MG2 : ℝ}
    (hG2_norm : ∀ τ : ℝ, ‖G₂ τ‖ ≤ MG2)
    (hG_ae_G2 : ∀ τ : ℝ, G_sm τ =ᵐ[volume] (G₂ τ : SpatialField)) :
    ∃ (g_Lq : ℝ → Lp Space q0E (volume : Measure Space))
      (Kq : ℝ × ℝ → Lp Space q0E (volume : Measure Space))
      (I_q : ℝ → Lp Space q0E (volume : Measure Space)),
      (∀ s : ℝ, (g_Lq s : SpatialField) =ᵐ[volume] G_sm s) ∧
      (∀ s : ℝ, ‖g_Lq s‖ ≤ MG) ∧
      StronglyMeasurable Kq ∧
      (∀ (t r : ℝ), 0 < r → Kq (t, r) = freeSemigroupLp q0E_ne_top ν r (g_Lq (t - r))) ∧
      (∀ τ : ℝ, IntegrableOn (fun r : ℝ => freeSemigroupLp q0E_ne_top ν r (g_Lq (τ - r)))
        (Ioi (0 : ℝ)) volume) ∧
      (∀ τ : ℝ, I_q τ = ∫ r in Ioi (0 : ℝ), freeSemigroupLp q0E_ne_top ν r (g_Lq (τ - r))) ∧
      StronglyMeasurable I_q ∧
      Function.Periodic I_q P ∧
      (∀ τ : ℝ, ‖I_q τ‖ ≤ 22 * MG) ∧
      (∀ τ : ℝ,
        (((∫ r in Ioi (0 : ℝ), UnforcedLeray.Loc.L02.freeL2 ν r (G₂ (τ - r)) : L2Space) :
          SpatialField) =ᵐ[volume] (I_q τ : SpatialField))) := by
  have : Fact (q0E ≠ ⊤) := ⟨q0E_ne_top⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let g_Lq : ℝ → Lp Space q0E (volume : Measure Space) := fun s => (hG_q0 s).1.toLp (G_sm s)
  have hg_Lq_ae : ∀ s : ℝ, (g_Lq s : SpatialField) =ᵐ[volume] G_sm s := fun s =>
    (hG_q0 s).1.coeFn_toLp
  have hg_Lq_eq : g_Lq = UnforcedLeray.BochnerTime.toPathLq q0E volume
      (fun z : ℝ × Space => G_sm z.1 z.2) :=
    funext fun s => (UnforcedLeray.BochnerTime.toPathLq_of_memLp
      (f := fun z : ℝ × Space => G_sm z.1 z.2) (t := s) (hG_q0 s).1).symm
  have hg_Lq_sm : StronglyMeasurable g_Lq := by
    rw [hg_Lq_eq]
    exact UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq hG_cont.stronglyMeasurable
  have hg_Lq_per : Function.Periodic g_Lq P := by
    intro s
    exact MemLp.toLp_congr (hG_q0 (s + P)).1 (hG_q0 s).1
      (Eventually.of_forall fun y => congrFun (hG_per s) y)
  have hg_Lq_norm : ∀ s : ℝ, ‖g_Lq s‖ ≤ MG := by
    intro s
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal hMG_pos (hG_q0 s).2
  have hG2_eq : G₂ = UnforcedLeray.BochnerTime.toPathLq 2 volume
      (fun z : ℝ × Space => G_sm z.1 z.2) := by
    funext s
    rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp
      (f := fun z : ℝ × Space => G_sm z.1 z.2) (t := s) (hG_mem2 s)]
    apply Lp.ext
    exact (hG_ae_G2 s).symm.trans (hG_mem2 s).coeFn_toLp.symm
  have hG2_sm : StronglyMeasurable G₂ := by
    rw [hG2_eq]
    exact UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq hG_cont.stronglyMeasurable
  let Kq : ℝ × ℝ → Lp Space q0E (volume : Measure Space) := fun z =>
    freeSemigroupLp q0E_ne_top ν (max z.2 0) (g_Lq (z.1 - z.2))
  let K2 : ℝ × ℝ → L2Space := fun z =>
    freeSemigroupLp ENNReal.ofNat_ne_top ν (max z.2 0) (G₂ (z.1 - z.2))
  have hKq_sm : StronglyMeasurable Kq :=
    Continuous.comp_stronglyMeasurable
      (g := fun p : ℝ × Lp Space q0E (volume : Measure Space) =>
        freeSemigroupLp q0E_ne_top ν (max p.1 0) p.2)
      (f := fun z : ℝ × ℝ => (z.2, g_Lq (z.1 - z.2)))
      (continuous_freeSemigroupLp_max q0E_ne_top hν (by rw [gammaExp_q0E]; norm_num))
      (continuous_snd.stronglyMeasurable.prodMk
        (hg_Lq_sm.comp_measurable (measurable_fst.sub measurable_snd)))
  have hK2_sm : StronglyMeasurable K2 :=
    Continuous.comp_stronglyMeasurable
      (g := fun p : ℝ × L2Space => freeSemigroupLp ENNReal.ofNat_ne_top ν (max p.1 0) p.2)
      (f := fun z : ℝ × ℝ => (z.2, G₂ (z.1 - z.2)))
      (continuous_freeSemigroupLp_max ENNReal.ofNat_ne_top hν
        (by rw [UnforcedLeray.Loc.L02.gammaExp_two]; norm_num))
      (continuous_snd.stronglyMeasurable.prodMk
        (hG2_sm.comp_measurable (measurable_fst.sub measurable_snd)))
  have hKq_pos : ∀ (t r : ℝ), 0 < r → Kq (t, r) = freeSemigroupLp q0E_ne_top ν r (g_Lq (t - r)) :=
    fun t r hr => by
      dsimp only [Kq]
      rw [max_eq_left hr.le]
  let I_q : ℝ → Lp Space q0E (volume : Measure Space) := fun τ =>
    ∫ r in Ioi (0 : ℝ), freeSemigroupLp q0E_ne_top ν r (g_Lq (τ - r))
  let I₂ : ℝ → L2Space := fun τ =>
    ∫ r in Ioi (0 : ℝ), UnforcedLeray.Loc.L02.freeL2 ν r (G₂ (τ - r))
  have hIq_eq_Kq : ∀ τ : ℝ, I_q τ = ∫ r in Ioi (0 : ℝ), Kq (τ, r) := fun τ =>
    setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => (hKq_pos τ r hr).symm
  have hIq_int : ∀ τ : ℝ,
      IntegrableOn (fun r : ℝ => freeSemigroupLp q0E_ne_top ν r (g_Lq (τ - r)))
        (Ioi (0 : ℝ)) volume := by
    intro τ
    have hmr : Measurable (fun r : ℝ => (τ, r)) :=
      (continuous_const.prodMk continuous_id).measurable
    have hsm_r : AEStronglyMeasurable
        (fun r : ℝ => freeSemigroupLp q0E_ne_top ν r (g_Lq (τ - r)))
        (volume.restrict (Ioi (0 : ℝ))) := by
      refine (hKq_sm.comp_measurable hmr).aestronglyMeasurable.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : 0 < r)
      exact hKq_pos τ r hr
    have hexp : IntegrableOn (fun r : ℝ => Real.exp (-(1 / 22 : ℝ) * r) * MG) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by norm_num) 0).mul_const MG
    refine hexp.mono' hsm_r ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (_hr : 0 < r)
    calc ‖freeSemigroupLp q0E_ne_top ν r (g_Lq (τ - r))‖
        ≤ ‖freeSemigroupLp q0E_ne_top ν r‖ * ‖g_Lq (τ - r)‖ :=
          (freeSemigroupLp q0E_ne_top ν r).le_opNorm _
      _ ≤ Real.exp (-gammaExp q0E * r) * MG :=
          mul_le_mul (norm_freeSemigroupLp_le q0E_ne_top ν r) (hg_Lq_norm (τ - r))
            (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-(1 / 22 : ℝ) * r) * MG := by rw [gammaExp_q0E]
  have hI2_int : ∀ τ : ℝ,
      IntegrableOn (fun r : ℝ => UnforcedLeray.Loc.L02.freeL2 ν r (G₂ (τ - r)))
        (Ioi (0 : ℝ)) volume := by
    intro τ
    have hmr : Measurable (fun r : ℝ => (τ, r)) :=
      (continuous_const.prodMk continuous_id).measurable
    have hsm_r : AEStronglyMeasurable
        (fun r : ℝ => UnforcedLeray.Loc.L02.freeL2 ν r (G₂ (τ - r)))
        (volume.restrict (Ioi (0 : ℝ))) := by
      refine (hK2_sm.comp_measurable hmr).aestronglyMeasurable.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : 0 < r)
      change K2 (τ, r) = UnforcedLeray.Loc.L02.freeL2 ν r (G₂ (τ - r))
      dsimp only [K2, UnforcedLeray.Loc.L02.freeL2]
      rw [max_eq_left hr.le]
    have hexp : IntegrableOn (fun r : ℝ => Real.exp (-(1 / 4 : ℝ) * r) * max MG2 0)
        (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by norm_num) 0).mul_const (max MG2 0)
    refine hexp.mono' hsm_r ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (_hr : 0 < r)
    calc ‖UnforcedLeray.Loc.L02.freeL2 ν r (G₂ (τ - r))‖
        ≤ ‖UnforcedLeray.Loc.L02.freeL2 ν r‖ * ‖G₂ (τ - r)‖ :=
          (UnforcedLeray.Loc.L02.freeL2 ν r).le_opNorm _
      _ ≤ Real.exp (-(r / 4)) * max MG2 0 :=
          mul_le_mul (UnforcedLeray.Loc.L02.norm_freeL2_le ν r)
            ((hG2_norm (τ - r)).trans (le_max_left _ _))
            (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-(1 / 4 : ℝ) * r) * max MG2 0 := by ring_nf
  have hI2_ae_Iq : ∀ τ : ℝ, (I₂ τ : SpatialField) =ᵐ[volume] (I_q τ : SpatialField) := by
    intro τ
    refine ae_eq_of_realSpatialTestCLM_eq (I₂ τ) (I_q τ) fun ψ hψ hψc i => ?_
    rw [← (realSpatialTestCLM 2 hψ hψc i).integral_comp_comm (hI2_int τ),
      ← (realSpatialTestCLM q0E hψ hψc i).integral_comp_comm (hIq_int τ)]
    refine setIntegral_congr_fun measurableSet_Ioi fun r (_hr : 0 < r) => ?_
    rw [realSpatialTestCLM_apply, realSpatialTestCLM_apply]
    refine integral_congr_ae ?_
    have hae2 := (UnforcedLeray.Loc.L02.coeFn_freeL2 ν r (G₂ (τ - r))).trans
      (freeEvolution_congr_ae (hG_ae_G2 (τ - r)).symm ν r)
    have haeq := (coeFn_freeSemigroupLp q0E_ne_top ν r (g_Lq (τ - r))).trans
      (freeEvolution_congr_ae (hg_Lq_ae (τ - r)) ν r)
    filter_upwards [hae2, haeq] with y hy2 hyq
    rw [hy2, hyq]
  have hIq_sm : StronglyMeasurable I_q := by
    have heq : I_q = fun τ => ∫ r in Ioi (0 : ℝ), Kq (τ, r) := funext hIq_eq_Kq
    rw [heq]
    exact hKq_sm.integral_prod_right'
  have hIq_per : Function.Periodic I_q P := by
    intro τ
    dsimp [I_q]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    have hsh : τ + P - r = τ - r + P := by ring
    rw [hsh, hg_Lq_per (τ - r)]
  have hIq_norm : ∀ τ : ℝ, ‖I_q τ‖ ≤ 22 * MG := by
    intro τ
    have hexp : IntegrableOn (fun r : ℝ => Real.exp (-(1 / 22 : ℝ) * r) * MG) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by norm_num) 0).mul_const MG
    have hbd := norm_integral_le_of_norm_le hexp (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (_hr : 0 < r)
      calc ‖freeSemigroupLp q0E_ne_top ν r (g_Lq (τ - r))‖
          ≤ Real.exp (-gammaExp q0E * r) * MG :=
            ((freeSemigroupLp q0E_ne_top ν r).le_opNorm _).trans
              (mul_le_mul (norm_freeSemigroupLp_le q0E_ne_top ν r) (hg_Lq_norm (τ - r))
                (norm_nonneg _) (Real.exp_pos _).le)
        _ = Real.exp (-(1 / 22 : ℝ) * r) * MG := by rw [gammaExp_q0E])
    have hval : ∫ r in Ioi (0 : ℝ), Real.exp (-(1 / 22 : ℝ) * r) * MG = 22 * MG := by
      rw [integral_mul_const, integral_exp_mul_Ioi (by norm_num) 0]
      norm_num
    exact hbd.trans_eq hval
  exact ⟨g_Lq, Kq, I_q, hg_Lq_ae, hg_Lq_norm, hKq_sm, hKq_pos, hIq_int,
    fun _ => rfl, hIq_sm, hIq_per, hIq_norm, hI2_ae_Iq⟩

/-- Slicewise identification of the `L²` Duhamel integral with `W τ` at almost every `τ : ℝ`
once `w = Rm g_q` in `Yq P q0E`. -/
theorem duhamel_ae_of_resolvent {ν P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hP : 0 < P)
    (W : ℝ → SpatialField) (w : Yq P q0E)
    (hw_rep : HasRep w (fun z : ℝ × Space => realC (W z.1 z.2)))
    (G_sm : ℝ → SpatialField)
    (hG_cont : Continuous fun z : ℝ × Space => G_sm z.1 z.2)
    (hG_per : Function.Periodic G_sm P)
    {MG : ℝ} (hMG_pos : 0 ≤ MG)
    (hG_q0 : ∀ τ : ℝ, MemLp (G_sm τ) q0E volume ∧
      eLpNorm (G_sm τ) q0E volume ≤ ENNReal.ofReal MG)
    (hG_mem2 : ∀ τ : ℝ, MemLp (G_sm τ) 2 volume)
    (G₂ : ℝ → L2Space) {MG2 : ℝ}
    (hG2_norm : ∀ τ : ℝ, ‖G₂ τ‖ ≤ MG2)
    (hG_ae_G2 : ∀ τ : ℝ, G_sm τ =ᵐ[volume] (G₂ τ : SpatialField))
    (g_q : Yq P q0E)
    (hg_rep : HasRep g_q (fun z : ℝ × Space => realC (G_sm z.1 z.2)))
    (Rm : Yq P q0E →L[ℂ] Yq P q0E)
    (hRm : ∀ f : Yq P q0E,
      Rm f = ∫ r in Ioi (0 : ℝ), Complex.exp (-((0 : ℂ) * r)) • phaseT q0E_ne_top ν r f)
    (hw_eq_Rm : w = Rm g_q) :
    ∀ᵐ τ : ℝ,
      (((∫ r in Ioi (0 : ℝ), UnforcedLeray.Loc.L02.freeL2 ν r (G₂ (τ - r)) : L2Space) :
          SpatialField) =ᵐ[volume] W τ) := by
  obtain ⟨g_Lq, Kq, I_q, hg_Lq_ae, hg_Lq_norm, hKq_sm, hKq_pos, hIq_int, hIq_def,
      hIq_sm, hIq_per, hIq_norm, hI2_ae_Iq⟩ :=
    duhamel_lq_exists ν P hν G_sm hG_cont hG_per hMG_pos hG_q0 hG_mem2 G₂ hG2_norm hG_ae_G2
  let Wc : ℝ × Space → CVec3 := fun z => realC (W z.1 z.2)
  let c_path : ℝ → Lp CVec3 q0E (volume : Measure Space) :=
    fun τ => ofReV.compLpL q0E volume (I_q τ)
  have hc_sm : StronglyMeasurable c_path :=
    Continuous.comp_stronglyMeasurable
      (g := ofReV.compLpL q0E (volume : Measure Space)) (f := I_q)
      (ofReV.compLpL q0E (volume : Measure Space)).continuous hIq_sm
  have hc_per : Function.Periodic c_path P := fun τ => by
    simp only [c_path, hIq_per τ]
  let C_c : ℝ := ‖ofReV.compLpL q0E (volume : Measure Space)‖ * (22 * MG)
  have hc_norm : ∀ τ : ℝ, ‖c_path τ‖ ≤ C_c := fun τ =>
    ((ofReV.compLpL q0E volume).le_opNorm (I_q τ)).trans
      (mul_le_mul_of_nonneg_left (hIq_norm τ) (norm_nonneg _))
  let c_cir : AddCircle P → Lp CVec3 q0E (volume : Measure Space) :=
    fun θ => c_path (UnforcedLeray.Short.PartIIa.pfyRho P θ)
  have hc_cir_sm : StronglyMeasurable c_cir :=
    hc_sm.comp_measurable (UnforcedLeray.Short.PartIIa.pfyRho_measurable P)
  have hc_cir_aesm : AEStronglyMeasurable c_cir (AddCircle.haarAddCircle (T := P)) :=
    hc_cir_sm.aestronglyMeasurable
  have hc_cir_bd : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)), ‖c_cir θ‖ ≤ C_c :=
    Eventually.of_forall fun θ => hc_norm (UnforcedLeray.Short.PartIIa.pfyRho P θ)
  have hc_cir_mem : MemLp c_cir q0E (AddCircle.haarAddCircle (T := P)) :=
    MemLp.of_bound hc_cir_aesm C_c hc_cir_bd
  let u_I : Yq P q0E := hc_cir_mem.toLp c_cir
  have hc_cir_coe : ∀ t : ℝ, c_cir (t : AddCircle P) = c_path t := by
    intro t
    obtain ⟨n, hn⟩ := UnforcedLeray.Short.PartIIa.pfyRho_coe P t
    change c_path (UnforcedLeray.Short.PartIIa.pfyRho P (t : AddCircle P)) = c_path t
    rw [hn]
    simpa [mul_comm] using hc_per.int_mul n t
  have huI_slice : ∀ᵐ t : ℝ, u_I (t : AddCircle P) = c_path t := by
    filter_upwards [ae_comp_mk (P := P) hc_cir_mem.coeFn_toLp] with t ht
    rw [ht, hc_cir_coe t]
  have hgq_slice : ∀ᵐ s : ℝ,
      g_q (s : AddCircle P) = ofReV.compLpL q0E volume (g_Lq s) := by
    filter_upwards [hg_rep.slice] with s hs
    apply Lp.ext
    filter_upwards [hs, ofReV.coeFn_compLpL (p := q0E) (μ := (volume : Measure Space)) (g_Lq s),
      hg_Lq_ae s] with y hy1 hy2 hy3
    rw [← hy1, hy2, hy3]
    exact PointwiseDerivSub.realC_eq_ofReV (G_sm s y)
  have huI_eq_Rm : u_I = Rm g_q := by
    refine eq_of_forall_phasePair fun Φ hΦ => ?_
    have hs := hΦ.sliceCont (conjExp q0E)
    have hpair_inner : ∀ f : Yq P q0E,
        phasePair P q0E Φ f =
          P⁻¹ • ∫ t in Ioc (0 : ℝ) (0 + P), innerPair q0E (sliceMap hs t) (f (t : AddCircle P)) := by
      intro f
      rw [phasePair_eq_periodIntegral hΦ f]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      rw [innerPair_apply]
      refine integral_congr_ae ?_
      filter_upwards [(hs.memLp t).coeFn_toLp] with y hy
      simp only [sliceMap]
      rw [hy]
    have hLHS : phasePair P q0E Φ u_I =
        P⁻¹ • ∫ t in Ioc (0 : ℝ) (0 + P),
          ∫ r in Ioi (0 : ℝ),
            innerPair q0E (sliceMap hs t)
              (ofReV.compLpL q0E volume
                (freeSemigroupLp q0E_ne_top ν r (g_Lq (t - r)))) := by
      rw [hpair_inner u_I]
      congr 1
      refine setIntegral_congr_ae measurableSet_Ioc ?_
      filter_upwards [huI_slice] with t ht _
      rw [ht]
      change innerPair q0E (sliceMap hs t) (ofReV.compLpL q0E volume (I_q t)) = _
      rw [hIq_def t]
      let L_t : Lp Space q0E (volume : Measure Space) →L[ℝ] ℂ :=
        ((innerPair q0E (sliceMap hs t)).restrictScalars ℝ).comp (ofReV.compLpL q0E volume)
      exact (L_t.integral_comp_comm (hIq_int t)).symm
    have hRm_int : IntegrableOn
        (fun r : ℝ => Complex.exp (-((0 : ℂ) * r)) • phaseT q0E_ne_top ν r g_q)
        (Ioi (0 : ℝ)) volume := by
      have hcont : ContinuousOn
          (fun r : ℝ => Complex.exp (-((0 : ℂ) * r)) • phaseT q0E_ne_top ν r g_q)
          (Ioi (0 : ℝ)) := by
        have hc1 : Continuous (fun r : ℝ => Complex.exp (-((0 : ℂ) * (r : ℂ)))) := by fun_prop
        exact hc1.continuousOn.smul
          ((continuousOn_phaseT q0E_ne_top hν.le g_q).mono Ioi_subset_Ici_self)
      have hexp : IntegrableOn (fun r : ℝ => 2 * Real.exp (-(1 / 22 : ℝ) * r) * ‖g_q‖)
          (Ioi (0 : ℝ)) :=
        ((integrableOn_exp_mul_Ioi (by norm_num) 0).const_mul 2).mul_const ‖g_q‖
      refine hexp.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (_hr : 0 < r)
      simp only [zero_mul, neg_zero, Complex.exp_zero, one_smul]
      calc ‖phaseT q0E_ne_top ν r g_q‖
          ≤ ‖phaseT q0E_ne_top ν r‖ * ‖g_q‖ := (phaseT q0E_ne_top ν r).le_opNorm g_q
        _ ≤ (2 * Real.exp (-gammaExp q0E * r)) * ‖g_q‖ :=
            mul_le_mul ((norm_phaseT_le q0E_ne_top ν r).trans (norm_freeC_le q0E_ne_top ν r))
              le_rfl (norm_nonneg _) (by positivity)
        _ = 2 * Real.exp (-(1 / 22 : ℝ) * r) * ‖g_q‖ := by rw [gammaExp_q0E]
    have hRHS : phasePair P q0E Φ (Rm g_q) =
        P⁻¹ • ∫ r in Ioi (0 : ℝ),
          ∫ t in Ioc (0 : ℝ) (0 + P),
            innerPair q0E (sliceMap hs t)
              (ofReV.compLpL q0E volume
                (freeSemigroupLp q0E_ne_top ν r (g_Lq (t - r)))) := by
      rw [hRm g_q, ← (phasePair P q0E Φ).integral_comp_comm hRm_int]
      have h1 : (∫ r in Ioi (0 : ℝ),
          phasePair P q0E Φ (Complex.exp (-((0 : ℂ) * r)) • phaseT q0E_ne_top ν r g_q)) =
          ∫ r in Ioi (0 : ℝ),
            P⁻¹ • ∫ t in Ioc (0 : ℝ) (0 + P),
              innerPair q0E (sliceMap hs t)
                (ofReV.compLpL q0E volume
                  (freeSemigroupLp q0E_ne_top ν r (g_Lq (t - r)))) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun r (_hr : 0 < r) => ?_
        simp only [zero_mul, neg_zero, Complex.exp_zero, one_smul]
        rw [hpair_inner (phaseT q0E_ne_top ν r g_q)]
        congr 1
        refine setIntegral_congr_ae measurableSet_Ioc ?_
        have hsh_ae : ∀ᵐ t : ℝ,
            g_q ((t - r : ℝ) : AddCircle P) = ofReV.compLpL q0E volume (g_Lq (t - r)) :=
          (measurePreserving_sub_right volume r).quasiMeasurePreserving.ae hgq_slice
        filter_upwards [ae_comp_mk (P := P) (coeFn_phaseT q0E_ne_top ν r g_q), hsh_ae]
          with t ht1 ht2 _
        have hsub_coe : ((t - r : ℝ) : AddCircle P) = (t : AddCircle P) - (r : AddCircle P) :=
          AddCircle.coe_sub P t r
        rw [ht1, ← hsub_coe, ht2, freeC_ofReV_compLpL]
      rw [h1, integral_smul]
    let F_tr : ℝ × ℝ → ℂ := fun z =>
      innerPair q0E (sliceMap hs z.1) (ofReV.compLpL q0E volume (Kq z))
    have hF_sm : StronglyMeasurable F_tr := by
      have hsm1 : StronglyMeasurable (fun z : ℝ × ℝ => sliceMap hs z.1) :=
        (hs.continuous.comp continuous_fst).stronglyMeasurable
      have hsm2 : StronglyMeasurable
          (fun z : ℝ × ℝ => ofReV.compLpL q0E (volume : Measure Space) (Kq z)) :=
        Continuous.comp_stronglyMeasurable
          (g := ofReV.compLpL q0E (volume : Measure Space)) (f := Kq)
          (ofReV.compLpL q0E (volume : Measure Space)).continuous hKq_sm
      have hbil : Continuous
          (fun p : Lp CVec3 (conjExp q0E) (volume : Measure Space) ×
            Lp CVec3 q0E (volume : Measure Space) => innerPair q0E p.1 p.2) :=
        (innerPair q0E).isBoundedBilinearMap.continuous
      exact Continuous.comp_stronglyMeasurable
        (g := fun p : Lp CVec3 (conjExp q0E) (volume : Measure Space) ×
          Lp CVec3 q0E (volume : Measure Space) => innerPair q0E p.1 p.2)
        (f := fun z : ℝ × ℝ => (sliceMap hs z.1, ofReV.compLpL q0E volume (Kq z)))
        hbil (hsm1.prodMk hsm2)
    obtain ⟨C_Φ, hC_Φ⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun t : ℝ => sliceMap hs t) hs.continuous.continuousOn
    have hC_Φ0 : 0 ≤ C_Φ := (norm_nonneg (sliceMap hs 0)).trans
      (hC_Φ 0 ⟨le_rfl, (lt_add_of_pos_right 0 hP).le⟩)
    let C_prod : ℝ := ‖innerPair q0E‖ * C_Φ * ‖ofReV.compLpL q0E (volume : Measure Space)‖ * MG
    have hF_prod_int : Integrable F_tr
        (((volume : Measure ℝ).restrict (Ioc 0 (0 + P))).prod
          ((volume : Measure ℝ).restrict (Ioi 0))) := by
      have hmaj1 : Integrable (fun _ : ℝ => C_prod)
          ((volume : Measure ℝ).restrict (Ioc 0 (0 + P))) :=
        integrableOn_const (C := C_prod) (hs := measure_Ioc_lt_top.ne) (hC := enorm_ne_top)
      have hmaj2 : Integrable (fun r : ℝ => Real.exp (-(1 / 22 : ℝ) * r))
          ((volume : Measure ℝ).restrict (Ioi 0)) :=
        integrableOn_exp_mul_Ioi (by norm_num) 0
      have hmaj : Integrable (fun z : ℝ × ℝ => C_prod * Real.exp (-(1 / 22 : ℝ) * z.2))
          (((volume : Measure ℝ).restrict (Ioc 0 (0 + P))).prod
            ((volume : Measure ℝ).restrict (Ioi 0))) :=
        hmaj1.mul_prod hmaj2
      refine hmaj.mono' hF_sm.aestronglyMeasurable ?_
      rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)]
        with ⟨t, r⟩ ⟨ht, (hr : 0 < r)⟩
      have ht_cc : t ∈ Icc (0 : ℝ) (0 + P) := Ioc_subset_Icc_self ht
      have hKq_n : ‖Kq (t, r)‖ ≤ Real.exp (-(1 / 22 : ℝ) * r) * MG := by
        rw [hKq_pos t r hr]
        calc ‖freeSemigroupLp q0E_ne_top ν r (g_Lq (t - r))‖
            ≤ Real.exp (-gammaExp q0E * r) * MG :=
              ((freeSemigroupLp q0E_ne_top ν r).le_opNorm _).trans
                (mul_le_mul (norm_freeSemigroupLp_le q0E_ne_top ν r) (hg_Lq_norm (t - r))
                  (norm_nonneg _) (Real.exp_pos _).le)
          _ = Real.exp (-(1 / 22 : ℝ) * r) * MG := by rw [gammaExp_q0E]
      dsimp [F_tr]
      calc ‖innerPair q0E (sliceMap hs t) (ofReV.compLpL q0E volume (Kq (t, r)))‖
          ≤ ‖innerPair q0E‖ * ‖sliceMap hs t‖ * ‖ofReV.compLpL q0E volume (Kq (t, r))‖ := by
            have h1 := (innerPair q0E (sliceMap hs t)).le_opNorm
              (ofReV.compLpL q0E volume (Kq (t, r)))
            have h2 := (innerPair q0E).le_opNorm (sliceMap hs t)
            exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
        _ ≤ ‖innerPair q0E‖ * C_Φ *
              (‖ofReV.compLpL q0E (volume : Measure Space)‖ *
                (Real.exp (-(1 / 22 : ℝ) * r) * MG)) := by
            refine mul_le_mul
              (mul_le_mul_of_nonneg_left (hC_Φ t ht_cc) (norm_nonneg (innerPair q0E))) ?_
              (norm_nonneg (ofReV.compLpL q0E volume (Kq (t, r))))
              (mul_nonneg (norm_nonneg (innerPair q0E)) hC_Φ0)
            exact ((ofReV.compLpL q0E volume).le_opNorm _).trans
              (mul_le_mul_of_nonneg_left hKq_n
                (norm_nonneg (ofReV.compLpL q0E (volume : Measure Space))))
        _ = C_prod * Real.exp (-(1 / 22 : ℝ) * r) := by dsimp [C_prod]; ring
    have hfub : (∫ t in Ioc (0 : ℝ) (0 + P), ∫ r in Ioi (0 : ℝ), F_tr (t, r)) =
        ∫ r in Ioi (0 : ℝ), ∫ t in Ioc (0 : ℝ) (0 + P), F_tr (t, r) :=
      (integral_prod F_tr hF_prod_int).symm.trans (integral_prod_symm F_tr hF_prod_int)
    have hL_eq : (∫ t in Ioc (0 : ℝ) (0 + P), ∫ r in Ioi (0 : ℝ),
        innerPair q0E (sliceMap hs t)
          (ofReV.compLpL q0E volume (freeSemigroupLp q0E_ne_top ν r (g_Lq (t - r))))) =
        ∫ t in Ioc (0 : ℝ) (0 + P), ∫ r in Ioi (0 : ℝ), F_tr (t, r) :=
      setIntegral_congr_fun measurableSet_Ioc fun t _ =>
        setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => by
          dsimp only [F_tr]
          rw [hKq_pos t r hr]
    have hR_eq : (∫ r in Ioi (0 : ℝ), ∫ t in Ioc (0 : ℝ) (0 + P),
        innerPair q0E (sliceMap hs t)
          (ofReV.compLpL q0E volume (freeSemigroupLp q0E_ne_top ν r (g_Lq (t - r))))) =
        ∫ r in Ioi (0 : ℝ), ∫ t in Ioc (0 : ℝ) (0 + P), F_tr (t, r) :=
      setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) =>
        setIntegral_congr_fun measurableSet_Ioc fun t _ => by
          dsimp only [F_tr]
          rw [hKq_pos t r hr]
    rw [hLHS, hRHS, hL_eq, hR_eq, hfub]
  have huI_eq_w : u_I = w := huI_eq_Rm.trans hw_eq_Rm.symm
  filter_upwards [huI_slice, hw_rep.slice] with τ hτ_uI hτ_w
  rw [huI_eq_w] at hτ_uI
  have hIq_ae_W : (I_q τ : SpatialField) =ᵐ[volume] W τ := by
    filter_upwards [hτ_w,
      ofReV.coeFn_compLpL (p := q0E) (μ := (volume : Measure Space)) (I_q τ)] with y hy_w hy_iq
    have h1 : Wc (τ, y) = (c_path τ : Space → CVec3) y := by
      change realC (W τ y) = (c_path τ : Space → CVec3) y
      rw [hy_w, hτ_uI]
    have h2 : ofReV (W τ y) = ofReV ((I_q τ : SpatialField) y) := by
      rw [← PointwiseDerivSub.realC_eq_ofReV, ← hy_iq]
      exact h1
    exact (reV_ofReV ((I_q τ : SpatialField) y)).symm.trans
      ((congrArg reV h2.symm).trans (reV_ofReV (W τ y)))
  exact (hI2_ae_Iq τ).trans hIq_ae_W

/-! ## 6. Main proof of `FreeDuhamelUniquenessAe` -/

private lemma vec3_sub_add_add {V : Type*} [AddCommGroup V] (A B C D : V) :
    A - (B + (C + D)) = A - B - C - D := by
  rw [sub_add_eq_sub_sub, sub_add_eq_sub_sub]

theorem spatialProjectedLin_eq_vlap (ν : ℝ) {F : SpatialField} (hF : ContDiff ℝ ∞ F) (y : Space) :
    spatialProjectedLin ν F y =
      (1 / 2 : ℝ) • fderiv ℝ F y y +
        (ν • UnforcedLeray.Heat.vlap F y + (1 / 2 : ℝ) • F y) := by
  unfold spatialProjectedLin spatialDiffReact spatialRadialDrift
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [spatialLaplacian_eq_vlap hF y]

/-- Smooth convective Leray source `-smoothConvectiveLeray U U` supplies a jointly continuous,
`P`-periodic representative in `L² ∩ L^{11/4}` agreeing slicewise a.e. with `-𝐏(U · ∇U)`. -/
theorem convectiveSource_props {P : ℝ} {U : ℝ → SpatialField}
    (hU_cd : ContDiff ℝ ∞ (fun z : ℝ × Space => U z.1 z.2))
    (hU_fam : IsUniformSmoothL4SliceFamily U)
    (hU_per : Function.Periodic U P) :
    ∃ (G_sm : ℝ → SpatialField) (MG MG2 : ℝ),
      0 ≤ MG ∧
      Continuous (fun z : ℝ × Space => G_sm z.1 z.2) ∧
      Function.Periodic G_sm P ∧
      (∀ τ : ℝ, MemLp (G_sm τ) q0E volume ∧
        eLpNorm (G_sm τ) q0E volume ≤ ENNReal.ofReal MG) ∧
      (∀ τ : ℝ, MemLp (G_sm τ) 2 volume) ∧
      (∀ τ : ℝ,
        ‖(-(UnforcedLeray.Leray.projection (UnforcedLeray.toL2
          (fun y => fderiv ℝ (U τ) y (U τ y)))) : L2Space)‖ ≤ MG2) ∧
      (∀ τ : ℝ, G_sm τ =ᵐ[volume]
        ((-(UnforcedLeray.Leray.projection (UnforcedLeray.toL2
          (fun y => fderiv ℝ (U τ) y (U τ y)))) : L2Space) : SpatialField)) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
  let F : ℝ → SpatialField := fun τ => spatialConvect (U τ) (U τ)
  let G_sm : ℝ → SpatialField := fun τ y => -smoothConvectiveLeray U U τ y
  let G₂ : ℝ → L2Space := fun τ =>
    -(UnforcedLeray.Leray.projection (UnforcedLeray.toL2 (fun y => fderiv ℝ (U τ) y (U τ y))))
  have hF_fam : IsUniformSmoothL4SliceFamily F :=
    HigherPhaseSub.sliceFamily_spatialConvect hU_fam hU_fam
  have hG_fam : IsUniformSmoothL4SliceFamily G_sm := by
    have h1 := HigherPhaseSub.sliceFamily_smul (-1 : ℝ)
      (HigherPhaseSub.sliceFamily_smoothConvectiveLeray smoothLeraySliceRegularity_proof
        U U hU_fam hU_fam)
    rw [neg_one_smul] at h1
    exact h1
  have hJ : LerayContSub.JetCont U :=
    fun vs => CorrComovingSub.continuous_dirSpatialJet_of_joint hU_cd vs
  have hF_cont : Continuous fun z : ℝ × Space => F z.1 z.2 :=
    LerayContSub.jetCont_spatialConvect
      (HigherPhaseSub.sliceFamily_contDiff_infty hU_fam)
      (HigherPhaseSub.sliceFamily_contDiff_infty hU_fam) hJ hJ []
  have hG_cont : Continuous fun z : ℝ × Space => G_sm z.1 z.2 :=
    (LerayContSub.continuous_smoothLeraySlice hF_fam hF_cont).neg
  have hG_per : Function.Periodic G_sm P := by
    intro τ
    have hF_per : F (τ + P) = F τ := by
      funext y
      simp only [F, spatialConvect, hU_per τ]
    funext y
    change -smoothLerayProj (F (τ + P)) y = -smoothLerayProj (F τ) y
    rw [hF_per]
  obtain ⟨MU0, hMU0⟩ := hU_fam.l4_bounded 0
  obtain ⟨MU1, hMU1⟩ := hU_fam.l4_bounded 1
  let CU : ℝ := max MU0 MU1
  have hF_l2 : ∀ τ : ℝ, MemLp (F τ) 2 volume ∧
      UnforcedLeray.l2Norm (F τ) ≤ 1 * max CU 0 ^ 2 := by
    intro τ
    have hUs := HigherPhaseSub.sliceFamily_contDiff_infty hU_fam τ
    refine B3RemH2Sub.memLp_two_of_mul_l4 (g := F τ)
      (HigherPhaseSub.sliceFamily_contDiff_infty hF_fam τ).continuous
      hUs.continuous.norm ((hUs.continuous_fderiv (by simp)).norm)
      (c := 1) (C := CU) zero_le_one
      (by
        have h0_eq : eLpNorm (fun x => ‖U τ x‖) 4 volume =
            eLpNorm (fun y => iteratedFDeriv ℝ 0 (U τ) y) 4 volume :=
          eLpNorm_congr_norm_ae (Eventually.of_forall fun y => by
            rw [Real.norm_of_nonneg (norm_nonneg _), norm_iteratedFDeriv_zero])
        exact h0_eq.trans_le ((hMU0 τ).trans (ENNReal.ofReal_le_ofReal (le_max_left MU0 MU1))))
      (by
        have h1_eq : eLpNorm (fun x => ‖fderiv ℝ (U τ) x‖) 4 volume =
            eLpNorm (fun y => iteratedFDeriv ℝ 1 (U τ) y) 4 volume :=
          eLpNorm_congr_norm_ae (Eventually.of_forall fun y => by
            rw [Real.norm_of_nonneg (norm_nonneg _), norm_iteratedFDeriv_one])
        exact h1_eq.trans_le ((hMU1 τ).trans (ENNReal.ofReal_le_ofReal (le_max_right MU0 MU1))))
      fun y => by
        rw [one_mul, mul_comm]
        exact ContinuousLinearMap.le_opNorm (fderiv ℝ (U τ) y) (U τ y)
  have hG_ae_G2 : ∀ τ : ℝ, G_sm τ =ᵐ[volume] (G₂ τ : SpatialField) := by
    intro τ
    obtain ⟨hF4, _, hrep⟩ := (smoothLeraySliceRegularity_proof.1 F hF_fam).1 τ
    have hproj := lerayLp_toLp_ae_eq_projection (p := 4) (by norm_num) (by norm_num)
      hF4 (hF_l2 τ).1
    have hneg := Lp.coeFn_neg
      (UnforcedLeray.Leray.projection (UnforcedLeray.toL2 (F τ)))
    filter_upwards [hrep, hproj, hneg] with y hy1 hy2 hy3
    change -smoothLeraySlice F τ y = (G₂ τ : SpatialField) y
    rw [hy1, hy2]
    exact hy3.symm
  let MG2 : ℝ := ‖UnforcedLeray.Leray.projection‖ * (1 * max CU 0 ^ 2)
  have hG2_norm : ∀ τ : ℝ, ‖G₂ τ‖ ≤ MG2 := by
    intro τ
    dsimp [G₂, MG2]
    rw [norm_neg]
    refine (UnforcedLeray.Leray.projection.le_opNorm _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    change ‖UnforcedLeray.toL2 (F τ)‖ ≤ 1 * max CU 0 ^ 2
    rw [UnforcedLeray.norm_toL2 (hF_l2 τ).1]
    exact (hF_l2 τ).2
  have hG_l2 : ∀ τ : ℝ, eLpNorm (G_sm τ) 2 volume ≤ ENNReal.ofReal MG2 := by
    intro τ
    rw [eLpNorm_congr_ae (hG_ae_G2 τ), ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hG2_norm τ)
  obtain ⟨MG_inf, hMG_inf⟩ := hG_fam.iteratedFDeriv_bounded 0
  let MG : ℝ := max (max MG2 MG_inf) 1
  have hMG_pos : 0 ≤ MG := zero_le_one.trans (le_max_right _ _)
  have hG_q0 : ∀ τ : ℝ, MemLp (G_sm τ) q0E volume ∧
      eLpNorm (G_sm τ) q0E volume ≤ ENNReal.ofReal MG := fun τ =>
    memLp_q0E_of_l2_linfty (HigherPhaseSub.sliceFamily_contDiff_infty hG_fam τ).continuous
      (hG_l2 τ) fun y => by simpa [norm_iteratedFDeriv_zero] using hMG_inf τ y
  have hG_mem2 : ∀ τ : ℝ, MemLp (G_sm τ) 2 volume := fun τ =>
    ⟨(HigherPhaseSub.sliceFamily_contDiff_infty hG_fam τ).continuous.aestronglyMeasurable,
      lt_of_le_of_lt (hG_l2 τ) ENNReal.ofReal_lt_top⟩
  exact ⟨G_sm, MG, MG2, hMG_pos, hG_cont, hG_per, hG_q0, hG_mem2, hG2_norm, hG_ae_G2⟩

/-- Distributional PDE `HasPhaseOp (0 • · + L0T ν) w g_q` from slicewise a.e. equality on `ℝ³`,
Lagrange integration by parts in `y`, and period FTC in `τ`. -/
theorem hasPhaseOp_rem_of_pde {ν P C_a : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hP : 0 < P)
    {a : SpatialField} (hInv4 : UnforcedLeray.Heat.InvDistClass 4 C_a a)
    {U G_sm : ℝ → SpatialField}
    (hU_cd : ContDiff ℝ ∞ (fun z : ℝ × Space => U z.1 z.2))
    (hU_fam : IsUniformSmoothL4SliceFamily U)
    (hW_per : Function.Periodic (fun τ => U τ - UnforcedLeray.Blueprint.heatProfile ν a τ) P)
    {w g_q : Yq P q0E}
    (hw_rep : HasRep w (fun z : ℝ × Space =>
      realC (U z.1 z.2 - UnforcedLeray.Blueprint.heatProfile ν a z.1 z.2)))
    (hg_rep : HasRep g_q (fun z : ℝ × Space => realC (G_sm z.1 z.2)))
    (hPt : ∀ t : ℝ,
      (fun y => deriv (fun s => U s y - UnforcedLeray.Blueprint.heatProfile ν a s y) t -
          (1 / 2 : ℝ) • fderiv ℝ (fun y' => U t y' - UnforcedLeray.Blueprint.heatProfile ν a t y') y y -
          ν • UnforcedLeray.Heat.vlap
            (fun y' => U t y' - UnforcedLeray.Blueprint.heatProfile ν a t y') y -
          (1 / 2 : ℝ) • (U t y - UnforcedLeray.Blueprint.heatProfile ν a t y))
        =ᵐ[volume] G_sm t) :
    HasPhaseOp (fun Φ => (0 : ℂ) • Φ + L0T ν Φ) w g_q := by
  have hInv2 : UnforcedLeray.Heat.InvDistClass 2 C_a a := hInv4.of_le (by norm_num)
  let W : ℝ → SpatialField := fun τ => U τ - UnforcedLeray.Blueprint.heatProfile ν a τ
  let Wc : ℝ × Space → CVec3 := fun z => realC (W z.1 z.2)
  let Gc : ℝ × Space → CVec3 := fun z => realC (G_sm z.1 z.2)
  have hW_smooth : ∀ τ : ℝ, ContDiff ℝ ∞ (W τ) := fun τ =>
    (HigherPhaseSub.sliceFamily_contDiff_infty hU_fam τ).sub
      (UnforcedLeray.Heat.simHeat_contDiff hν hInv4.heatAdmissible τ)
  have hW_cont : Continuous fun z : ℝ × Space => W z.1 z.2 :=
    hU_cd.continuous.sub (continuous_heatProfile_joint hν hInv2)
  let W_dt : ℝ → SpatialField := fun t y =>
    fderiv ℝ (fun z : ℝ × Space => U z.1 z.2) (t, y) (1, 0) -
      (ν • UnforcedLeray.Heat.vlap (UnforcedLeray.Blueprint.heatProfile ν a t) y +
        (1 / 2 : ℝ) • fderiv ℝ (UnforcedLeray.Blueprint.heatProfile ν a t) y y +
        (1 / 2 : ℝ) • UnforcedLeray.Blueprint.heatProfile ν a t y)
  have hWdt_cont : Continuous fun z : ℝ × Space => W_dt z.1 z.2 :=
    ((hU_cd.continuous_fderiv (by simp)).clm_apply continuous_const).sub
      (continuous_heatProfile_dt_joint hν hInv2)
  have hW_deriv : ∀ (t : ℝ) (y : Space), HasDerivAt (fun s => W s y) (W_dt t y) t := by
    intro t y
    have hγ : HasDerivAt (fun s : ℝ => (s, y)) (1, 0) t :=
      (hasDerivAt_id' t).prodMk (hasDerivAt_const t y)
    have hAU := ((hU_cd.differentiable (by simp)) (t, y)).hasFDerivAt
    have hcomp := hAU.comp_hasDerivAt t hγ
    have hdU : HasDerivAt (fun s => U s y)
        (fderiv ℝ (fun z : ℝ × Space => U z.1 z.2) (t, y) (1, 0)) t := hcomp
    have hdH : HasDerivAt (fun s => UnforcedLeray.Blueprint.heatProfile ν a s y)
        (ν • UnforcedLeray.Heat.vlap (UnforcedLeray.Blueprint.heatProfile ν a t) y +
          (1 / 2 : ℝ) • fderiv ℝ (UnforcedLeray.Blueprint.heatProfile ν a t) y y +
          (1 / 2 : ℝ) • UnforcedLeray.Blueprint.heatProfile ν a t y) t :=
      UnforcedLeray.Heat.simHeat_equation hν hInv2 t y
    exact hdU.sub hdH
  intro Φ hΦ
  have hL0T_eq : (fun x => (0 : ℂ) • Φ x + L0T ν Φ x) = L0T ν Φ := by
    funext x; simp
  change phasePair P q0E (fun x => (0 : ℂ) • Φ x + L0T ν Φ x) w = phasePair P q0E Φ g_q
  rw [hL0T_eq, phasePair_eq_pairF_rep (isPhaseTest_L0T hΦ ν) w,
    pairF_rep_eq P w Wc hw_rep, phasePair_eq_pairF_rep hΦ g_q,
    pairF_rep_eq P g_q Gc hg_rep]
  unfold pairF phaseInt
  congr 1
  have hsl : ∀ t : ℝ,
      (∫ y : Space, dotL (L0T ν Φ (t, y)) (Wc (t, y))) =
        -(∫ y : Space, dotL (dτ Φ (t, y)) (Wc (t, y))) -
          ∫ y : Space, dotL (Φ (t, y)) (realC (spatialProjectedLin ν (W t) y)) :=
    fun t => slice_ibp_L0T ν hΦ (hW_smooth t) t
  simp_rw [hsl]
  obtain ⟨R₁, hR₁⟩ := hΦ.bounded_support
  obtain ⟨R₂, hR₂⟩ := hΦ.dτ.bounded_support
  let R : ℝ := max R₁ R₂
  let K : Set Space := Metric.closedBall (0 : Space) R
  have hbox : IsCompact (Icc (0 : ℝ) P ×ˢ K) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : Space) R)
  have hmeas_prod :
      ((volume : Measure ℝ).restrict (Ioc 0 P)).prod ((volume : Measure Space).restrict K) =
        (volume : Measure (ℝ × Space)).restrict (Ioc 0 P ×ˢ K) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hIdτ_t : IntegrableOn
      (fun t : ℝ => -(∫ y : Space, dotL (dτ Φ (t, y)) (Wc (t, y)))) (Ioc 0 P) volume := by
    have hf_cont : Continuous (fun z : ℝ × Space => dotL (dτ Φ z) (Wc z)) :=
      (dotL.continuous.comp hΦ.dτ.smooth.continuous).clm_apply (continuous_realC.comp hW_cont)
    have hf_int : Integrable (fun z : ℝ × Space => dotL (dτ Φ z) (Wc z))
        (((volume : Measure ℝ).restrict (Ioc 0 P)).prod
          ((volume : Measure Space).restrict K)) := by
      rw [hmeas_prod]
      exact (hf_cont.continuousOn.integrableOn_compact hbox).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)
    have heq_t : (fun t : ℝ => ∫ y : Space, dotL (dτ Φ (t, y)) (Wc (t, y))) =
        fun t => ∫ y in K, dotL (dτ Φ (t, y)) (Wc (t, y)) := funext fun t =>
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        have hgt : R < ‖y‖ := by
          simpa [K, Metric.mem_closedBall, dist_zero_right, not_le] using hy
        simp [hR₂ t y (lt_of_le_of_lt (le_max_right _ _) hgt)]).symm
    refine IntegrableOn.neg ?_
    rw [IntegrableOn, heq_t]
    exact hf_int.integral_prod_left
  have hIproj_t : IntegrableOn
      (fun t : ℝ => ∫ y : Space, dotL (Φ (t, y)) (realC (spatialProjectedLin ν (W t) y)))
      (Ioc 0 P) volume := by
    have hproj_cont : Continuous (fun z : ℝ × Space => spatialProjectedLin ν (W z.1) z.2) :=
      continuous_spatialProjectedLin_sub hν hInv4 hU_cd hU_fam
    have hf_cont : Continuous (fun z : ℝ × Space =>
        dotL (Φ z) (realC (spatialProjectedLin ν (W z.1) z.2))) :=
      (dotL.continuous.comp hΦ.smooth.continuous).clm_apply
        (continuous_realC.comp hproj_cont)
    have hf_int : Integrable
        (fun z : ℝ × Space => dotL (Φ z) (realC (spatialProjectedLin ν (W z.1) z.2)))
        (((volume : Measure ℝ).restrict (Ioc 0 P)).prod
          ((volume : Measure Space).restrict K)) := by
      rw [hmeas_prod]
      exact (hf_cont.continuousOn.integrableOn_compact hbox).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)
    have heq_t : (fun t : ℝ =>
        ∫ y : Space, dotL (Φ (t, y)) (realC (spatialProjectedLin ν (W t) y))) =
        fun t => ∫ y in K, dotL (Φ (t, y)) (realC (spatialProjectedLin ν (W t) y)) :=
      funext fun t => (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        have hgt : R < ‖y‖ := by
          simpa [K, Metric.mem_closedBall, dist_zero_right, not_le] using hy
        simp [hR₁ t y (lt_of_le_of_lt (le_max_left _ _) hgt)]).symm
    rw [IntegrableOn, heq_t]
    exact hf_int.integral_prod_left
  have hI_Wdt_t : IntegrableOn
      (fun t : ℝ => ∫ y : Space, dotL (Φ (t, y)) (realC (W_dt t y)))
      (Ioc 0 P) volume := by
    have hf_cont : Continuous (fun z : ℝ × Space => dotL (Φ z) (realC (W_dt z.1 z.2))) :=
      (dotL.continuous.comp hΦ.smooth.continuous).clm_apply
        (continuous_realC.comp hWdt_cont)
    have hf_int : Integrable (fun z : ℝ × Space => dotL (Φ z) (realC (W_dt z.1 z.2)))
        (((volume : Measure ℝ).restrict (Ioc 0 P)).prod
          ((volume : Measure Space).restrict K)) := by
      rw [hmeas_prod]
      exact (hf_cont.continuousOn.integrableOn_compact hbox).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)
    have heq_t : (fun t : ℝ => ∫ y : Space, dotL (Φ (t, y)) (realC (W_dt t y))) =
        fun t => ∫ y in K, dotL (Φ (t, y)) (realC (W_dt t y)) := funext fun t =>
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        have hgt : R < ‖y‖ := by
          simpa [K, Metric.mem_closedBall, dist_zero_right, not_le] using hy
        simp [hR₁ t y (lt_of_le_of_lt (le_max_left _ _) hgt)]).symm
    rw [IntegrableOn, heq_t]
    exact hf_int.integral_prod_left
  rw [integral_sub hIdτ_t hIproj_t, integral_neg,
    period_ibp_dτ hP hΦ hW_cont hWdt_cont hW_per hW_deriv, neg_neg,
    ← integral_sub hI_Wdt_t hIproj_t]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  have hI1 : Integrable (fun y : Space => dotL (Φ (t, y)) (realC (W_dt t y))) volume :=
    BaseRepIBP.integrable_slice_dotL_realC hΦ t
      (hWdt_cont.comp (Continuous.prodMk_right t))
  have hI2 : Integrable (fun y : Space =>
      dotL (Φ (t, y)) (realC (spatialProjectedLin ν (W t) y))) volume :=
    BaseRepIBP.integrable_slice_dotL_realC hΦ t
      (HigherPhaseSub.contDiff_infty_spatialProjectedLin ν (hW_smooth t)).continuous
  rw [← integral_sub hI1 hI2]
  refine integral_congr_ae ?_
  filter_upwards [hPt t] with y hy_pt
  have hreal_sub : realC (W_dt t y) - realC (spatialProjectedLin ν (W t) y) =
      realC (W_dt t y - spatialProjectedLin ν (W t) y) := by
    simp only [PointwiseDerivSub.realC_eq_ofReV, map_sub]
  rw [← map_sub, hreal_sub]
  have hlhs : W_dt t y - spatialProjectedLin ν (W t) y =
      deriv (fun s => U s y - UnforcedLeray.Blueprint.heatProfile ν a s y) t -
        (1 / 2 : ℝ) • fderiv ℝ (fun y' => U t y' - UnforcedLeray.Blueprint.heatProfile ν a t y') y y -
        ν • UnforcedLeray.Heat.vlap
          (fun y' => U t y' - UnforcedLeray.Blueprint.heatProfile ν a t y') y -
        (1 / 2 : ℝ) • (U t y - UnforcedLeray.Blueprint.heatProfile ν a t y) :=
    (congrArg₂ HSub.hSub (hW_deriv t y).deriv.symm
      (spatialProjectedLin_eq_vlap ν (hW_smooth t) y)).trans (vec3_sub_add_add _ _ _ _)
  exact congrArg (fun v => dotL (Φ (t, y)) (realC v)) (hlhs.trans hy_pt)

/-- Resolvent representation and homogeneous uniqueness in `Yq P q0E` at `μ = 0`. -/
theorem resolvent_unique_at_zero {ν P : ℝ} [Fact (0 < P)] (hν : 0 < ν)
    (w g_q : Yq P q0E)
    (hw_op : HasPhaseOp (fun Φ => (0 : ℂ) • Φ + L0T ν Φ) w g_q) :
    ∃ Rm : Yq P q0E →L[ℂ] Yq P q0E,
      (∀ f : Yq P q0E,
        Rm f = ∫ r in Ioi (0 : ℝ), Complex.exp (-((0 : ℂ) * r)) • phaseT q0E_ne_top ν r f) ∧
      w = Rm g_q := by
  obtain ⟨Rm, _hRm_norm, hRm⟩ :=
    UnforcedLeray.Short.PartIIa.bodyResolvent_exists q0E q0E_gt_one q0E_lt_three P ν hν 0
      gammaR_q0E_pos
  have hRm_op : HasPhaseOp (fun Φ => (0 : ℂ) • Φ + L0T ν Φ) (Rm g_q) g_q :=
    UnforcedLeray.Short.PartIIa.bodyResolvent_solves q0E q0E_gt_one q0E_lt_three P ν hν 0
      gammaR_q0E_pos Rm hRm g_q
  have hdiff : HasPhaseOp (fun Φ => (0 : ℂ) • Φ + L0T ν Φ) (w - Rm g_q) 0 := fun Φ hΦ => by
    rw [map_sub, map_zero, hw_op Φ hΦ, hRm_op Φ hΦ, sub_self]
  refine ⟨Rm, hRm, sub_eq_zero.1 ?_⟩
  exact UnforcedLeray.Short.PartIIa.bodyOp_uniqueness q0E q0E_gt_one q0E_lt_three P ν hν 0
    gammaR_q0E_pos (w - Rm g_q) hdiff

theorem freeDuhamelUniquenessAe_main : UnforcedLeray.Short.IIb.FreeDuhamelUniquenessAe := by
  intro ν P hν hP _hP1 a ha U hU_cd hU_fam hU_per _hU_sol ⟨M_q, hMq⟩ hPDE
  have : Fact (0 < P) := ⟨hP⟩
  obtain ⟨C_a, hInv4⟩ := B3RemH2Sub.exists_invDistClass4_of_isB3Datum ha
  have hInv2 : UnforcedLeray.Heat.InvDistClass 2 C_a a := hInv4.of_le (by norm_num)
  -- Step 1a: Remainder `W = U - H_a` and lift `w : Yq P q0E`
  have hW_cont : Continuous fun z : ℝ × Space =>
      (U z.1 - UnforcedLeray.Blueprint.heatProfile ν a z.1) z.2 :=
    hU_cd.continuous.sub (continuous_heatProfile_joint hν hInv2)
  have hW_per : Function.Periodic (fun τ => U τ - UnforcedLeray.Blueprint.heatProfile ν a τ) P := by
    intro τ
    funext y
    change U (τ + P) y - UnforcedLeray.Blueprint.heatProfile ν a (τ + P) y =
      U τ y - UnforcedLeray.Blueprint.heatProfile ν a τ y
    rw [congrFun (hU_per τ) y, UnforcedLeray.Blueprint.L01.heatProfile_add_period hν ha.dss τ y]
  have hW_bd : ∀ τ : ℝ,
      eLpNorm (U τ - UnforcedLeray.Blueprint.heatProfile ν a τ) q0E volume ≤
        ENNReal.ofReal (max M_q 0) := fun τ =>
    (hMq τ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  obtain ⟨w, hw_rep, _⟩ := yqOfFields P
    (fun z : ℝ × Space => realC (U z.1 z.2 - UnforcedLeray.Blueprint.heatProfile ν a z.1 z.2))
    (isInYr_realC_of_slice hP (le_max_right M_q 0) hW_cont hW_per hW_bd)
  -- Step 1b: Smooth convective Leray source `G_sm` and lift `g_q : Yq P q0E`
  obtain ⟨G_sm, MG, MG2, hMG_pos, hG_cont, hG_per, hG_q0, hG_mem2, hG2_norm, hG_ae_G2⟩ :=
    convectiveSource_props hU_cd hU_fam hU_per
  obtain ⟨g_q, hg_rep, _⟩ := yqOfFields P
    (fun z : ℝ × Space => realC (G_sm z.1 z.2))
    (isInYr_realC_of_slice hP hMG_pos hG_cont hG_per (fun τ => (hG_q0 τ).2))
  -- Step 2: Weak PDE `HasPhaseOp (fun Φ => (0 : ℂ) • Φ + L0T ν Φ) w g_q`
  have hw_op : HasPhaseOp (fun Φ => (0 : ℂ) • Φ + L0T ν Φ) w g_q :=
    hasPhaseOp_rem_of_pde (a := a) (U := U) (G_sm := G_sm) (w := w) (g_q := g_q)
      hν hP hInv4 hU_cd hU_fam hW_per hw_rep hg_rep
      (fun t => (hPDE t).trans (hG_ae_G2 t).symm)
  -- Step 3: Resolvent existence, equation, and homogeneous uniqueness at `μ = 0`
  obtain ⟨Rm, hRm, hw_eq_Rm⟩ := resolvent_unique_at_zero hν w g_q hw_op
  -- Step 4: Conclude via `duhamel_ae_of_resolvent`
  exact duhamel_ae_of_resolvent hν hP
    (fun τ => U τ - UnforcedLeray.Blueprint.heatProfile ν a τ) w hw_rep
    G_sm hG_cont hG_per hMG_pos hG_q0 hG_mem2
    (fun τ => -(UnforcedLeray.Leray.projection (UnforcedLeray.toL2
      (fun y => fderiv ℝ (U τ) y (U τ y)))))
    hG2_norm hG_ae_G2 g_q hg_rep Rm hRm hw_eq_Rm

end UnforcedLeray.Short.IIb.FreeUniqAux

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:B3/2/1/3` (`FreeDuhamelUniquenessAe`)**: free uniqueness in `Y_{11/4}` identifies
`U(τ) - H_a(τ)` for almost every phase `τ : ℝ` with the `L²` similarity Duhamel integral of
`-𝐏(U · ∇U)` (SP 2613-2629). -/
theorem freeDuhamelUniquenessAe_proof : UnforcedLeray.Short.IIb.FreeDuhamelUniquenessAe :=
  FreeUniqAux.freeDuhamelUniquenessAe_main

end UnforcedLeray.Short.IIb

end
