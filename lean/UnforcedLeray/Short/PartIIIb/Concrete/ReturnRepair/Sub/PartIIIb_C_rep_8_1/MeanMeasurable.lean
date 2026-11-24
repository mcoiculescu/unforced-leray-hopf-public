import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_org
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.VelYH

/-!
# `PartIII-b:C/rep/8/1/4` (`meanMeasurable`): measurability of the mean residual

Source `the November 2 reference manuscript` lines 5380-5387 and 5484-5506.
`meanE T` is the chart coefficient of `wardEXY(U, p, X^mt, Y^mt)`.  The fields `X^mt, Y^mt` are
phase-free functions of `y` alone, so their spatial derivatives are measurable by
`measurable_fderiv` (unconditional).  The background `U` and the pressure `p` of an actual level are
smooth on `ℝ × Space` (`IsExactProfile`, carried by `SeqData.IsActualLevel.profile`), so their
parametric spatial derivatives are measurable by `measurable_fderiv_apply_const_with_param`.
Every term of the Ward residual is then a measurable function of `(τ, y)`, and `coefOf` of a jointly
measurable field is measurable (`vyh_measurable_coefOf`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace MMAux

theorem fderiv_slice_eq' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] {Φ : ℝ × Space → F} (hΦ : Differentiable ℝ Φ) (p : ℝ × Space)
    (w : Space) : fderiv ℝ (fun z => Φ (p.1, z)) p.2 w = fderiv ℝ Φ p (0, w) := by
  have h1 : HasFDerivAt (fun z : Space => (p.1, z))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have h2 : HasFDerivAt (fun z => Φ (p.1, z))
      ((fderiv ℝ Φ (p.1, p.2)).comp
        ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) p.2 :=
    (hΦ (p.1, p.2)).hasFDerivAt.comp p.2 h1
  rw [h2.fderiv]
  simp

theorem continuous_slice_fderiv' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] {Φ : ℝ × Space → F} (hΦ : ContDiff ℝ 1 Φ) (w : Space) :
    Continuous (fun p : ℝ × Space => fderiv ℝ (fun z => Φ (p.1, z)) p.2 w) := by
  have heq : (fun p : ℝ × Space => fderiv ℝ (fun z => Φ (p.1, z)) p.2 w) =
      fun p => fderiv ℝ Φ p (0, w) :=
    funext fun p => fderiv_slice_eq' (hΦ.differentiable (by norm_num)) p w
  rw [heq]
  exact (hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem measurable_slice1 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] {Φ : ℝ × Space → F} (hΦ : Continuous Φ) (w : Space) :
    Measurable (fun p : ℝ × Space => fderiv ℝ (fun z => Φ (p.1, z)) p.2 w) :=
  measurable_fderiv_apply_const_with_param ℝ (f := fun t z => Φ (t, z)) hΦ w

theorem measurable_slice2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] {Φ : ℝ × Space → F} (hΦ : ContDiff ℝ 1 Φ) (b a : Space) :
    Measurable (fun p : ℝ × Space =>
      fderiv ℝ (fun y => fderiv ℝ (fun z => Φ (p.1, z)) y b) p.2 a) :=
  measurable_fderiv_apply_const_with_param ℝ
    (f := fun t y => fderiv ℝ (fun z => Φ (t, z)) y b) (continuous_slice_fderiv' hΦ b) a

theorem measurable_hcoord (l : Fin 3) : Measurable (fun v : Space => v l) :=
  (EuclideanSpace.proj l).continuous.measurable

/-- **Measurability of the Ward residual** `wardEXY(U, p, X, Y)` with phase-free `X = GX`,
`Y = GY` (the mean fields), on `ℝ × Space`. -/
theorem measurable_wardEXY {ν μ R : ℝ} (U : ℝ → SpatialField) (P : ℝ → Space → ℝ)
    (GX GY : Space → Space)
    (hU : ContDiff ℝ 1 (fun x : ℝ × Space => U x.1 x.2))
    (hP : Continuous (fun x : ℝ × Space => P x.1 x.2)) :
    Measurable (fun x : ℝ × Space => wardEXY ν μ R U P (fun _ => GX) (fun _ => GY) x.1 x.2) := by
  have hUc : Continuous (fun x : ℝ × Space => U x.1 x.2) := hU.continuous
  have hUm : Measurable (fun x : ℝ × Space => U x.1 x.2) := hUc.measurable
  have hUm' : ∀ l : Fin 3, Measurable (fun x : ℝ × Space => U x.1 x.2 l) :=
    fun l => (measurable_hcoord l).comp hUm
  -- the mean fields: first derivatives and second derivatives
  have hGX1 : ∀ j : Fin 3, Measurable (fun y : Space => fderiv ℝ GX y (coordinateVector j)) :=
    fun j => measurable_fderiv_apply_const ℝ GX (coordinateVector j)
  have hGX2 : ∀ j l : Fin 3, Measurable (fun y : Space =>
      fderiv ℝ (fun y' => fderiv ℝ GX y' (coordinateVector l)) y (coordinateVector j)) :=
    fun j l => measurable_fderiv_apply_const ℝ
      (fun y' => fderiv ℝ GX y' (coordinateVector l)) (coordinateVector j)
  have hGY1 : Measurable (fun x : ℝ × Space => fderiv ℝ GY x.2) :=
    (measurable_fderiv ℝ GY).comp measurable_snd
  -- the Ward terms
  have hev : Continuous (fun q : (Space →L[ℝ] Space) × Space => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  have hM1 : Measurable (fun x : ℝ × Space => fderiv ℝ GY x.2 (U x.1 x.2)) :=
    hev.measurable.comp (hGY1.prodMk hUm)
  -- `physCdiff(U, GX)`
  have hM2 : Measurable (fun x : ℝ × Space => physCdiff (U x.1) GX x.2) := by
    unfold physCdiff
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    refine Finset.measurable_sum Finset.univ (fun l _ => ?_)
    refine Measurable.sub ?_ ?_
    · have ha : Measurable (fun x : ℝ × Space => physPd (U x.1) j x.2 l) :=
        (measurable_hcoord l).comp (measurable_slice1 hUc (coordinateVector j))
      have hb : Measurable (fun x : ℝ × Space => physPd2 GX j l x.2) :=
        (hGX2 j l).comp measurable_snd
      exact ha.smul hb
    · have ha : Measurable (fun x : ℝ × Space => physPd GX j x.2 l) :=
        (measurable_hcoord l).comp ((measurable_fderiv_apply_const ℝ GX (coordinateVector j)).comp
          measurable_snd)
      have hb : Measurable (fun x : ℝ × Space => physPd2 (U x.1) j l x.2) :=
        measurable_slice2 hU (coordinateVector l) (coordinateVector j)
      exact ha.smul hb
  -- `physUUD2(U, GX)`
  have hM3 : Measurable (fun x : ℝ × Space => physUUD2 (U x.1) GX x.2) := by
    unfold physUUD2
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    refine Finset.measurable_sum Finset.univ (fun l _ => ?_)
    have ha : Measurable (fun x : ℝ × Space => U x.1 x.2 j * U x.1 x.2 l) :=
      (hUm' j).mul (hUm' l)
    have hb : Measurable (fun x : ℝ × Space => physPd2 GX j l x.2) :=
      (hGX2 j l).comp measurable_snd
    exact ha.smul hb
  -- `physDXp(GX, P)`
  have hM4 : Measurable (fun x : ℝ × Space => physDXp GX (P x.1) x.2) := by
    unfold physDXp
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp ?_
    refine measurable_pi_lambda _ (fun i => ?_)
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    have hd : Measurable (fun x : ℝ × Space => fderiv ℝ (P x.1) x.2 (coordinateVector j)) :=
      measurable_slice1 (Φ := fun x : ℝ × Space => P x.1 x.2) hP (coordinateVector j)
    have hpi : Measurable (fun x : ℝ × Space => physPd GX j x.2 i) :=
      (measurable_hcoord i).comp ((hGX1 j).comp measurable_snd)
    have hpj : Measurable (fun x : ℝ × Space => physPd GX i x.2 j) :=
      (measurable_hcoord j).comp ((hGX1 i).comp measurable_snd)
    exact (hpi.add hpj).mul hd
  have hF := ((hM1.const_smul (2 : ℝ)).sub (hM2.const_smul (2 * ν))).add hM3 |>.sub hM4
  unfold wardEXY
  exact hF

/-- **The mean Ward residual is measurable** (the coefficient of `wardEXY` at the chart points). -/
theorem meanE_aesm (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (T : LStr Pl K L)
    (hU : ContDiff ℝ 1 (fun x : ℝ × Space => L.U x.1 x.2))
    (hP : Continuous (fun x : ℝ × Space => L.pres x.1 x.2)) :
    AEStronglyMeasurable (meanE Pl K L μ T) (srcMeasure (cOf L.ν)) := by
  unfold meanE
  have hF := measurable_wardEXY (ν := L.ν) (μ := μ) (R := L.ε⁻¹) L.U L.pres
    (fun y => Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y)
    (fun y => Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y) hU hP
  exact (vyh_measurable_coefOf L.ε⁻¹ hF).aestronglyMeasurable

end MMAux

open MMAux

/-- **`PartIII-b:C/rep/8/1/4`** (`meanMeasurable`): the mean residual is measurable along the
sequence (on the actual levels, whose background is an exact profile). -/
theorem meanMeasurable (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.MeanMeasurable := by
  unfold SeqData.MeanMeasurable
  filter_upwards [hst.actual] with n hn z _
  unfold MeanMeasurableAt
  intro T
  have hprof := hn.profile
  have hU : ContDiff ℝ 1 (fun x : ℝ × Space => (D.level n).U x.1 x.2) :=
    hprof.smoothU.of_le (by exact_mod_cast le_top)
  have hP : Continuous (fun x : ℝ × Space => (D.level n).pres x.1 x.2) :=
    hprof.smoothP.continuous
  exact meanE_aesm D.Pl D.K (D.level n) (D.mu n z) T hU hP

end UnforcedLeray.Short.PartIIIb.Concrete
