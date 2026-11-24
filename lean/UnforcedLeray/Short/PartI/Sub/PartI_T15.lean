import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Sub.PartI_T14
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanEnergy
import UnforcedLeray.Lib.Kernels.ParamIntegral
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# `PartI:T15` (`Sub/PartI_T15.lean`): decomposition of `OverlapMeanDecay`

Source of record: `the November 2 reference manuscript`, lines 304-313, 415-425
(old lines 425-436).

With `𝖲(T, Y) = c² S(s_c + c² T / ν, c Y)` (`overlapMeanStream tr T Y`),
`b(T, Y) = hmean 1 (overlapField ν c tr.v T) Y 0 = -∂_Y 𝖲(T, Y)`, and
`g(T, Y) = \overline{W₁ W₂}(T, Y)` (`overlapStressProfile tr T Y`, where
`W(T) = hfluct 1 (overlapField ν c tr.v T)`), the primitive `𝖲` solves
`∂_T 𝖲 - ∂_Y² 𝖲 = e_c g` with `‖𝖲(0)‖_{L¹_Y} ≤ C` (from `OverlapMeanPrimitive`).

This module proves unconditionally:
1. Smoothness (`contDiff_hmean_unit`, `contDiff_hfluct_unit`) and parametric differentiation
   (`norm_iteratedDeriv_hmean_unit_le`) for unit horizontal averages on `Plane`.
2. Control of `∂_Y^j b` by `jet j U` in `L^∞_Y` and `L²_Y`, and the entire short-time regime
   `0 ≤ T ≤ 1` (`overlapMeanDecay_shortTime`) from `OverlapHighNormUniform`.
3. Exponential `L¹_Y` decay of `g(t) = overlapStressProfile tr t` (`eLpNorm_overlapStressProfile_one_le`)
   and all-order `L²_Y` / `L^∞_Y` exponential decay of `∂_Y^k g(t)`
   (`eLpNorm_iteratedDeriv_overlapStressProfile_le`) from `OverlapFluctuationDecay` via the
   Leibniz rule (`norm_iteratedFDeriv_mul_le`) and unit-cell Cauchy-Schwarz.
4. Exponential time-integral bounds on `(0, T/2]` and `(T/2, T]` (`lintegral_Ioc_exp_neg_le`),
   polynomial absorption `e^{-a T / 2} ≤ C_abs (1 + T)^{-1 - j/2}` for `T ≥ 1`, and conditional
   assembly `overlap_mean_decay_of` from the single remaining 1D heat Duhamel split leaf
   `OverlapMeanDuhamelSplit` (`PartI:T15/1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 Vc width)

/-! ### 1. Overlap Reynolds stress profile and 1D heat Duhamel split leaf (`PartI:T15/1`) -/

/-- The overlap horizontal Reynolds stress profile
`\overline{W₁ W₂}(T, Y) = hmean 1 (fun y => W(T, y)₀ * W(T, y)₁) Y`
where `W(T) = hfluct 1 (overlapField ν c tr.v T)` (source line 418). -/
def overlapStressProfile {ν c : ℝ} (tr : B0140.TrainSol ν c) (T Y : ℝ) : ℝ :=
  let W := hfluct 1 (overlapField ν c tr.v T)
  hmean 1 (fun y : Plane => W y 0 * W y 1) Y

/-- **1D heat Duhamel split at `T / 2` for the overlap mean drift `b = -∂_Y 𝖲` (`PartI:T15/1`)**
(source lines 415-425):
for every derivative order `j : ℕ`, there exists `C_G > 0` (from the 1D Gaussian kernel derivative
bounds `‖∂_Y^{j+1} G_t‖_p ≤ C t^{-1 - j/2 + 1/(2p)}` for `p = 2, ∞`) such that for all `ν > 0`,
`c > 1`, every `BUC` train `tr : B0140.TrainSol ν c`, and every `T ≥ 1`, splitting the 1D heat
Duhamel representation of `∂_Y^j b(T) = -∂_Y^{j+1} 𝖲(T)` (where `∂_T 𝖲 - ∂_Y² 𝖲 = e_c g`,
`𝖲 = overlapMeanStream tr`, `g = overlapStressProfile tr`) at `T / 2` bounds `‖∂_Y^j b(T)‖_p`
(`p = 2, ⊤`) by `C_G (1 + T)^{-1 - j/2 + 1/(2p)} (‖𝖲(0)‖₁ + e_c ∫_0^{T/2} ‖g(t)‖₁ dt)` plus the
late-half source derivative integral `e_c ∫_{T/2}^T ‖∂_Y^{j+1} g(t)‖_p dt`. -/
def OverlapMeanDuhamelSplit : Prop :=
  ∀ j : ℕ, ∃ C_G : ℝ, 0 < C_G ∧
    ∀ (ν c : ℝ), 0 < ν → 1 < c →
      ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
        ∀ T : ℝ, 1 ≤ T →
          let U := overlapField ν c tr.v T
          let b : ℝ → ℝ := fun Y => hmean 1 U Y 0
          let S₀ : ℝ → ℝ := overlapMeanStream tr 0
          let g : ℝ → ℝ → ℝ := overlapStressProfile tr
          let early : ℝ≥0∞ :=
            eLpNorm S₀ 1 volume +
              ENNReal.ofReal (eC ν c) * ∫⁻ t in Ioc 0 (T / 2), eLpNorm (g t) 1 volume
          eLpNorm (iteratedDeriv j b) 2 volume ≤
            ENNReal.ofReal (C_G * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) * early +
              ENNReal.ofReal (eC ν c) *
                ∫⁻ t in Ioc (T / 2) T, eLpNorm (iteratedDeriv (j + 1) (g t)) 2 volume ∧
          eLpNorm (iteratedDeriv j b) ⊤ volume ≤
            ENNReal.ofReal (C_G * (1 + T) ^ (-1 - (j : ℝ) / 2)) * early +
              ENNReal.ofReal (eC ν c) *
                ∫⁻ t in Ioc (T / 2) T, eLpNorm (iteratedDeriv (j + 1) (g t)) ⊤ volume

namespace PartI_T15

/-! ### 2. Smoothness of `overlapField`, `hmean 1`, and `hfluct 1` -/

private theorem hmean_apply_vec {c : ℝ} {a : Plane → Vec} (ha : Continuous a) (η : ℝ) (j : Fin 2) :
    (hmean c a η) j = hmean c (fun z => a z j) η := by
  have hint : Integrable (fun q : ℝ => a (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (ha.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h := (EuclideanSpace.proj j : Vec →L[ℝ] ℝ).integral_comp_comm hint
  unfold hmean
  rw [PiLp.smul_apply]
  congr 1
  simpa using h.symm

theorem contDiff_overlapField_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {T : ℝ}
    (hs : 0 ≤ B0146.overlapAge ν c + c ^ 2 * T / ν) :
    ContDiff ℝ ∞ (overlapField ν c tr.v T) := by
  set s := B0146.overlapAge ν c + c ^ 2 * T / ν
  have hcd : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v
  have hmap : ContDiff ℝ ∞ (fun y : Plane => ((s, c • y) : ℝ × Plane)) :=
    contDiff_const.prodMk (contDiff_id.const_smul c)
  have hv : ContDiffOn ℝ ∞ (fun y : Plane => tr.v s (c • y)) univ :=
    hcd.comp hmap.contDiffOn (fun y _ => ⟨hs, mem_univ _⟩)
  exact (contDiffOn_univ.1 hv).const_smul (c ^ 3)

private theorem slice_iteratedFDeriv_snd {Φ : Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (q : ℝ) (n : ℕ) (Y : ℝ) :
    iteratedFDeriv ℝ n (fun Y' : ℝ => Φ (q, Y')) Y =
      (iteratedFDeriv ℝ n Φ (q, Y)).compContinuousLinearMap
        (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ ℝ) := by
  have hτ : ContDiff ℝ ∞ (fun z : Plane => z + (q, (0 : ℝ))) :=
    contDiff_id.add contDiff_const
  have hsmooth : ContDiff ℝ ∞ (fun z : Plane => Φ (z + (q, (0 : ℝ)))) :=
    hΦ.comp hτ
  have hfun : (fun Y' : ℝ => Φ (q, Y')) =
      (fun z : Plane => Φ (z + (q, (0 : ℝ)))) ∘ (ContinuousLinearMap.inr ℝ ℝ ℝ) := by
    funext Y'
    simp
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (i := n)
    (ContinuousLinearMap.inr ℝ ℝ ℝ) hsmooth Y (mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  have hY : ContinuousLinearMap.inr ℝ ℝ ℝ Y + (q, (0 : ℝ)) = (q, Y) := by simp
  rw [hY]

private theorem norm_inr_le_one : ‖(ContinuousLinearMap.inr ℝ ℝ ℝ : ℝ →L[ℝ] Plane)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by simp

private theorem norm_slice_iteratedFDeriv_snd_le {Φ : Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (q : ℝ) (n : ℕ) (Y : ℝ) :
    ‖iteratedFDeriv ℝ n (fun Y' : ℝ => Φ (q, Y')) Y‖ ≤ ‖iteratedFDeriv ℝ n Φ (q, Y)‖ := by
  rw [slice_iteratedFDeriv_snd hΦ q n Y]
  have hprod : ∏ _i : Fin n, ‖(ContinuousLinearMap.inr ℝ ℝ ℝ : ℝ →L[ℝ] Plane)‖ ≤ 1 := by
    calc ∏ _i : Fin n, ‖(ContinuousLinearMap.inr ℝ ℝ ℝ : ℝ →L[ℝ] Plane)‖
        ≤ ∏ _i : Fin n, (1 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_inr_le_one)
      _ = 1 := Finset.prod_const_one
  calc ‖(iteratedFDeriv ℝ n Φ (q, Y)).compContinuousLinearMap
          (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ ℝ)‖
      ≤ ‖iteratedFDeriv ℝ n Φ (q, Y)‖ *
          ∏ _i : Fin n, ‖(ContinuousLinearMap.inr ℝ ℝ ℝ : ℝ →L[ℝ] Plane)‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n Φ (q, Y)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ n Φ (q, Y)‖ := mul_one _

private theorem slice_iteratedFDeriv_snd_continuous {Φ : Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (n : ℕ) (Y : ℝ) :
    Continuous (fun q : ℝ => iteratedFDeriv ℝ n (fun Y' : ℝ => Φ (q, Y')) Y) := by
  have hcont : Continuous (fun q : ℝ => iteratedFDeriv ℝ n Φ (q, Y)) :=
    (hΦ.continuous_iteratedFDeriv (m := n) (mod_cast le_top)).comp
      (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Plane) ℝ =>
      A.compContinuousLinearMap (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ ℝ)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ ℝ)).continuous
  refine (hT.comp hcont).congr fun q => ?_
  exact (slice_iteratedFDeriv_snd hΦ q n Y).symm

private theorem hmean_unit_locDominated {Φ : Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    UnforcedLeray.Kernels.LocDominated (volume.restrict (Ioc (-1 / 2 : ℝ) (1 / 2)))
      (fun (q : ℝ) (Y : ℝ) => Φ (q, Y)) univ := by
  intro n Y₀ _
  have hK : IsCompact (Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Metric.closedBall Y₀ 1) :=
    isCompact_Icc.prod (isCompact_closedBall Y₀ 1)
  have hcont : ContinuousOn (iteratedFDeriv ℝ n Φ)
      (Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Metric.closedBall Y₀ 1) :=
    (hΦ.continuous_iteratedFDeriv (m := n) (mod_cast le_top)).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨Metric.closedBall Y₀ 1, Metric.closedBall_mem_nhds Y₀ one_pos,
    fun _ => C, integrable_const C, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (-1 / 2 : ℝ) (1 / 2)))]
    with q hq Y hY
  exact (norm_slice_iteratedFDeriv_snd_le hΦ q n Y).trans
    (hC (q, Y) ⟨Ioc_subset_Icc_self hq, hY⟩)

theorem contDiff_hmean_unit {Φ : Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (hmean 1 Φ) := by
  have hfun : hmean 1 Φ = fun Y' : ℝ => ∫ q in Ioc (-1 / 2 : ℝ) (1 / 2), Φ (q, Y') := by
    funext Y'
    simp [hmean]
  rw [hfun]
  have hsmooth : ∀ q : ℝ, ContDiff ℝ ∞ (fun Y' : ℝ => Φ (q, Y')) := fun q =>
    hΦ.comp (contDiff_const.prodMk contDiff_id)
  have hmeas : ∀ (n : ℕ) (Y' : ℝ),
      AEStronglyMeasurable (fun q : ℝ => iteratedFDeriv ℝ n (fun Y'' : ℝ => Φ (q, Y'')) Y')
        (volume.restrict (Ioc (-1 / 2 : ℝ) (1 / 2))) :=
    fun n Y' => (slice_iteratedFDeriv_snd_continuous hΦ n Y').aestronglyMeasurable
  exact contDiffOn_univ.1 (UnforcedLeray.Kernels.contDiffOn_integral
    (μ := volume.restrict (Ioc (-1 / 2 : ℝ) (1 / 2)))
    (F := fun (q : ℝ) (Y' : ℝ) => Φ (q, Y'))
    (U := univ) isOpen_univ (ae_of_all _ hsmooth) hmeas (hmean_unit_locDominated hΦ))

theorem contDiff_hmean_unit_fst {U : Plane → Vec} (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (fun Y : ℝ => hmean 1 U Y 0) := by
  have hU0 : ContDiff ℝ ∞ (fun z : Plane => U z 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hU
  have heq : (fun Y : ℝ => hmean 1 U Y 0) = hmean 1 (fun z : Plane => U z 0) := by
    funext Y
    exact hmean_apply_vec hU.continuous Y 0
  rw [heq]
  exact contDiff_hmean_unit hU0

theorem contDiff_hmean_unit_vec {U : Plane → Vec} (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (hmean 1 U) := by
  let e : Vec ≃L[ℝ] (Fin 2 → ℝ) := EuclideanSpace.equiv (Fin 2) ℝ
  have hcoord : ∀ i : Fin 2, ContDiff ℝ ∞ (fun Y : ℝ => (hmean 1 U Y) i) := by
    intro i
    have hUi : ContDiff ℝ ∞ (fun z : Plane => U z i) :=
      (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hU
    have heq : (fun Y : ℝ => (hmean 1 U Y) i) = hmean 1 (fun z : Plane => U z i) := by
      funext Y
      exact hmean_apply_vec hU.continuous Y i
    rw [heq]
    exact contDiff_hmean_unit hUi
  have hpi : ContDiff ℝ ∞ (fun Y : ℝ => e (hmean 1 U Y)) :=
    contDiff_pi.2 hcoord
  have hcomp := e.symm.contDiff.comp hpi
  change ContDiff ℝ ∞ (fun Y : ℝ => e.symm (e (hmean 1 U Y))) at hcomp
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hcomp

theorem contDiff_hfluct_unit {U : Plane → Vec} (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (hfluct 1 U) :=
  hU.sub ((contDiff_hmean_unit_vec hU).comp contDiff_snd)

theorem norm_iteratedDeriv_hmean_unit_le {Φ : Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (j : ℕ) (Y : ℝ) :
    ‖iteratedDeriv j (hmean 1 Φ) Y‖ ≤
      ∫ q in Ioc (-1 / 2 : ℝ) (1 / 2), ‖iteratedFDeriv ℝ j Φ (q, Y)‖ := by
  have hfun : hmean 1 Φ = fun Y' : ℝ => ∫ q in Ioc (-1 / 2 : ℝ) (1 / 2), Φ (q, Y') := by
    funext Y'
    simp [hmean]
  have hsmooth : ∀ q : ℝ, ContDiff ℝ ∞ (fun Y' : ℝ => Φ (q, Y')) := fun q =>
    hΦ.comp (contDiff_const.prodMk contDiff_id)
  have hmeas : ∀ (n : ℕ) (Y' : ℝ),
      AEStronglyMeasurable (fun q : ℝ => iteratedFDeriv ℝ n (fun Y'' : ℝ => Φ (q, Y'')) Y')
        (volume.restrict (Ioc (-1 / 2 : ℝ) (1 / 2))) :=
    fun n Y' => (slice_iteratedFDeriv_snd_continuous hΦ n Y').aestronglyMeasurable
  have h1 := UnforcedLeray.Kernels.norm_iteratedFDeriv_integral_le
    (μ := volume.restrict (Ioc (-1 / 2 : ℝ) (1 / 2)))
    (F := fun (q : ℝ) (Y' : ℝ) => Φ (q, Y'))
    (U := univ) isOpen_univ (ae_of_all _ hsmooth) hmeas (hmean_unit_locDominated hΦ)
    j (mem_univ Y)
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ), hfun]
  refine h1.trans (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) ?_ ?_)
  · have hcont : Continuous (fun q : ℝ => ‖iteratedFDeriv ℝ j Φ (q, Y)‖) :=
      ((hΦ.continuous_iteratedFDeriv (m := j) (mod_cast le_top)).comp
        (continuous_id.prodMk continuous_const)).norm
    exact hcont.integrableOn_Ioc
  · exact ae_of_all _ fun q => norm_slice_iteratedFDeriv_snd_le hΦ q j Y

/-! ### 3. Control of `∂_Y^j b` by `jet j U` and short-time regime `0 ≤ T ≤ 1` -/

private theorem norm_proj_le_one (i : Fin 2) :
    ‖(EuclideanSpace.proj i : Vec →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using PiLp.norm_apply_le v i

private theorem norm_iteratedFDeriv_coord_le {U : Plane → Vec} (hU : ContDiff ℝ ∞ U)
    (i : Fin 2) (j : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ j (fun w : Plane => U w i) z‖ ≤ ‖jet j U z‖ := by
  have h := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
    (f := U) (x := z) (N := (∞ : WithTop ℕ∞)) (n := j) hU.contDiffAt (mod_cast le_top)
  calc ‖iteratedFDeriv ℝ j (fun w : Plane => U w i) z‖
      ≤ ‖(EuclideanSpace.proj i : Vec →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ j U z‖ := h
    _ ≤ 1 * ‖iteratedFDeriv ℝ j U z‖ :=
        mul_le_mul_of_nonneg_right (norm_proj_le_one i) (norm_nonneg _)
    _ = ‖jet j U z‖ := by rw [one_mul]; rfl

theorem norm_iteratedDeriv_b_le_hmean_jet {U : Plane → Vec} (hU : ContDiff ℝ ∞ U)
    (j : ℕ) (Y : ℝ) :
    ‖iteratedDeriv j (fun Y' => hmean 1 U Y' 0) Y‖ ≤
      hmean 1 (fun z : Plane => ‖jet j U z‖) Y := by
  have hU0 : ContDiff ℝ ∞ (fun z : Plane => U z 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hU
  have hb_eq : (fun Y' : ℝ => hmean 1 U Y' 0) = hmean 1 (fun z : Plane => U z 0) := by
    funext Y'
    exact hmean_apply_vec hU.continuous Y' 0
  rw [hb_eq]
  have h1 := norm_iteratedDeriv_hmean_unit_le hU0 j Y
  have h2 : ∫ q in Ioc (-1 / 2 : ℝ) (1 / 2), ‖iteratedFDeriv ℝ j (fun z : Plane => U z 0) (q, Y)‖ ≤
      ∫ q in Ioc (-1 / 2 : ℝ) (1 / 2), ‖jet j U (q, Y)‖ := by
    refine integral_mono ?_ ?_ (fun q => norm_iteratedFDeriv_coord_le hU 0 j (q, Y))
    · exact (((hU0.continuous_iteratedFDeriv (m := j) (mod_cast le_top)).comp
        (continuous_id.prodMk continuous_const)).norm).integrableOn_Ioc
    · exact (((hU.continuous_iteratedFDeriv (m := j) (mod_cast le_top)).comp
        (continuous_id.prodMk continuous_const)).norm).integrableOn_Ioc
  simpa [hmean] using h1.trans h2

private theorem norm_jet_le_of_supNormD {U : Plane → Vec} {C : ℝ} (hC : 0 ≤ C) (j : ℕ)
    (hsup : B0277.supNormD j U ≤ ENNReal.ofReal C) (z : Plane) :
    ‖jet j U z‖ ≤ C := by
  have hz : ‖jet j U z‖ₑ ≤ ENNReal.ofReal C :=
    (le_iSup (fun w : Plane => ‖iteratedFDeriv ℝ j U w‖ₑ) z).trans hsup
  rw [← ofReal_norm] at hz
  exact (ENNReal.ofReal_le_ofReal_iff hC).1 hz

private theorem eLpNorm_top_le_of_norm_le_hmean {g : ℝ → ℝ}
    {C : ℝ} (_hC : 0 ≤ C) (hle : ∀ Y : ℝ, ‖g Y‖ ≤ C) :
    eLpNorm g ⊤ volume ≤ ENNReal.ofReal C := by
  rw [eLpNorm_exponent_top]
  refine essSup_le_of_ae_le _ (ae_of_all _ fun Y => ?_)
  dsimp only
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hle Y)

private theorem hmean_unit_le_const_of_le {F : Plane → ℝ} {C : ℝ}
    (hle : ∀ z : Plane, ‖F z‖ ≤ C) (Y : ℝ) :
    hmean 1 F Y ≤ C := by
  have h2 := meanEnergy_norm_hmean_le (c := 1) one_pos (F := F) (G := fun _ : Plane => C)
    continuous_const hle Y
  have h3 : (1 : ℝ)⁻¹ * ∫ _q in Ico (-1 / 2 : ℝ) (1 / 2), C = C := by
    rw [inv_one, one_mul, setIntegral_const, Measure.real, Real.volume_Ico,
      show (1 / 2 : ℝ) - (-1 / 2) = 1 by ring, ENNReal.ofReal_one, ENNReal.toReal_one,
      one_smul]
  rw [h3] at h2
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h2)

theorem eLpNorm_iteratedDeriv_b_top_le {U : Plane → Vec} (hU : ContDiff ℝ ∞ U)
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ)
    (hsup : B0277.supNormD j U ≤ ENNReal.ofReal C) :
    eLpNorm (iteratedDeriv j (fun Y => hmean 1 U Y 0)) ⊤ volume ≤ ENNReal.ofReal C := by
  refine eLpNorm_top_le_of_norm_le_hmean hC fun Y => ?_
  refine (norm_iteratedDeriv_b_le_hmean_jet hU j Y).trans ?_
  exact hmean_unit_le_const_of_le (fun z => by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_jet_le_of_supNormD hC j hsup z) Y

private theorem integral_jet_sq_le_of_cellL2 {U : Plane → Vec} (hU : ContDiff ℝ ∞ U)
    {M : ℝ} (hM : 0 ≤ M) (j : ℕ) (hl2 : cellL2 1 (jet j U) ≤ ENNReal.ofReal M) :
    Integrable (fun z : Plane => ‖jet j U z‖ ^ 2) (Cyl.cellμ 1) ∧
    ∫ z : Plane, ‖jet j U z‖ ^ 2 ∂(Cyl.cellμ 1) ≤ M ^ 2 := by
  have hjet_cont : Continuous (fun z : Plane => ‖jet j U z‖) :=
    (hU.continuous_iteratedFDeriv (m := j) (mod_cast le_top)).norm
  have hmem : MemLp (fun z : Plane => ‖jet j U z‖) 2 (Cyl.cellμ 1) := by
    refine ⟨hjet_cont.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_norm]
    exact hl2.trans_lt ENNReal.ofReal_lt_top
  have heq_U : cellL2 1 (jet j U) =
      ENNReal.ofReal (Real.sqrt (∫ z : Plane, ‖jet j U z‖ ^ 2 ∂(Cyl.cellμ 1))) := by
    unfold cellL2
    rw [← eLpNorm_norm]
    have h := jl2_abs_eLpNorm (Cyl.cellμ 1) (fun z : Plane => ‖jet j U z‖) hmem
    simpa [abs_of_nonneg (norm_nonneg _)] using h
  have hsqrt_le : Real.sqrt (∫ z : Plane, ‖jet j U z‖ ^ 2 ∂(Cyl.cellμ 1)) ≤ M := by
    rw [heq_U] at hl2
    exact (ENNReal.ofReal_le_ofReal_iff hM).1 hl2
  have hint_nonneg : 0 ≤ ∫ z : Plane, ‖jet j U z‖ ^ 2 ∂(Cyl.cellμ 1) :=
    integral_nonneg fun _ => sq_nonneg _
  refine ⟨hmem.integrable_sq, ?_⟩
  calc ∫ z : Plane, ‖jet j U z‖ ^ 2 ∂(Cyl.cellμ 1)
      = (Real.sqrt (∫ z : Plane, ‖jet j U z‖ ^ 2 ∂(Cyl.cellμ 1))) ^ 2 :=
        (Real.sq_sqrt hint_nonneg).symm
    _ ≤ M ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 2

private theorem eLpNorm_two_le_of_hmean_sq_bound {g : ℝ → ℝ} (hg : Continuous g)
    {F G : Plane → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hG_int : Integrable G (Cyl.cellμ 1))
    (hFG : ∀ z : Plane, F z ^ 2 ≤ G z)
    (hgF : ∀ Y : ℝ, ‖g Y‖ ≤ hmean 1 F Y)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∫ z : Plane, G z ∂(Cyl.cellμ 1) ≤ B ^ 2) :
    eLpNorm g 2 volume ≤ ENNReal.ofReal B := by
  have hprod : Integrable G ((volume.restrict (Ico (-1 / 2 : ℝ) (1 / 2))).prod volume) := by
    rwa [← Cyl.cellμ_eq_prod]
  have hGY : Integrable (fun Y : ℝ => ∫ q in Ico (-1 / 2 : ℝ) (1 / 2), G (q, Y)) :=
    hprod.integral_prod_right
  have hg_sq : ∀ Y : ℝ, g Y ^ 2 ≤ ∫ q in Ico (-1 / 2 : ℝ) (1 / 2), G (q, Y) := by
    intro Y
    have h1 := hgF Y
    have h2 : g Y ^ 2 ≤ hmean 1 F Y ^ 2 := by
      rw [← sq_abs (g Y), ← Real.norm_eq_abs]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := meanEnergy_hmean_sq_le (c := 1) one_pos hF hG hFG Y
    rw [inv_one, one_mul] at h3
    exact h2.trans h3
  have hg_mem : MemLp g 2 volume := by
    refine (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 ?_
    refine Integrable.mono' hGY (hg.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun Y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg (g Y))]
    exact hg_sq Y
  have heq_g : eLpNorm g 2 volume = ENNReal.ofReal (Real.sqrt (∫ Y : ℝ, g Y ^ 2)) := by
    have h := hg_mem.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num)
    have e2 : ∀ Y : ℝ, ‖g Y‖ ^ (2 : ℝ) = g Y ^ 2 := fun Y => by
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    rw [h]
    simp only [e2, ENNReal.toReal_ofNat]
    rw [Real.sqrt_eq_rpow, one_div]
  have hint_le : ∫ Y : ℝ, g Y ^ 2 ≤ B ^ 2 := by
    calc ∫ Y : ℝ, g Y ^ 2
        ≤ ∫ Y : ℝ, ∫ q in Ico (-1 / 2 : ℝ) (1 / 2), G (q, Y) :=
          integral_mono hg_mem.integrable_sq hGY hg_sq
      _ = ∫ z : Plane, G z ∂(Cyl.cellμ 1) := by
          rw [Cyl.cellμ_eq_prod, ← MeasureTheory.integral_prod_symm _ hprod]
      _ ≤ B ^ 2 := hB
  rw [heq_g]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.sqrt (∫ Y : ℝ, g Y ^ 2)
      ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hint_le
    _ = B := Real.sqrt_sq hB0

theorem eLpNorm_iteratedDeriv_b_two_le {U : Plane → Vec} (hU : ContDiff ℝ ∞ U)
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ) (hl2 : cellL2 1 (jet j U) ≤ ENNReal.ofReal C) :
    eLpNorm (iteratedDeriv j (fun Y => hmean 1 U Y 0)) 2 volume ≤ ENNReal.ofReal C := by
  have hb_cd : ContDiff ℝ ∞ (fun Y : ℝ => hmean 1 U Y 0) := contDiff_hmean_unit_fst hU
  have hg_cont : Continuous (iteratedDeriv j (fun Y => hmean 1 U Y 0)) :=
    (hb_cd.of_le (by simp)).continuous_iteratedDeriv' j
  have hjet_cont : Continuous (fun z : Plane => ‖jet j U z‖) :=
    (hU.continuous_iteratedFDeriv (m := j) (mod_cast le_top)).norm
  obtain ⟨hG_int, hG_le⟩ := integral_jet_sq_le_of_cellL2 hU hC j hl2
  exact eLpNorm_two_le_of_hmean_sq_bound hg_cont hjet_cont (hjet_cont.pow 2) hG_int
    (fun _ => le_rfl) (norm_iteratedDeriv_b_le_hmean_jet hU j) hC hG_le

theorem overlapMeanDecay_shortTime (hHN : OverlapHighNormUniform) (ρ : ℝ) (hρ : 1 / 2 < ρ)
    (j : ℕ) :
    ∃ C_short ν₀ : ℝ, 0 < C_short ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ T : ℝ, 0 ≤ T → T ≤ 1 →
            let U := overlapField ν (trainPeriod ρ ν) tr.v T
            let b : ℝ → ℝ := fun Y => hmean 1 U Y 0
            eLpNorm (iteratedDeriv j b) 2 volume ≤
                ENNReal.ofReal (C_short * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) ∧
            eLpNorm (iteratedDeriv j b) ⊤ volume ≤
                ENNReal.ofReal (C_short * (1 + T) ^ (-1 - (j : ℝ) / 2)) := by
  obtain ⟨C, ν₁, hC, hν₁, hU_bound⟩ := hHN ρ hρ j
  refine ⟨C * 2 ^ (1 + (j : ℝ) / 2), min ν₁ (1 / 2), by positivity,
    lt_min hν₁ (by norm_num), ?_⟩
  intro ν hν hν_le tr htr T hT hT1
  dsimp only
  let c := trainPeriod ρ ν
  have hν_1 : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
  have hc1 : 1 < c := by
    unfold c trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  have hs : 0 ≤ B0146.overlapAge ν c + c ^ 2 * T / ν :=
    (overlapAge_add_pos hν hc1 hT).le
  have hU_cd : ContDiff ℝ ∞ (overlapField ν c tr.v T) :=
    contDiff_overlapField_slice tr hs
  obtain ⟨hl2, hsup⟩ := hU_bound ν hν hν_1 tr htr T hT j le_rfl
  have hbl2 := eLpNorm_iteratedDeriv_b_two_le hU_cd hC.le j hl2
  have hbsup := eLpNorm_iteratedDeriv_b_top_le hU_cd hC.le j hsup
  have h1T_pos : 0 < 1 + T := by linarith
  have h1T_le2 : 1 + T ≤ 2 := by linarith
  have hpow_sup : 1 ≤ 2 ^ (1 + (j : ℝ) / 2) * (1 + T) ^ (-1 - (j : ℝ) / 2) := by
    have hle : (1 + T) ^ (1 + (j : ℝ) / 2) ≤ 2 ^ (1 + (j : ℝ) / 2) :=
      Real.rpow_le_rpow h1T_pos.le h1T_le2 (by positivity)
    have hmul : (1 + T) ^ (1 + (j : ℝ) / 2) * (1 + T) ^ (-1 - (j : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add h1T_pos]
      have : (1 + (j : ℝ) / 2) + (-1 - (j : ℝ) / 2) = 0 := by ring
      rw [this, Real.rpow_zero]
    nlinarith [Real.rpow_pos_of_pos h1T_pos (-1 - (j : ℝ) / 2)]
  have hpow_l2 : 1 ≤ 2 ^ (1 + (j : ℝ) / 2) * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4) := by
    have h1T_ge1 : 1 ≤ 1 + T := by linarith
    have hle : (1 + T) ^ (-1 - (j : ℝ) / 2) ≤ (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4) :=
      Real.rpow_le_rpow_of_exponent_le h1T_ge1 (by linarith)
    nlinarith [(by positivity : (0 : ℝ) ≤ 2 ^ (1 + (j : ℝ) / 2))]
  refine ⟨hbl2.trans (ENNReal.ofReal_le_ofReal (by nlinarith)),
    hbsup.trans (ENNReal.ofReal_le_ofReal (by nlinarith))⟩

/-! ### 4. `L¹_Y`, `L²_Y`, and `L^∞_Y` bounds on `overlapStressProfile` and its derivatives -/

/-- `L¹_Y` bound on `hmean 1 (fun z => W z 0 * W z 1)` from `cellL2 1 (jet 0 W) ≤ ofReal M`. -/
theorem eLpNorm_hmean_prod_one_le {W : Plane → Vec} (hW : ContDiff ℝ ∞ W)
    {M : ℝ} (hM : 0 ≤ M) (hl2 : cellL2 1 (jet 0 W) ≤ ENNReal.ofReal M) :
    eLpNorm (hmean 1 (fun z : Plane => W z 0 * W z 1)) 1 volume ≤ ENNReal.ofReal (M ^ 2) := by
  set Φ : Plane → ℝ := fun z => W z 0 * W z 1
  have hW0 : Continuous (fun z : Plane => W z 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp hW.continuous
  have hW1 : Continuous (fun z : Plane => W z 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp hW.continuous
  have hg_cont : Continuous (hmean 1 Φ) := meanEnergy_hmean_continuous (hW0.mul hW1)
  have hjet_cont : Continuous (fun z : Plane => ‖jet 0 W z‖ ^ 2) :=
    ((hW.continuous_iteratedFDeriv (m := 0) (mod_cast le_top)).norm).pow 2
  obtain ⟨hG_int, hG_le⟩ := integral_jet_sq_le_of_cellL2 hW hM 0 hl2
  have hprod : Integrable (fun z : Plane => ‖jet 0 W z‖ ^ 2)
      ((volume.restrict (Ico (-1 / 2 : ℝ) (1 / 2))).prod volume) := by
    rwa [← Cyl.cellμ_eq_prod]
  have hGY : Integrable (fun Y : ℝ => ∫ q in Ico (-1 / 2 : ℝ) (1 / 2), ‖jet 0 W (q, Y)‖ ^ 2) :=
    hprod.integral_prod_right
  have hpt : ∀ z : Plane, ‖Φ z‖ ≤ ‖jet 0 W z‖ ^ 2 := by
    intro z
    have h0 : ‖jet 0 W z‖ = ‖W z‖ := by simp [jet, norm_iteratedFDeriv_zero]
    rw [h0]
    exact meanEnergy_norm_mul_coord_le (W z)
  have hY_bound : ∀ Y : ℝ, ‖hmean 1 Φ Y‖ ≤
      ∫ q in Ico (-1 / 2 : ℝ) (1 / 2), ‖jet 0 W (q, Y)‖ ^ 2 := by
    intro Y
    have h := meanEnergy_norm_hmean_le (c := 1) one_pos hjet_cont hpt Y
    simpa using h
  have hg_int : Integrable (hmean 1 Φ) volume :=
    Integrable.mono' hGY hg_cont.aestronglyMeasurable (Eventually.of_forall hY_bound)
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hg_int]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ Y : ℝ, ‖hmean 1 Φ Y‖
      ≤ ∫ Y : ℝ, ∫ q in Ico (-1 / 2 : ℝ) (1 / 2), ‖jet 0 W (q, Y)‖ ^ 2 :=
        integral_mono hg_int.norm hGY hY_bound
    _ = ∫ z : Plane, ‖jet 0 W z‖ ^ 2 ∂(Cyl.cellμ 1) := by
        rw [Cyl.cellμ_eq_prod, ← MeasureTheory.integral_prod_symm _ hprod]
    _ ≤ M ^ 2 := hG_le

/-- Pointwise Leibniz bound on `iteratedFDeriv ℝ k (fun z => W z 0 * W z 1)`. -/
private theorem norm_iteratedFDeriv_prod_le {W : Plane → Vec} (hW : ContDiff ℝ ∞ W)
    {M : ℝ} (hM : 0 ≤ M) (k : ℕ)
    (hsup : ∀ i ≤ k, B0277.supNormD i W ≤ ENNReal.ofReal M) (z : Plane) :
    ‖iteratedFDeriv ℝ k (fun w : Plane => W w 0 * W w 1) z‖ ≤
      ∑ i ∈ Finset.range (k + 1), (2 ^ k * M) * ‖jet i W z‖ := by
  have hW0 : ContDiff ℝ ∞ (fun w : Plane => W w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hW
  have hW1 : ContDiff ℝ ∞ (fun w : Plane => W w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hW
  have hleib := norm_iteratedFDeriv_mul_le hW0 hW1 z (n := k) (mod_cast le_top)
  refine hleib.trans (Finset.sum_le_sum fun i hi => ?_)
  have hi_le : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hki_le : k - i ≤ k := Nat.sub_le k i
  have hchoose : (k.choose i : ℝ) ≤ (2 ^ k : ℝ) := by
    exact_mod_cast Nat.choose_le_two_pow k i
  have h0_le : ‖iteratedFDeriv ℝ i (fun w : Plane => W w 0) z‖ ≤ ‖jet i W z‖ :=
    norm_iteratedFDeriv_coord_le hW 0 i z
  have h1_le : ‖iteratedFDeriv ℝ (k - i) (fun w : Plane => W w 1) z‖ ≤ M :=
    (norm_iteratedFDeriv_coord_le hW 1 (k - i) z).trans
      (norm_jet_le_of_supNormD hM (k - i) (hsup (k - i) hki_le) z)
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w : Plane => W w 0) z‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun w : Plane => W w 1) z‖
      ≤ (2 ^ k : ℝ) * ‖jet i W z‖ * M := by
        refine mul_le_mul (mul_le_mul hchoose h0_le (norm_nonneg _) (by positivity))
          h1_le (norm_nonneg _) (by positivity)
    _ = (2 ^ k * M) * ‖jet i W z‖ := by ring

/-- `L²_Y` and `L^∞_Y` bounds on `iteratedDeriv k (hmean 1 (fun z => W z 0 * W z 1))`
from bounds on `cellL2 1 (jet i W)` and `supNormD i W` for `i ≤ k`. -/
theorem eLpNorm_iteratedDeriv_hmean_prod_le {W : Plane → Vec} (hW : ContDiff ℝ ∞ W)
    {M : ℝ} (hM : 0 ≤ M) (k : ℕ)
    (hl2 : ∀ i ≤ k, cellL2 1 (jet i W) ≤ ENNReal.ofReal M)
    (hsup : ∀ i ≤ k, B0277.supNormD i W ≤ ENNReal.ofReal M) :
    eLpNorm (iteratedDeriv k (hmean 1 (fun z : Plane => W z 0 * W z 1))) 2 volume ≤
        ENNReal.ofReal ((k + 1 : ℝ) * 2 ^ k * M ^ 2) ∧
    eLpNorm (iteratedDeriv k (hmean 1 (fun z : Plane => W z 0 * W z 1))) ⊤ volume ≤
        ENNReal.ofReal ((k + 1 : ℝ) * 2 ^ k * M ^ 2) := by
  set Φ : Plane → ℝ := fun z => W z 0 * W z 1
  have hW0 : ContDiff ℝ ∞ (fun w : Plane => W w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hW
  have hW1 : ContDiff ℝ ∞ (fun w : Plane => W w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hW
  have hΦ : ContDiff ℝ ∞ Φ := hW0.mul hW1
  set F : Plane → ℝ := fun z => ∑ i ∈ Finset.range (k + 1), (2 ^ k * M) * ‖jet i W z‖
  have hF_cont : Continuous F :=
    continuous_finsetSum _ fun i _ => continuous_const.mul
      ((hW.continuous_iteratedFDeriv (m := i) (mod_cast le_top)).norm)
  have hgF : ∀ Y : ℝ, ‖iteratedDeriv k (hmean 1 Φ) Y‖ ≤ hmean 1 F Y := by
    intro Y
    have h1 := norm_iteratedDeriv_hmean_unit_le hΦ k Y
    have h2 : ∫ q in Ioc (-1 / 2 : ℝ) (1 / 2), ‖iteratedFDeriv ℝ k Φ (q, Y)‖ ≤
        ∫ q in Ioc (-1 / 2 : ℝ) (1 / 2), F (q, Y) := by
      refine integral_mono ?_ ?_ (fun q => norm_iteratedFDeriv_prod_le hW hM k hsup (q, Y))
      · exact (((hΦ.continuous_iteratedFDeriv (m := k) (mod_cast le_top)).comp
          (continuous_id.prodMk continuous_const)).norm).integrableOn_Ioc
      · exact (hF_cont.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
    simpa [hmean] using h1.trans h2
  have hB0 : 0 ≤ (k + 1 : ℝ) * 2 ^ k * M ^ 2 := by positivity
  have htop : eLpNorm (iteratedDeriv k (hmean 1 Φ)) ⊤ volume ≤
      ENNReal.ofReal ((k + 1 : ℝ) * 2 ^ k * M ^ 2) := by
    refine eLpNorm_top_le_of_norm_le_hmean hB0 fun Y => (hgF Y).trans ?_
    refine hmean_unit_le_const_of_le (fun z => ?_) Y
    have hF_nonneg : 0 ≤ F z := Finset.sum_nonneg fun i _ => by positivity
    rw [Real.norm_of_nonneg hF_nonneg]
    calc ∑ i ∈ Finset.range (k + 1), (2 ^ k * M) * ‖jet i W z‖
        ≤ ∑ _i ∈ Finset.range (k + 1), (2 ^ k * M) * M := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi_le : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          exact mul_le_mul_of_nonneg_left
            (norm_jet_le_of_supNormD hM i (hsup i hi_le) z) (by positivity)
      _ = (k + 1 : ℝ) * 2 ^ k * M ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          ring
  set G : Plane → ℝ := fun z =>
    (k + 1 : ℝ) * ∑ i ∈ Finset.range (k + 1), ((2 ^ k * M) * ‖jet i W z‖) ^ 2
  have hG_cont : Continuous G :=
    continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (continuous_const.mul ((hW.continuous_iteratedFDeriv (m := i) (mod_cast le_top)).norm)).pow 2)
  have hFG : ∀ z : Plane, F z ^ 2 ≤ G z := by
    intro z
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 1))
      (f := fun i => (2 ^ k * M) * ‖jet i W z‖)
    simpa [F, G, Finset.card_range, Nat.cast_add, Nat.cast_one] using hcs
  have hterm_int : ∀ i ∈ Finset.range (k + 1),
      Integrable (fun z : Plane => ((2 ^ k * M) * ‖jet i W z‖) ^ 2) (Cyl.cellμ 1) ∧
      ∫ z : Plane, ((2 ^ k * M) * ‖jet i W z‖) ^ 2 ∂(Cyl.cellμ 1) ≤ (2 ^ k * M ^ 2) ^ 2 := by
    intro i hi
    have hi_le : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    obtain ⟨hi_int, hi_le_M2⟩ := integral_jet_sq_le_of_cellL2 hW hM i (hl2 i hi_le)
    have hfun : (fun z : Plane => ((2 ^ k * M) * ‖jet i W z‖) ^ 2) =
        fun z : Plane => (2 ^ k * M) ^ 2 * ‖jet i W z‖ ^ 2 := by
      funext z; ring
    rw [hfun]
    refine ⟨hi_int.const_mul _, ?_⟩
    rw [integral_const_mul]
    calc (2 ^ k * M) ^ 2 * ∫ z : Plane, ‖jet i W z‖ ^ 2 ∂(Cyl.cellμ 1)
        ≤ (2 ^ k * M) ^ 2 * M ^ 2 :=
          mul_le_mul_of_nonneg_left hi_le_M2 (sq_nonneg _)
      _ = (2 ^ k * M ^ 2) ^ 2 := by ring
  have hG_int : Integrable G (Cyl.cellμ 1) :=
    (integrable_finsetSum _ fun i hi => (hterm_int i hi).1).const_mul _
  have hG_le : ∫ z : Plane, G z ∂(Cyl.cellμ 1) ≤ ((k + 1 : ℝ) * 2 ^ k * M ^ 2) ^ 2 := by
    change ∫ z : Plane, ((k + 1 : ℝ) *
        ∑ i ∈ Finset.range (k + 1), ((2 ^ k * M) * ‖jet i W z‖) ^ 2) ∂(Cyl.cellμ 1) ≤ _
    rw [integral_const_mul, integral_finsetSum _ fun i hi => (hterm_int i hi).1]
    have hsum : ∑ i ∈ Finset.range (k + 1),
        ∫ z : Plane, ((2 ^ k * M) * ‖jet i W z‖) ^ 2 ∂(Cyl.cellμ 1) ≤
        ∑ _i ∈ Finset.range (k + 1), (2 ^ k * M ^ 2) ^ 2 :=
      Finset.sum_le_sum fun i hi => (hterm_int i hi).2
    calc (k + 1 : ℝ) * ∑ i ∈ Finset.range (k + 1),
            ∫ z : Plane, ((2 ^ k * M) * ‖jet i W z‖) ^ 2 ∂(Cyl.cellμ 1)
        ≤ (k + 1 : ℝ) * ∑ _i ∈ Finset.range (k + 1), (2 ^ k * M ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ((k + 1 : ℝ) * 2 ^ k * M ^ 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          ring
  have hg_cont : Continuous (iteratedDeriv k (hmean 1 Φ)) :=
    ((contDiff_hmean_unit hΦ).of_le (by simp)).continuous_iteratedDeriv' k
  have hl2_bound := eLpNorm_two_le_of_hmean_sq_bound hg_cont hF_cont hG_cont hG_int hFG hgF
    hB0 hG_le
  exact ⟨hl2_bound, htop⟩

/-! ### 5. Finite-range extraction from `OverlapFluctuationDecay` and time-integral bounds -/

/-- From `OverlapFluctuationDecay`, for any `ρ > 1/2` and `N : ℕ`, there exist common constants
`C > 0`, `lam > 0`, `ν₀ > 0` valid simultaneously for all derivative orders `i ≤ N`. -/
theorem overlapFluctuationDecay_finRange (hFD : OverlapFluctuationDecay) (ρ : ℝ) (hρ : 1 / 2 < ρ)
    (N : ℕ) :
    ∃ C lam ν₀ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ t : ℝ, 0 ≤ t → ∀ i ≤ N,
            let U := overlapField ν (trainPeriod ρ ν) tr.v t
            cellL2 1 (jet i (hfluct 1 U)) ≤ ENNReal.ofReal (C * Real.exp (-(lam * t))) ∧
            B0277.supNormD i (hfluct 1 U) ≤ ENNReal.ofReal (C * Real.exp (-(lam * t))) := by
  induction N with
  | zero =>
    obtain ⟨C, lam, ν₀, hC, hlam, hν₀, h0⟩ := hFD ρ hρ 0
    refine ⟨C, lam, ν₀, hC, hlam, hν₀, fun ν hν hν_le tr htr t ht i hi => ?_⟩
    have hi0 : i = 0 := Nat.le_zero.1 hi
    subst hi0
    exact h0 ν hν hν_le tr htr t ht
  | succ N ih =>
    obtain ⟨C₁, lam₁, ν₁, hC₁, hlam₁, hν₁, h₁⟩ := ih
    obtain ⟨C₂, lam₂, ν₂, hC₂, hlam₂, hν₂, h₂⟩ := hFD ρ hρ (N + 1)
    refine ⟨max C₁ C₂, min lam₁ lam₂, min ν₁ ν₂, lt_max_of_lt_left hC₁,
      lt_min hlam₁ hlam₂, lt_min hν₁ hν₂, ?_⟩
    intro ν hν hν_le tr htr t ht i hi
    have hν₁' : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
    have hν₂' : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
    rcases Nat.of_le_succ hi with hiN | rfl
    · obtain ⟨hl2, hsup⟩ := h₁ ν hν hν₁' tr htr t ht i hiN
      have hle : C₁ * Real.exp (-(lam₁ * t)) ≤ (max C₁ C₂) * Real.exp (-(min lam₁ lam₂ * t)) := by
        refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 ?_) (Real.exp_nonneg _)
          (hC₁.le.trans (le_max_left _ _))
        exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) ht)
      exact ⟨hl2.trans (ENNReal.ofReal_le_ofReal hle), hsup.trans (ENNReal.ofReal_le_ofReal hle)⟩
    · obtain ⟨hl2, hsup⟩ := h₂ ν hν hν₂' tr htr t ht
      have hle : C₂ * Real.exp (-(lam₂ * t)) ≤ (max C₁ C₂) * Real.exp (-(min lam₁ lam₂ * t)) := by
        refine mul_le_mul (le_max_right _ _) (Real.exp_le_exp.2 ?_) (Real.exp_nonneg _)
          (hC₁.le.trans (le_max_left _ _))
        exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) ht)
      exact ⟨hl2.trans (ENNReal.ofReal_le_ofReal hle), hsup.trans (ENNReal.ofReal_le_ofReal hle)⟩

/-- Exponential time-integral bound on `Ioc t₁ t₂`:
`∫⁻ t in Ioc t₁ t₂, ofReal (C * exp (-(a * t))) ≤ ofReal ((C / a) * exp (-(a * t₁)))`. -/
theorem lintegral_Ioc_exp_neg_le {C a t₁ t₂ : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (ht : t₁ ≤ t₂) :
    ∫⁻ t in Ioc t₁ t₂, ENNReal.ofReal (C * Real.exp (-(a * t))) ≤
      ENNReal.ofReal ((C / a) * Real.exp (-(a * t₁))) := by
  set f : ℝ → ℝ := fun t => C * Real.exp (-(a * t))
  set F : ℝ → ℝ := fun t => -(C / a) * Real.exp (-(a * t))
  have hf_cont : Continuous f :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
  have hf_int : IntegrableOn f (Ioc t₁ t₂) volume := hf_cont.integrableOn_Ioc
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Ioc t₁ t₂)] f :=
    ae_of_all _ fun t => mul_nonneg hC (Real.exp_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hf_int hf_nonneg,
    ← intervalIntegral.integral_of_le ht]
  have hderiv : ∀ t ∈ uIcc t₁ t₂, HasDerivAt F (f t) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => -(a * s)) (-a) t := by
      have h0 : HasDerivAt (fun s : ℝ => a * s) (a * 1) t := (hasDerivAt_id t).const_mul a
      rw [mul_one] at h0
      exact h0.neg
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(a * s))) (Real.exp (-(a * t)) * (-a)) t :=
      h1.exp
    have h3 := h2.const_mul (-(C / a))
    have heq : -(C / a) * (Real.exp (-(a * t)) * (-a)) = f t := by
      dsimp [f]
      field_simp [ha.ne']
    rwa [heq] at h3
  have hint_ivl : IntervalIntegrable f volume t₁ t₂ := hf_cont.intervalIntegrable t₁ t₂
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_ivl]
  refine ENNReal.ofReal_le_ofReal ?_
  dsimp [F]
  have hpos : 0 ≤ (C / a) * Real.exp (-(a * t₂)) := by positivity
  linarith

private theorem pow_mul_exp_neg_le_factorial (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    s ^ k * Real.exp (-s) ≤ (k.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (x := s) hs k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hf] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos s)]
  linarith [mul_comm (Real.exp s) (k.factorial : ℝ)]

/-- Absorption constant for `exp (-(a * (T / 2))) ≤ C_abs * (1 + T) ^ (-1 - j / 2)` on `T ≥ 1`. -/
def expAbsorbConst (a : ℝ) (j : ℕ) : ℝ :=
  (4 / a) ^ (j + 1) * ((j + 1).factorial : ℝ)

theorem expAbsorbConst_pos {a : ℝ} (ha : 0 < a) (j : ℕ) : 0 < expAbsorbConst a j := by
  unfold expAbsorbConst
  have hf : (0 : ℝ) < (j + 1).factorial := by exact_mod_cast Nat.factorial_pos (j + 1)
  positivity

theorem exp_neg_half_le_rpow {a T : ℝ} (ha : 0 < a) (hT : 1 ≤ T) (j : ℕ) :
    Real.exp (-(a * (T / 2))) ≤ expAbsorbConst a j * (1 + T) ^ (-1 - (j : ℝ) / 2) ∧
    Real.exp (-(a * (T / 2))) ≤ expAbsorbConst a j * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4) := by
  have h1T_pos : 0 < 1 + T := by linarith
  have h1T_ge1 : 1 ≤ 1 + T := by linarith
  have hs_nonneg : 0 ≤ a * (T / 2) := by positivity
  have h1T_le : 1 + T ≤ (4 / a) * (a * (T / 2)) := by
    have : (4 / a) * (a * (T / 2)) = 2 * T := by field_simp [ha.ne']; ring
    linarith
  have hpow1 : (1 + T) ^ (1 + (j : ℝ) / 2) ≤ (1 + T) ^ ((j + 1 : ℕ) : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le h1T_ge1 ?_
    push_cast
    linarith
  rw [Real.rpow_natCast] at hpow1
  have hpow2 : (1 + T) ^ (j + 1) ≤ (4 / a) ^ (j + 1) * (a * (T / 2)) ^ (j + 1) := by
    calc (1 + T) ^ (j + 1)
        ≤ ((4 / a) * (a * (T / 2))) ^ (j + 1) :=
          pow_le_pow_left₀ h1T_pos.le h1T_le (j + 1)
      _ = (4 / a) ^ (j + 1) * (a * (T / 2)) ^ (j + 1) := mul_pow _ _ _
  have hfac := pow_mul_exp_neg_le_factorial (j + 1) hs_nonneg
  have hprod : (1 + T) ^ (1 + (j : ℝ) / 2) * Real.exp (-(a * (T / 2))) ≤ expAbsorbConst a j := by
    calc (1 + T) ^ (1 + (j : ℝ) / 2) * Real.exp (-(a * (T / 2)))
        ≤ ((4 / a) ^ (j + 1) * (a * (T / 2)) ^ (j + 1)) * Real.exp (-(a * (T / 2))) :=
          mul_le_mul_of_nonneg_right (hpow1.trans hpow2) (Real.exp_nonneg _)
      _ = (4 / a) ^ (j + 1) * ((a * (T / 2)) ^ (j + 1) * Real.exp (-(a * (T / 2)))) := by ring
      _ ≤ (4 / a) ^ (j + 1) * ((j + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = expAbsorbConst a j := rfl
  have hmul_inv : (1 + T) ^ (1 + (j : ℝ) / 2) * (1 + T) ^ (-1 - (j : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add h1T_pos]
    have : (1 + (j : ℝ) / 2) + (-1 - (j : ℝ) / 2) = 0 := by ring
    rw [this, Real.rpow_zero]
  have hbase : Real.exp (-(a * (T / 2))) ≤ expAbsorbConst a j * (1 + T) ^ (-1 - (j : ℝ) / 2) := by
    have h := mul_le_mul_of_nonneg_right hprod
      (Real.rpow_nonneg h1T_pos.le (-1 - (j : ℝ) / 2))
    calc Real.exp (-(a * (T / 2)))
        = ((1 + T) ^ (1 + (j : ℝ) / 2) * (1 + T) ^ (-1 - (j : ℝ) / 2)) *
            Real.exp (-(a * (T / 2))) := by rw [hmul_inv, one_mul]
      _ = ((1 + T) ^ (1 + (j : ℝ) / 2) * Real.exp (-(a * (T / 2)))) *
            (1 + T) ^ (-1 - (j : ℝ) / 2) := by ring
      _ ≤ expAbsorbConst a j * (1 + T) ^ (-1 - (j : ℝ) / 2) := h
  have hrpow_le : (1 + T) ^ (-1 - (j : ℝ) / 2) ≤ (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4) :=
    Real.rpow_le_rpow_of_exponent_le h1T_ge1 (by linarith)
  refine ⟨hbase, hbase.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hrpow_le (expAbsorbConst_pos ha j).le

/-! ### 6. Long-time (`T ≥ 1`) decay from `OverlapMeanDuhamelSplit` -/

theorem overlapMeanDecay_longTime (hFD : OverlapFluctuationDecay) (hMP : OverlapMeanPrimitive)
    (hDuh : OverlapMeanDuhamelSplit) (ρ : ℝ) (hρ : 1 / 2 < ρ) (j : ℕ) :
    ∃ C_long ν₀ : ℝ, 0 < C_long ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          ∀ T : ℝ, 1 ≤ T →
            let U := overlapField ν (trainPeriod ρ ν) tr.v T
            let b : ℝ → ℝ := fun Y => hmean 1 U Y 0
            eLpNorm (iteratedDeriv j b) 2 volume ≤
                ENNReal.ofReal (C_long * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) ∧
            eLpNorm (iteratedDeriv j b) ⊤ volume ≤
                ENNReal.ofReal (C_long * (1 + T) ^ (-1 - (j : ℝ) / 2)) := by
  obtain ⟨C_MP, ν_MP, hC_MP, hν_MP, hMP_bound⟩ := hMP ρ hρ
  obtain ⟨C_W, lam, ν_W, hC_W, hlam, hν_W, hW_bound⟩ :=
    overlapFluctuationDecay_finRange hFD ρ hρ (j + 1)
  obtain ⟨C_G, hC_G, hDuh_j⟩ := hDuh j
  obtain ⟨ν_asym, hν_asym, _, hAsym⟩ := trainPeriodAsymptotics_proof ρ hρ 2 two_pos
  set A_k : ℝ := ((j + 1 : ℕ) + 1 : ℝ) * 2 ^ (j + 1) * C_W ^ 2
  have hA_k : 0 < A_k := by positivity
  set C_early : ℝ := C_MP + C_W ^ 2 / (2 * lam)
  set C_late : ℝ := (A_k / (2 * lam)) * expAbsorbConst (2 * lam) j
  set C_long : ℝ := C_G * C_early + C_late
  have hC_long : 0 < C_long := by
    have : 0 < expAbsorbConst (2 * lam) j := expAbsorbConst_pos (by positivity) j
    positivity
  refine ⟨C_long, min (min ν_MP ν_W) (min ν_asym (1 / 2)), hC_long,
    lt_min (lt_min hν_MP hν_W) (lt_min hν_asym (by norm_num)), ?_⟩
  intro ν hν hν_le tr htr T hT1
  dsimp only
  let c := trainPeriod ρ ν
  have hν_MP' : ν ≤ ν_MP := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_W' : ν ≤ ν_W := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_asym' : ν ≤ ν_asym := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_half : ν ≤ 1 / 2 := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc1 : 1 < c := by
    unfold c trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  obtain ⟨_, hνc2_ge2⟩ := hAsym ν hν hν_asym'
  have heC_pos : 0 ≤ eC ν c := by unfold eC; positivity
  have heC_le1 : eC ν c ≤ 1 := by
    unfold eC
    rw [inv_le_one_iff₀]
    right
    linarith
  have hS0_le : eLpNorm (overlapMeanStream tr 0) 1 volume ≤ ENNReal.ofReal C_MP :=
    (hMP_bound ν hν hν_MP' tr htr).2.2
  have hg_bounds : ∀ t : ℝ, 0 ≤ t →
      eLpNorm (overlapStressProfile tr t) 1 volume ≤
        ENNReal.ofReal (C_W ^ 2 * Real.exp (-(2 * lam * t))) ∧
      eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) 2 volume ≤
        ENNReal.ofReal (A_k * Real.exp (-(2 * lam * t))) ∧
      eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) ⊤ volume ≤
        ENNReal.ofReal (A_k * Real.exp (-(2 * lam * t))) := by
    intro t ht
    have hst : 0 ≤ B0146.overlapAge ν c + c ^ 2 * t / ν :=
      (overlapAge_add_pos hν hc1 ht).le
    have hUt_cd : ContDiff ℝ ∞ (overlapField ν c tr.v t) := contDiff_overlapField_slice tr hst
    have hWt_cd : ContDiff ℝ ∞ (hfluct 1 (overlapField ν c tr.v t)) :=
      contDiff_hfluct_unit hUt_cd
    set M_t : ℝ := C_W * Real.exp (-(lam * t))
    have hM_t : 0 ≤ M_t := by positivity
    have hM_sq : M_t ^ 2 = C_W ^ 2 * Real.exp (-(2 * lam * t)) := by
      dsimp [M_t]
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hAk_eq : ((j + 1 : ℕ) + 1 : ℝ) * 2 ^ (j + 1) * M_t ^ 2 =
        A_k * Real.exp (-(2 * lam * t)) := by
      rw [hM_sq]
      dsimp [A_k]
      ring
    have hl2_0 : cellL2 1 (jet 0 (hfluct 1 (overlapField ν c tr.v t))) ≤ ENNReal.ofReal M_t :=
      (hW_bound ν hν hν_W' tr htr t ht 0 (Nat.zero_le _)).1
    have h1 := eLpNorm_hmean_prod_one_le hWt_cd hM_t hl2_0
    rw [hM_sq] at h1
    obtain ⟨h2, h3⟩ := eLpNorm_iteratedDeriv_hmean_prod_le hWt_cd hM_t (j + 1)
      (fun i hi => (hW_bound ν hν hν_W' tr htr t ht i hi).1)
      (fun i hi => (hW_bound ν hν hν_W' tr htr t ht i hi).2)
    rw [hAk_eq] at h2 h3
    exact ⟨h1, h2, h3⟩
  have h_int_early : ∫⁻ t in Ioc 0 (T / 2), eLpNorm (overlapStressProfile tr t) 1 volume ≤
      ENNReal.ofReal (C_W ^ 2 / (2 * lam)) := by
    have hmono : ∫⁻ t in Ioc 0 (T / 2), eLpNorm (overlapStressProfile tr t) 1 volume ≤
        ∫⁻ t in Ioc 0 (T / 2), ENNReal.ofReal (C_W ^ 2 * Real.exp (-(2 * lam * t))) := by
      refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
      exact (hg_bounds t ht.1.le).1
    have hcalc := lintegral_Ioc_exp_neg_le (C := C_W ^ 2) (a := 2 * lam)
      (t₁ := 0) (t₂ := T / 2) (by positivity) (by positivity) (by linarith)
    rw [mul_zero, neg_zero, Real.exp_zero, mul_one] at hcalc
    exact hmono.trans hcalc
  have hearly_le : eLpNorm (overlapMeanStream tr 0) 1 volume +
      ENNReal.ofReal (eC ν c) *
        ∫⁻ t in Ioc 0 (T / 2), eLpNorm (overlapStressProfile tr t) 1 volume ≤
      ENNReal.ofReal C_early := by
    have h1 : ENNReal.ofReal (eC ν c) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal heC_le1
    rw [ENNReal.ofReal_one] at h1
    calc eLpNorm (overlapMeanStream tr 0) 1 volume +
            ENNReal.ofReal (eC ν c) *
              ∫⁻ t in Ioc 0 (T / 2), eLpNorm (overlapStressProfile tr t) 1 volume
        ≤ ENNReal.ofReal C_MP + 1 * ENNReal.ofReal (C_W ^ 2 / (2 * lam)) :=
          add_le_add hS0_le (mul_le_mul' h1 h_int_early)
      _ = ENNReal.ofReal C_early := by
          rw [one_mul, ← ENNReal.ofReal_add hC_MP.le (by positivity)]
  have h_int_late_2 : ∫⁻ t in Ioc (T / 2) T,
      eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) 2 volume ≤
      ENNReal.ofReal ((A_k / (2 * lam)) * Real.exp (-(2 * lam * (T / 2)))) := by
    have hmono : ∫⁻ t in Ioc (T / 2) T,
        eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) 2 volume ≤
        ∫⁻ t in Ioc (T / 2) T, ENNReal.ofReal (A_k * Real.exp (-(2 * lam * t))) := by
      refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
      exact (hg_bounds t (by linarith [ht.1])).2.1
    exact hmono.trans (lintegral_Ioc_exp_neg_le hA_k.le (by positivity) (by linarith))
  have h_int_late_top : ∫⁻ t in Ioc (T / 2) T,
      eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) ⊤ volume ≤
      ENNReal.ofReal ((A_k / (2 * lam)) * Real.exp (-(2 * lam * (T / 2)))) := by
    have hmono : ∫⁻ t in Ioc (T / 2) T,
        eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) ⊤ volume ≤
        ∫⁻ t in Ioc (T / 2) T, ENNReal.ofReal (A_k * Real.exp (-(2 * lam * t))) := by
      refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
      exact (hg_bounds t (by linarith [ht.1])).2.2
    exact hmono.trans (lintegral_Ioc_exp_neg_le hA_k.le (by positivity) (by linarith))
  obtain ⟨hDuh_2, hDuh_top⟩ := hDuh_j ν c hν hc1 tr htr T hT1
  obtain ⟨hexp_top, hexp_2⟩ := exp_neg_half_le_rpow (a := 2 * lam) (by positivity) hT1 j
  have heC_one : ENNReal.ofReal (eC ν c) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal heC_le1
  have h1T_pos : 0 ≤ 1 + T := by linarith
  have hC_early_pos : 0 ≤ C_early := by positivity
  have hC_late_pos : 0 ≤ C_late := by
    have : 0 < expAbsorbConst (2 * lam) j := expAbsorbConst_pos (by positivity) j
    positivity
  refine ⟨?_, ?_⟩
  · have hlate_le : ENNReal.ofReal (eC ν c) *
        ∫⁻ t in Ioc (T / 2) T,
          eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) 2 volume ≤
        ENNReal.ofReal (C_late * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) := by
      calc ENNReal.ofReal (eC ν c) *
              ∫⁻ t in Ioc (T / 2) T,
                eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) 2 volume
          ≤ 1 * ENNReal.ofReal ((A_k / (2 * lam)) * Real.exp (-(2 * lam * (T / 2)))) :=
            mul_le_mul' heC_one h_int_late_2
        _ ≤ ENNReal.ofReal (C_late * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) := by
            rw [one_mul]
            refine ENNReal.ofReal_le_ofReal ?_
            calc (A_k / (2 * lam)) * Real.exp (-(2 * lam * (T / 2)))
                ≤ (A_k / (2 * lam)) *
                    (expAbsorbConst (2 * lam) j * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) :=
                  mul_le_mul_of_nonneg_left hexp_2 (by positivity)
              _ = C_late * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4) := by ring
    refine hDuh_2.trans ?_
    calc ENNReal.ofReal (C_G * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) *
            (eLpNorm (overlapMeanStream tr 0) 1 volume +
              ENNReal.ofReal (eC ν c) *
                ∫⁻ t in Ioc 0 (T / 2), eLpNorm (overlapStressProfile tr t) 1 volume) +
            ENNReal.ofReal (eC ν c) *
              ∫⁻ t in Ioc (T / 2) T,
                eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) 2 volume
        ≤ ENNReal.ofReal (C_G * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) *
            ENNReal.ofReal C_early +
            ENNReal.ofReal (C_late * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) :=
          add_le_add (mul_le_mul_right hearly_le _) hlate_le
      _ = ENNReal.ofReal (C_long * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4)) := by
          have hp1 : 0 ≤ C_G * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4) := by positivity
          have hp2 : 0 ≤ C_late * (1 + T) ^ (-1 - (j : ℝ) / 2 + 1 / 4) := by positivity
          rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_add (mul_nonneg hp1 hC_early_pos) hp2]
          congr 1
          dsimp [C_long]
          ring
  · have hlate_le : ENNReal.ofReal (eC ν c) *
        ∫⁻ t in Ioc (T / 2) T,
          eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) ⊤ volume ≤
        ENNReal.ofReal (C_late * (1 + T) ^ (-1 - (j : ℝ) / 2)) := by
      calc ENNReal.ofReal (eC ν c) *
              ∫⁻ t in Ioc (T / 2) T,
                eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) ⊤ volume
          ≤ 1 * ENNReal.ofReal ((A_k / (2 * lam)) * Real.exp (-(2 * lam * (T / 2)))) :=
            mul_le_mul' heC_one h_int_late_top
        _ ≤ ENNReal.ofReal (C_late * (1 + T) ^ (-1 - (j : ℝ) / 2)) := by
            rw [one_mul]
            refine ENNReal.ofReal_le_ofReal ?_
            calc (A_k / (2 * lam)) * Real.exp (-(2 * lam * (T / 2)))
                ≤ (A_k / (2 * lam)) *
                    (expAbsorbConst (2 * lam) j * (1 + T) ^ (-1 - (j : ℝ) / 2)) :=
                  mul_le_mul_of_nonneg_left hexp_top (by positivity)
              _ = C_late * (1 + T) ^ (-1 - (j : ℝ) / 2) := by ring
    refine hDuh_top.trans ?_
    calc ENNReal.ofReal (C_G * (1 + T) ^ (-1 - (j : ℝ) / 2)) *
            (eLpNorm (overlapMeanStream tr 0) 1 volume +
              ENNReal.ofReal (eC ν c) *
                ∫⁻ t in Ioc 0 (T / 2), eLpNorm (overlapStressProfile tr t) 1 volume) +
            ENNReal.ofReal (eC ν c) *
              ∫⁻ t in Ioc (T / 2) T,
                eLpNorm (iteratedDeriv (j + 1) (overlapStressProfile tr t)) ⊤ volume
        ≤ ENNReal.ofReal (C_G * (1 + T) ^ (-1 - (j : ℝ) / 2)) *
            ENNReal.ofReal C_early +
            ENNReal.ofReal (C_late * (1 + T) ^ (-1 - (j : ℝ) / 2)) :=
          add_le_add (mul_le_mul_right hearly_le _) hlate_le
      _ = ENNReal.ofReal (C_long * (1 + T) ^ (-1 - (j : ℝ) / 2)) := by
          have hp1 : 0 ≤ C_G * (1 + T) ^ (-1 - (j : ℝ) / 2) := by positivity
          have hp2 : 0 ≤ C_late * (1 + T) ^ (-1 - (j : ℝ) / 2) := by positivity
          rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_add (mul_nonneg hp1 hC_early_pos) hp2]
          congr 1
          dsimp [C_long]
          ring

end PartI_T15

/-! ### 7. Conditional assembly `overlap_mean_decay_of` (`PartI:T15`) -/

/-- **Conditional assembly of `OverlapMeanDecay` (`PartI:T15`)** from `OverlapHighNormUniform`,
`OverlapFluctuationDecay`, `OverlapMeanPrimitive`, and `OverlapMeanDuhamelSplit`.
Composed by `PartI:T15` (`overlap_mean_decay` in `Short/PartI/Tasks/OverlapMeanDecay.lean`). -/
theorem overlap_mean_decay_of (hHN : OverlapHighNormUniform) (hFD : OverlapFluctuationDecay)
    (hMP : OverlapMeanPrimitive) (hDuh : OverlapMeanDuhamelSplit) :
    OverlapMeanDecay := by
  intro ρ hρ j
  obtain ⟨C_S, ν_S, hC_S, hν_S, hShort⟩ := PartI_T15.overlapMeanDecay_shortTime hHN ρ hρ j
  obtain ⟨C_L, ν_L, hC_L, hν_L, hLong⟩ :=
    PartI_T15.overlapMeanDecay_longTime hFD hMP hDuh ρ hρ j
  refine ⟨max C_S C_L, min (min ν_S ν_L) (1 / 2), lt_max_of_lt_left hC_S,
    lt_min (lt_min hν_S hν_L) (by norm_num), ?_⟩
  intro ν hν hν_le tr htr T hT
  have hν_S' : ν ≤ ν_S := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_L' : ν ≤ ν_L := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc1 : 1 < c := by
    unfold c trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  have hs : 0 ≤ B0146.overlapAge ν c + c ^ 2 * T / ν :=
    (overlapAge_add_pos hν hc1 hT).le
  have hb_cd : ContDiff ℝ ∞ (fun Y => hmean 1 (overlapField ν c tr.v T) Y 0) :=
    PartI_T15.contDiff_hmean_unit_fst (PartI_T15.contDiff_overlapField_slice tr hs)
  have h1T : 0 ≤ 1 + T := by linarith
  by_cases hT1 : T ≤ 1
  · obtain ⟨hl2, hsup⟩ := hShort ν hν hν_S' tr htr T hT hT1
    refine ⟨hb_cd, ?_, ?_⟩
    · exact hl2.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg h1T _)))
    · exact hsup.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg h1T _)))
  · have hT1' : 1 ≤ T := le_of_not_ge hT1
    obtain ⟨hl2, hsup⟩ := hLong ν hν hν_L' tr htr T hT1'
    refine ⟨hb_cd, ?_, ?_⟩
    · exact hl2.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg h1T _)))
    · exact hsup.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg h1T _)))

end UnforcedLeray.Short.PartI
