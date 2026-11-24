import UnforcedLeray.Short.PartI.Sub.PartI_T14
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanEnergy
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStreamSmooth
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Helpers for `PartI:T14/1` (`MeanStreamDiffDuhamelL1`)

Source of record: `the November 2 reference manuscript`, lines 398-410.

This module establishes:
1. Initial datum identification (`meanStream_zero_eq_vortexMeanStream`):
   `meanStream tr 0 η = vortexMeanStream ν c 0 η` for `c ≥ 1`.
2. Derivatives and homogeneous 1D heat equation for `vortexMeanStream` (`vortexMeanStream_heat_eq`),
   together with transverse decay and uniform bound of `∂_η (vortexMeanStream ν c r)`.
3. Increment of `meanStream tr · 0` from age `0` (`meanStreamIncrement_zero`) and joint continuity
   of `meanStream tr` on `Ici 0 ×ˢ univ` (`continuousOn_meanStream_Ici`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec width)

/-! ### 1. Initial datum: `meanStream tr 0 η = vortexMeanStream ν c 0 η` -/

private def tIoc (c : ℝ) (n : ℤ) : Set ℝ :=
  (fun w : ℝ => w + (n : ℝ) * c) ⁻¹' Ioc (-c / 2) (c / 2)

private theorem measurableSet_tIoc (c : ℝ) (n : ℤ) : MeasurableSet (tIoc c n) :=
  measurableSet_Ioc.preimage (measurable_id.add_const _)

private theorem pairwise_disjoint_tIoc {c : ℝ} (hc : 0 < c) :
    Pairwise (Function.onFun Disjoint (tIoc c)) := by
  intro m n hmn
  show Disjoint (tIoc c m) (tIoc c n)
  rw [Set.disjoint_left]
  intro w hm hn
  simp only [tIoc, mem_preimage] at hm hn
  obtain ⟨k, _, hk⟩ := existsUnique_add_zsmul_mem_Ioc hc w (-c / 2)
  have hlen : -c / 2 + c = c / 2 := by ring
  have h1 := hk m (by show w + m • c ∈ Ioc (-c / 2) (-c / 2 + c); rwa [zsmul_eq_mul, hlen])
  have h2 := hk n (by show w + n • c ∈ Ioc (-c / 2) (-c / 2 + c); rwa [zsmul_eq_mul, hlen])
  exact hmn (h1.trans h2.symm)

private theorem iUnion_tIoc {c : ℝ} (hc : 0 < c) : ⋃ n : ℤ, tIoc c n = univ := by
  refine eq_univ_of_forall fun w => mem_iUnion.2 ?_
  obtain ⟨k, hk, _⟩ := existsUnique_add_zsmul_mem_Ioc hc w (-c / 2)
  have hlen : -c / 2 + c = c / 2 := by ring
  refine ⟨k, ?_⟩
  simp only [tIoc, mem_preimage]
  rwa [zsmul_eq_mul, hlen] at hk

private theorem preimage_sub_tIoc (c : ℝ) (n : ℤ) :
    (fun q : ℝ => q - (n : ℝ) * c) ⁻¹' tIoc c n = Ioc (-c / 2) (c / 2) := by
  ext q
  simp [tIoc]

private theorem setIntegral_Ioc_translate (g : ℝ → ℝ) (c : ℝ) (n : ℤ) :
    ∫ q in Ioc (-c / 2) (c / 2), g (q - (n : ℝ) * c) = ∫ w in tIoc c n, g w := by
  have h := (measurePreserving_sub_right volume ((n : ℝ) * c)).setIntegral_preimage_emb
    (measurableEmbedding_subRight ((n : ℝ) * c)) g (tIoc c n)
  rwa [preimage_sub_tIoc] at h

private theorem setLIntegral_Ioc_translate (g : ℝ → ℝ≥0∞) (c : ℝ) (n : ℤ) :
    ∫⁻ q in Ioc (-c / 2) (c / 2), g (q - (n : ℝ) * c) = ∫⁻ w in tIoc c n, g w := by
  have h := (measurePreserving_sub_right volume ((n : ℝ) * c)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_subRight ((n : ℝ) * c)) g (tIoc c n)
  rwa [preimage_sub_tIoc] at h

private theorem integral_Ioc_tsum_translate {g : ℝ → ℝ} (hg : Integrable g volume)
    {c : ℝ} (hc : 0 < c) :
    ∫ q in Ioc (-c / 2) (c / 2), (∑' n : ℤ, g (q - (n : ℝ) * c)) = ∫ w : ℝ, g w := by
  have hmeas : ∀ n : ℤ, AEStronglyMeasurable (fun q : ℝ => g (q - (n : ℝ) * c))
      (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    fun n => (hg.comp_sub_right ((n : ℝ) * c)).aestronglyMeasurable.restrict
  have hlin : ∑' n : ℤ, ∫⁻ q in Ioc (-c / 2) (c / 2), ‖g (q - (n : ℝ) * c)‖ₑ =
      ∫⁻ w : ℝ, ‖g w‖ₑ := by
    simp_rw [setLIntegral_Ioc_translate (fun w => ‖g w‖ₑ) c]
    rw [← lintegral_iUnion (measurableSet_tIoc c) (pairwise_disjoint_tIoc hc),
      iUnion_tIoc hc, Measure.restrict_univ]
  rw [integral_tsum hmeas (by rw [hlin]; exact hg.2.ne)]
  simp_rw [setIntegral_Ioc_translate g c]
  rw [← integral_iUnion (measurableSet_tIoc c) (pairwise_disjoint_tIoc hc)
    (by rw [iUnion_tIoc hc]; exact hg.integrableOn), iUnion_tIoc hc, Measure.restrict_univ]

/-- At `s = 0` and `c ≥ 1`, the horizontal average `meanStream tr 0 η` of the initial stream
equals `vortexMeanStream ν c 0 η = -(8π c⁻¹) G_1(η)`. -/
theorem meanStream_zero_eq_vortexMeanStream {ν c : ℝ} (hc1 : 1 ≤ c)
    (tr : B0140.TrainSol ν c) (η : ℝ) :
    meanStream tr 0 η = vortexMeanStream ν c 0 η := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  unfold meanStream
  rw [tr.isTrain.stream_zero hc1]
  unfold hmean
  rw [smul_eq_mul]
  set g : ℝ → ℝ := fun q => Real.exp (-(q ^ 2) / 4)
  have hg_eq : g = fun q : ℝ => Real.exp (-(1 / 4 : ℝ) * q ^ 2) := by
    funext q; dsimp [g]; congr 1; ring
  have hg_int : Integrable g volume := by
    rw [hg_eq]
    exact integrable_exp_neg_mul_sq (by norm_num)
  have hg_val : ∫ w : ℝ, g w = Real.sqrt (4 * Real.pi) := by
    rw [hg_eq, integral_gaussian, show Real.pi / (1 / 4 : ℝ) = 4 * Real.pi by ring]
  have hfun : (fun q : ℝ => B0140.trainStream c (q, η)) =
      fun q : ℝ => (-2 * Real.exp (-(η ^ 2) / 4)) * ∑' n : ℤ, g (q - (n : ℝ) * c) := by
    funext q
    rw [B0140.trainStream_apply]
    have hsplit : ∀ n : ℤ, Real.exp (-((q - (n : ℝ) * c) ^ 2 + η ^ 2) / 4) =
        Real.exp (-(η ^ 2) / 4) * g (q - (n : ℝ) * c) := by
      intro n
      dsimp [g]
      rw [← Real.exp_add]
      congr 1; ring
    simp_rw [hsplit, tsum_mul_left]
    ring
  rw [hfun, integral_const_mul, integral_Ioc_tsum_translate hg_int hc0, hg_val]
  unfold vortexMeanStream heatKernel1 width
  simp only [mul_zero, add_zero, mul_one]
  have hsqrt_pos : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (4 * Real.pi) * Real.sqrt (4 * Real.pi) = 4 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  calc c⁻¹ * (-2 * Real.exp (-(η ^ 2) / 4) * Real.sqrt (4 * Real.pi))
      = -(2 * (Real.sqrt (4 * Real.pi) * Real.sqrt (4 * Real.pi)) * c⁻¹) *
          ((Real.sqrt (4 * Real.pi))⁻¹ * Real.exp (-(η ^ 2) / 4)) := by
        field_simp [hsqrt_pos.ne']
    _ = -(8 * Real.pi * c⁻¹) *
          ((Real.sqrt (4 * Real.pi))⁻¹ * Real.exp (-(η ^ 2) / 4)) := by
        rw [hsq]
        ring

/-! ### 2. Smoothness, derivatives, and 1D heat equation of `vortexMeanStream` -/

theorem hasDerivAt_heatKernel1_eta {a : ℝ} (ha : 0 < a) (η : ℝ) :
    HasDerivAt (heatKernel1 a) (-(η / (2 * a)) * heatKernel1 a η) η := by
  unfold heatKernel1
  have harg : HasDerivAt (fun x : ℝ => -(x ^ 2) / (4 * a)) (-(η / (2 * a))) η := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * η) η := by
      simpa using hasDerivAt_pow 2 η
    have h2 := (h1.neg).div_const (4 * a)
    refine h2.congr_deriv ?_
    field_simp [ha.ne']
    ring
  have hexp := harg.exp
  have hmul := hexp.const_mul (Real.sqrt (4 * Real.pi * a))⁻¹
  refine hmul.congr_deriv ?_
  ring

theorem deriv_heatKernel1_eta {a : ℝ} (ha : 0 < a) (η : ℝ) :
    deriv (heatKernel1 a) η = -(η / (2 * a)) * heatKernel1 a η :=
  (hasDerivAt_heatKernel1_eta ha η).deriv

theorem hasDerivAt_deriv_heatKernel1_eta {a : ℝ} (ha : 0 < a) (η : ℝ) :
    HasDerivAt (deriv (heatKernel1 a))
      (heatKernel1 a η * (η ^ 2 / (4 * a ^ 2) - 1 / (2 * a))) η := by
  have hfun : deriv (heatKernel1 a) = fun x : ℝ => (-(2 * a)⁻¹ * x) * heatKernel1 a x := by
    funext x
    rw [deriv_heatKernel1_eta ha x]
    ring
  rw [hfun]
  have hlin : HasDerivAt (fun x : ℝ => -(2 * a)⁻¹ * x) (-(2 * a)⁻¹ * 1) η :=
    (hasDerivAt_id η).const_mul (-(2 * a)⁻¹)
  have hprod := hlin.mul (hasDerivAt_heatKernel1_eta ha η)
  refine hprod.congr_deriv ?_
  field_simp [ha.ne']
  ring

theorem deriv_deriv_heatKernel1_eta {a : ℝ} (ha : 0 < a) (η : ℝ) :
    deriv (deriv (heatKernel1 a)) η =
      heatKernel1 a η * (η ^ 2 / (4 * a ^ 2) - 1 / (2 * a)) :=
  (hasDerivAt_deriv_heatKernel1_eta ha η).deriv

theorem hasDerivAt_heatKernel1_time {a : ℝ} (ha : 0 < a) (η : ℝ) :
    HasDerivAt (fun t : ℝ => heatKernel1 t η)
      (heatKernel1 a η * (η ^ 2 / (4 * a ^ 2) - 1 / (2 * a))) a := by
  unfold heatKernel1
  have harg : HasDerivAt (fun t : ℝ => 4 * Real.pi * t) (4 * Real.pi) a := by
    simpa using (hasDerivAt_id a).const_mul (4 * Real.pi)
  have hargPos : 0 < 4 * Real.pi * a := by positivity
  have hsqrt := (Real.hasDerivAt_sqrt hargPos.ne').comp a harg
  have hsqrt0 : Real.sqrt (4 * Real.pi * a) ≠ 0 := by positivity
  have hinv := hsqrt.inv hsqrt0
  have hsq : (Real.sqrt (4 * Real.pi * a)) ^ 2 = 4 * Real.pi * a :=
    Real.sq_sqrt hargPos.le
  have hnorm : HasDerivAt (fun t : ℝ => (Real.sqrt (4 * Real.pi * t))⁻¹)
      ((Real.sqrt (4 * Real.pi * a))⁻¹ * (-(1 / (2 * a)))) a := by
    refine hinv.congr_deriv ?_
    dsimp only [Function.comp_apply]
    rw [hsq]
    field_simp [hsqrt0, ha.ne']
  have hexpArg : HasDerivAt (fun t : ℝ => -(η ^ 2) / (4 * t)) (η ^ 2 / (4 * a ^ 2)) a := by
    have hinv' : HasDerivAt (fun t : ℝ => t⁻¹) (-(a ^ 2)⁻¹) a := hasDerivAt_inv ha.ne'
    have hmul := hinv'.const_mul (-(η ^ 2 / 4))
    have hfun : (fun t : ℝ => -(η ^ 2 / 4) * t⁻¹) = fun t : ℝ => -(η ^ 2) / (4 * t) := by
      funext t; ring
    rw [← hfun]
    refine hmul.congr_deriv ?_
    field_simp [ha.ne']
  have hprod := hnorm.mul hexpArg.exp
  refine hprod.congr_deriv ?_
  ring

/-- `vortexMeanStream ν c` solves the homogeneous 1D heat equation `(∂_r - ν ∂_η²) V = 0`
for `ν > 0` and `r ≥ 0`. -/
theorem vortexMeanStream_heat_eq {ν c r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (η : ℝ) :
    deriv (fun r' => vortexMeanStream ν c r' η) r -
      ν * deriv (deriv (fun e => vortexMeanStream ν c r e)) η = 0 := by
  have ha : 0 < width ν r := by
    unfold width
    nlinarith
  have hw : HasDerivAt (width ν) ν r := by
    unfold width
    simpa using ((hasDerivAt_id r).const_mul ν).const_add 1
  have htime : HasDerivAt (fun r' => vortexMeanStream ν c r' η)
      (-(8 * Real.pi * c⁻¹) *
        (heatKernel1 (width ν r) η * (η ^ 2 / (4 * width ν r ^ 2) - 1 / (2 * width ν r)) * ν)) r := by
    unfold vortexMeanStream
    exact ((hasDerivAt_heatKernel1_time ha η).comp r hw).const_mul (-(8 * Real.pi * c⁻¹))
  have hd1 : deriv (fun e => vortexMeanStream ν c r e) =
      fun e => -(8 * Real.pi * c⁻¹) * deriv (heatKernel1 (width ν r)) e := by
    funext e
    unfold vortexMeanStream
    exact deriv_const_mul (-(8 * Real.pi * c⁻¹)) (hasDerivAt_heatKernel1_eta ha e).differentiableAt
  have hd2 : deriv (deriv (fun e => vortexMeanStream ν c r e)) η =
      -(8 * Real.pi * c⁻¹) *
        (heatKernel1 (width ν r) η * (η ^ 2 / (4 * width ν r ^ 2) - 1 / (2 * width ν r))) := by
    rw [hd1]
    exact ((hasDerivAt_deriv_heatKernel1_eta ha η).const_mul (-(8 * Real.pi * c⁻¹))).deriv
  rw [htime.deriv, hd2]
  ring

/-- Joint smoothness of `vortexMeanStream ν c` on `Ici 0 ×ˢ univ` for `ν > 0`. -/
theorem contDiffOn_vortexMeanStream {ν c : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => vortexMeanStream ν c x.1 x.2) (Ici 0 ×ˢ univ) := by
  have hw_pos : ∀ x ∈ Ici (0 : ℝ) ×ˢ (univ : Set ℝ), 0 < 4 * Real.pi * width ν x.1 := by
    intro x hx
    have hx1 : 0 ≤ x.1 := hx.1
    have ha : 0 < width ν x.1 := by unfold width; nlinarith
    positivity
  have hw_ne : ∀ x ∈ Ici (0 : ℝ) ×ˢ (univ : Set ℝ), width ν x.1 ≠ 0 := by
    intro x hx
    have hx1 : 0 ≤ x.1 := hx.1
    have ha : 0 < width ν x.1 := by unfold width; nlinarith
    exact ha.ne'
  have hsqrt_ne : ∀ x ∈ Ici (0 : ℝ) ×ˢ (univ : Set ℝ),
      Real.sqrt (4 * Real.pi * width ν x.1) ≠ 0 :=
    fun x hx => (Real.sqrt_pos.2 (hw_pos x hx)).ne'
  have hwidth : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => width ν x.1) (Ici 0 ×ˢ univ) :=
    contDiffOn_const.add (contDiffOn_const.mul contDiffOn_fst)
  have h4pi : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => 4 * Real.pi * width ν x.1) (Ici 0 ×ˢ univ) :=
    contDiffOn_const.mul hwidth
  have hsqrt : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => Real.sqrt (4 * Real.pi * width ν x.1))
      (Ici 0 ×ˢ univ) :=
    fun x hx => (Real.contDiffAt_sqrt (hw_pos x hx).ne').comp_contDiffWithinAt x (h4pi x hx)
  have hinv : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => (Real.sqrt (4 * Real.pi * width ν x.1))⁻¹)
      (Ici 0 ×ˢ univ) :=
    hsqrt.inv hsqrt_ne
  have hexp_arg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => -(x.2 ^ 2) / (4 * width ν x.1))
      (Ici 0 ×ˢ univ) :=
    (contDiffOn_snd.pow 2).neg.div (contDiffOn_const.mul hwidth)
      (fun x hx => mul_ne_zero (by norm_num) (hw_ne x hx))
  have hexp : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => Real.exp (-(x.2 ^ 2) / (4 * width ν x.1)))
      (Ici 0 ×ˢ univ) :=
    Real.contDiff_exp.comp_contDiffOn hexp_arg
  exact contDiffOn_const.mul (hinv.mul hexp)

/-- Transverse decay `∂_η (vortexMeanStream ν c r) R → 0` as `R → +∞` for `ν > 0, r ≥ 0`. -/
theorem tendsto_deriv_vortexMeanStream_atTop {ν c r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    Tendsto (fun R : ℝ => deriv (vortexMeanStream ν c r) R) atTop (𝓝 0) := by
  have ha : 0 < width ν r := by unfold width; nlinarith
  set C : ℝ := |8 * Real.pi * c⁻¹| * (Real.sqrt (4 * Real.pi * width ν r))⁻¹ * 2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ( (eventually_gt_atTop (0 : ℝ)).mono fun R hR => ?_ )
    (by simpa [mul_zero] using tendsto_inv_atTop_zero.const_mul C)
  rw [Real.norm_eq_abs]
  have hderiv : deriv (vortexMeanStream ν c r) R =
      (8 * Real.pi * c⁻¹) * (Real.sqrt (4 * Real.pi * width ν r))⁻¹ *
        ((R / (2 * width ν r)) * Real.exp (-(R ^ 2) / (4 * width ν r))) := by
    unfold vortexMeanStream
    rw [((hasDerivAt_heatKernel1_eta ha R).const_mul (-(8 * Real.pi * c⁻¹))).deriv]
    unfold heatKernel1
    ring
  have hsq_exp : (R ^ 2 / (4 * width ν r)) * Real.exp (-(R ^ 2) / (4 * width ν r)) ≤ 1 := by
    have h1 : R ^ 2 / (4 * width ν r) ≤ Real.exp (R ^ 2 / (4 * width ν r)) := by
      linarith [Real.add_one_le_exp (R ^ 2 / (4 * width ν r))]
    calc (R ^ 2 / (4 * width ν r)) * Real.exp (-(R ^ 2) / (4 * width ν r))
        ≤ Real.exp (R ^ 2 / (4 * width ν r)) * Real.exp (-(R ^ 2) / (4 * width ν r)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := by
          rw [← Real.exp_add,
            show R ^ 2 / (4 * width ν r) + -(R ^ 2) / (4 * width ν r) = 0 by ring,
            Real.exp_zero]
  have hR_exp : (R / (2 * width ν r)) * Real.exp (-(R ^ 2) / (4 * width ν r)) ≤ 2 * R⁻¹ := by
    have hid : (R / (2 * width ν r)) * Real.exp (-(R ^ 2) / (4 * width ν r)) =
        (2 * R⁻¹) * ((R ^ 2 / (4 * width ν r)) * Real.exp (-(R ^ 2) / (4 * width ν r))) := by
      field_simp [ha.ne', hR.ne']
      ring
    rw [hid]
    exact mul_le_of_le_one_right (by positivity) hsq_exp
  have hpos1 : 0 ≤ (Real.sqrt (4 * Real.pi * width ν r))⁻¹ := by positivity
  have hpos2 : 0 ≤ (R / (2 * width ν r)) * Real.exp (-(R ^ 2) / (4 * width ν r)) := by positivity
  rw [hderiv, abs_mul, abs_mul, abs_of_nonneg hpos1, abs_of_nonneg hpos2]
  calc |8 * Real.pi * c⁻¹| * (Real.sqrt (4 * Real.pi * width ν r))⁻¹ *
        (R / (2 * width ν r) * Real.exp (-(R ^ 2) / (4 * width ν r)))
      ≤ |8 * Real.pi * c⁻¹| * (Real.sqrt (4 * Real.pi * width ν r))⁻¹ * (2 * R⁻¹) :=
        mul_le_mul_of_nonneg_left hR_exp (by positivity)
    _ = C * R⁻¹ := by unfold C; ring

/-- Uniform bound `|∂_η (vortexMeanStream ν c r) R| ≤ 8π c⁻¹` for all `ν > 0, c > 0, r ≥ 0, R : ℝ`. -/
theorem abs_deriv_vortexMeanStream_le {ν c r : ℝ} (hν : 0 < ν) (hc : 0 < c) (hr : 0 ≤ r)
    (R : ℝ) :
    |deriv (vortexMeanStream ν c r) R| ≤ 8 * Real.pi * c⁻¹ := by
  set a := width ν r
  have ha1 : 1 ≤ a := by unfold a width; nlinarith
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have ha2 : 0 < 2 * a := by linarith
  have hderiv : deriv (vortexMeanStream ν c r) R =
      (8 * Real.pi * c⁻¹) * ((Real.sqrt (4 * Real.pi * a))⁻¹ *
        ((R / (2 * a)) * Real.exp (-(R ^ 2) / (4 * a)))) := by
    unfold vortexMeanStream
    rw [((hasDerivAt_heatKernel1_eta ha0 R).const_mul (-(8 * Real.pi * c⁻¹))).deriv]
    unfold heatKernel1
    ring
  rw [hderiv, abs_mul, abs_of_pos (by positivity), abs_mul, abs_of_pos (by positivity),
    abs_mul, Real.abs_exp, abs_div, abs_of_pos ha2]
  have hsqrt_ge1 : 1 ≤ Real.sqrt (4 * Real.pi * a) := by
    rw [Real.le_sqrt zero_le_one (by positivity)]
    have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  have hinv_le1 : (Real.sqrt (4 * Real.pi * a))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt_ge1
  have hR_le : |R| / (2 * a) ≤ Real.exp (R ^ 2 / (4 * a)) := by
    have hsq : 0 ≤ (|R| / 2 - 1) ^ 2 := sq_nonneg _
    have h1 : |R| ≤ R ^ 2 / 4 + 1 := by
      have : (|R| / 2 - 1) ^ 2 = R ^ 2 / 4 - |R| + 1 := by
        rw [sub_sq, div_pow, sq_abs]
        ring
      linarith
    have h2 : |R| / (2 * a) ≤ R ^ 2 / (4 * a) + 1 := by
      rw [div_le_iff₀ ha2]
      calc |R| ≤ R ^ 2 / 4 + 1 := h1
        _ ≤ R ^ 2 / 2 + 2 * a := by nlinarith [sq_nonneg R]
        _ = (R ^ 2 / (4 * a) + 1) * (2 * a) := by field_simp [ha0.ne']; ring
    exact h2.trans (Real.add_one_le_exp (R ^ 2 / (4 * a)))
  have hexp_le1 : |R| / (2 * a) * Real.exp (-(R ^ 2) / (4 * a)) ≤ 1 := by
    calc |R| / (2 * a) * Real.exp (-(R ^ 2) / (4 * a))
        ≤ Real.exp (R ^ 2 / (4 * a)) * Real.exp (-(R ^ 2) / (4 * a)) :=
          mul_le_mul_of_nonneg_right hR_le (Real.exp_pos _).le
      _ = 1 := by
          rw [← Real.exp_add, show R ^ 2 / (4 * a) + -(R ^ 2) / (4 * a) = 0 by ring,
            Real.exp_zero]
  calc 8 * Real.pi * c⁻¹ *
        ((Real.sqrt (4 * Real.pi * a))⁻¹ * (|R| / (2 * a) * Real.exp (-(R ^ 2) / (4 * a))))
      ≤ 8 * Real.pi * c⁻¹ * (1 * 1) := by
        gcongr
    _ = 8 * Real.pi * c⁻¹ := by ring

/-! ### 3. Increment of `meanStream tr · 0` from age `0` and continuity on `Ici 0 ×ˢ univ` -/

private theorem continuousOn_integral_meanVel1 {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (R : ℝ) :
    ContinuousOn (fun r : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr r t) (Ici 0) := by
  set v0_ext : ℝ → Plane → ℝ := fun r z => tr.v (max r 0) z 0
  have hv_cont : Continuous (fun p : ℝ × Plane => v0_ext p.1 p.2) := by
    have hsm : ContinuousOn (fun p : ℝ × Plane => tr.v p.1 p.2 0) (Ici 0 ×ˢ univ) :=
      ((PiLp.continuous_apply 2 _ 0).comp_continuousOn tr.isTrain.smooth_v.continuousOn)
    have hmap : Continuous (fun p : ℝ × Plane => ((max p.1 0, p.2) : ℝ × Plane)) :=
      (continuous_fst.max continuous_const).prodMk continuous_snd
    exact hsm.comp_continuous hmap (fun p => ⟨mem_Ici.2 (le_max_right p.1 0), mem_univ _⟩)
  have hu_cont : Continuous (Function.uncurry (fun r t : ℝ => hmean c (v0_ext r) t)) := by
    have hle : -c / 2 ≤ c / 2 := by linarith
    have hfun : Function.uncurry (fun r t : ℝ => hmean c (v0_ext r) t) =
        fun p : ℝ × ℝ => c⁻¹ * ∫ q in (-c / 2)..(c / 2), v0_ext p.1 (q, p.2) := by
      funext p
      simp only [hmean, smul_eq_mul, intervalIntegral.integral_of_le hle]
      rfl
    rw [hfun]
    have hcont_q : Continuous (Function.uncurry (fun (p : ℝ × ℝ) (q : ℝ) => v0_ext p.1 (q, p.2))) :=
      hv_cont.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))
    exact continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hcont_q (-c / 2) (c / 2))
  have hI_cont : Continuous (fun r : ℝ => ∫ t in (0 : ℝ)..R, hmean c (v0_ext r) t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hu_cont 0 R
  refine hI_cont.continuousOn.congr fun r hr => ?_
  have hmax : max r 0 = r := max_eq_left hr
  simp only [meanVel1, v0_ext, hmax]

/-- Increment of `meanStream tr · 0` from age `0` to `s > 0`. -/
theorem meanStreamIncrement_zero {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) {s : ℝ} (hs : 0 < s) :
    meanStream tr s 0 - meanStream tr 0 0 =
      ∫ r in (0 : ℝ)..s, (meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0) := by
  obtain ⟨M0, hM0⟩ := hb.sup_bound hs.le
  obtain ⟨M1, hM1⟩ := hb.deriv_bound hs.le 1
  set Bd : ℝ := ν * (2 * M1) + 2 * (M0 * M0) with hBd
  have hDbd : ∀ R : ℝ, ∀ r ∈ Ioc 0 s,
      |ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) -
        (meanStress tr r R - meanStress tr r 0)| ≤ Bd := by
    intro R r hr
    have hr0 : 0 ≤ r := hr.1.le
    have hrS : r ≤ s := hr.2
    have hM1r : ∀ z : Plane, ‖iteratedFDeriv ℝ 1 (tr.v r) z‖ ≤ M1 :=
      fun z => hM1 r ⟨hr0, hrS⟩ z
    have hM0r : ∀ z : Plane, ‖tr.v r z‖ ≤ M0 := fun z => hM0 r ⟨hr0, hrS⟩ z
    have hu1 := msi_deriv_meanVel1_bound hc tr hr0 hM1r R
    have hu0 := msi_deriv_meanVel1_bound hc tr hr0 hM1r 0
    have hg1 := msi_meanStress_bound hc tr hM0r R
    have hg0 := msi_meanStress_bound hc tr hM0r 0
    have hX : |deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0| ≤ 2 * M1 := by
      rw [abs_le]
      constructor <;> linarith [(abs_le.1 hu1).1, (abs_le.1 hu1).2,
        (abs_le.1 hu0).1, (abs_le.1 hu0).2]
    have hY : |meanStress tr r R - meanStress tr r 0| ≤ 2 * (M0 * M0) := by
      rw [abs_le]
      constructor <;> linarith [(abs_le.1 hg1).1, (abs_le.1 hg1).2,
        (abs_le.1 hg0).1, (abs_le.1 hg0).2]
    have hX' := abs_le.1 hX
    have hY' := abs_le.1 hY
    have hνX1 : ν * (-(2 * M1)) ≤ ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) :=
      mul_le_mul_of_nonneg_left hX'.1 hν.le
    have hνX2 : ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) ≤ ν * (2 * M1) :=
      mul_le_mul_of_nonneg_left hX'.2 hν.le
    rw [abs_le, hBd]
    constructor <;> linarith [hY'.1, hY'.2]
  have hDeriv : ∀ R : ℝ, ∀ r : ℝ, 0 < r → HasDerivAt
      (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t)
      (ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) -
        (meanStress tr r R - meanStress tr r 0)) r :=
    fun R r hr => meanVelIntegralDeriv ν c hν hc tr r hr R
  have hGeq : ∀ R : ℝ, ∀ r : ℝ, 0 < r →
      deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r =
        ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) -
          (meanStress tr r R - meanStress tr r 0) :=
    fun R r hr => (hDeriv R r hr).deriv
  have hFTC : ∀ R : ℝ, (∫ r in (0 : ℝ)..s,
      deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r) =
        (∫ t in (0 : ℝ)..R, meanVel1 tr s t) - (∫ t in (0 : ℝ)..R, meanVel1 tr 0 t) := by
    intro R
    have hint : IntervalIntegrable
        (fun r => deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r) volume 0 s := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le]
      refine Measure.integrableOn_of_bounded (M := Bd) measure_Ioc_lt_top.ne
        (measurable_deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t)).aestronglyMeasurable
        ?_
      refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
      rw [Real.norm_eq_abs, hGeq R x hx.1]
      exact hDbd R x hx
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs.le
      ((continuousOn_integral_meanVel1 hc tr R).mono Icc_subset_Ici_self)
      (fun x hx => ((hDeriv R x hx.1).congr_deriv (hGeq R x hx.1).symm).hasDerivWithinAt)
      hint
  have hlimD : ∀ r : ℝ, 0 < r → Tendsto
      (fun R : ℝ => ν * (deriv (meanVel1 tr r) R - deriv (meanVel1 tr r) 0) -
        (meanStress tr r R - meanStress tr r 0)) atTop
      (𝓝 (meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0)) := by
    intro r hr
    have h1 := (bucMeanVelDecay ν c hν hc tr hb r hr.le).2
    have h2 := bucMeanStressDecay ν c hν hc tr hb r hr.le
    have h := ((h1.sub_const (deriv (meanVel1 tr r) 0)).const_mul ν).sub
      (h2.sub_const (meanStress tr r 0))
    have e : ν * (0 - deriv (meanVel1 tr r) 0) - (0 - meanStress tr r 0) =
        meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0 := by ring
    rw [e] at h
    exact h
  have hDCT : Tendsto (fun R : ℝ => ∫ r in (0 : ℝ)..s,
      deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r) atTop
      (𝓝 (∫ r in (0 : ℝ)..s, (meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => Bd)
      (Eventually.of_forall fun R =>
        (measurable_deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t)).aestronglyMeasurable)
      (Eventually.of_forall fun R => ae_of_all _ fun x hx => ?_)
      intervalIntegrable_const (ae_of_all _ fun x hx => ?_)
    · rw [uIoc_of_le hs.le] at hx
      rw [Real.norm_eq_abs, hGeq R x hx.1]
      exact hDbd R x hx
    · rw [uIoc_of_le hs.le] at hx
      exact Tendsto.congr (fun R => (hGeq R x hx.1).symm) (hlimD x hx.1)
  have hconst : ∀ R : ℝ, (∫ r in (0 : ℝ)..s,
      deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r) +
        (meanStream tr s R - meanStream tr 0 R) =
        meanStream tr s 0 - meanStream tr 0 0 := by
    intro R
    rw [hFTC R]
    have e2 := msi_stream_split tr hs.le R
    have e1 := msi_stream_split tr le_rfl R
    linarith
  have hlim2 : Tendsto (fun R : ℝ => (∫ r in (0 : ℝ)..s,
      deriv (fun x : ℝ => ∫ t in (0 : ℝ)..R, meanVel1 tr x t) r) +
        (meanStream tr s R - meanStream tr 0 R)) atTop
      (𝓝 ((∫ r in (0 : ℝ)..s, (meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0)) + (0 - 0))) :=
    hDCT.add ((meanStreamDecay ν c hν hc tr s hs.le).sub
      (meanStreamDecay ν c hν hc tr 0 le_rfl))
  have h3 : Tendsto (fun _ : ℝ => meanStream tr s 0 - meanStream tr 0 0) atTop
      (𝓝 ((∫ r in (0 : ℝ)..s, (meanStress tr r 0 - ν * deriv (meanVel1 tr r) 0)) + (0 - 0))) :=
    Tendsto.congr hconst hlim2
  have key := tendsto_nhds_unique tendsto_const_nhds h3
  linarith

/-- Joint continuity of `meanStream tr` on `Ici 0 ×ˢ univ`. -/
theorem continuousOn_meanStream_Ici {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hb : IsBUCTrain tr) :
    ContinuousOn (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ici 0 ×ˢ univ) := by
  -- 1. Continuity of `r ↦ meanStream tr r 0` on `Ici 0`
  have hS0_cont : ContinuousOn (fun r : ℝ => meanStream tr r 0) (Ici 0) := by
    intro r hr
    rcases eq_or_lt_of_le (mem_Ici.1 hr) with rfl | hr_pos
    · -- At `r = 0`: bound `|meanStream tr r' 0 - meanStream tr 0 0| ≤ Bd * r'` on `[0, 1]`
      obtain ⟨M0, hM0⟩ := hb.sup_bound zero_le_one
      obtain ⟨M1, hM1⟩ := hb.deriv_bound zero_le_one 1
      set Bd : ℝ := M0 * M0 + ν * M1
      have hBd_nn : 0 ≤ Bd := by
        have hM0_nn : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0 ⟨le_rfl, zero_le_one⟩ 0)
        have hM1_nn : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 ⟨le_rfl, zero_le_one⟩ 0)
        positivity
      have hbound : ∀ r' ∈ Ico (0 : ℝ) 1,
          ‖meanStream tr r' 0 - meanStream tr 0 0‖ ≤ Bd * r' := by
        intro r' hr'
        rcases eq_or_lt_of_le hr'.1 with rfl | hr'_pos
        · simp
        · rw [meanStreamIncrement_zero hν hc tr hb hr'_pos,
            intervalIntegral.integral_of_le hr'_pos.le]
          have hpt : ∀ t ∈ Ioc 0 r',
              ‖meanStress tr t 0 - ν * deriv (meanVel1 tr t) 0‖ ≤ Bd := by
            intro t ht
            have ht0 : 0 ≤ t := ht.1.le
            have ht1 : t ≤ 1 := ht.2.trans hr'.2.le
            have hg0 := msi_meanStress_bound hc tr (fun z => hM0 t ⟨ht0, ht1⟩ z) 0
            have hu0 := msi_deriv_meanVel1_bound hc tr ht0 (fun z => hM1 t ⟨ht0, ht1⟩ z) 0
            rw [Real.norm_eq_abs, abs_le]
            constructor <;> nlinarith [(abs_le.1 hg0).1, (abs_le.1 hg0).2,
              (abs_le.1 hu0).1, (abs_le.1 hu0).2]
          have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 r')
            measure_Ioc_lt_top hpt
          rwa [Real.volume_real_Ioc_of_le hr'_pos.le, sub_zero] at h
      rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      refine ⟨min 1 (ε / (Bd + 1)), lt_min one_pos (div_pos hε (by positivity)), ?_⟩
      intro r' hr' hdist
      have hr'0 : 0 ≤ r' := hr'
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hr'0] at hdist
      have hr'1 : r' < 1 := hdist.trans_le (min_le_left _ _)
      have hr'2 : r' < ε / (Bd + 1) := hdist.trans_le (min_le_right _ _)
      rw [dist_eq_norm]
      calc ‖meanStream tr r' 0 - meanStream tr 0 0‖
          ≤ Bd * r' := hbound r' ⟨hr'0, hr'1⟩
        _ ≤ (Bd + 1) * r' := by nlinarith
        _ < (Bd + 1) * (ε / (Bd + 1)) := mul_lt_mul_of_pos_left hr'2 (by positivity)
        _ = ε := mul_div_cancel₀ ε (by positivity)
    · -- At `r > 0`: `meanStream` is smooth on `Ioi 0 ×ˢ univ`
      have hS := (trainMeanEquations_proof ν c hν hc tr hb).1
      have hslice : ContinuousOn (fun r' : ℝ => meanStream tr r' 0) (Ioi 0) :=
        hS.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
          (fun r' hr' => ⟨hr', mem_univ _⟩)
      exact (hslice.continuousAt (Ioi_mem_nhds hr_pos)).continuousWithinAt
  -- 2. Parametric integral representation `S(r, η) = S(r, 0) - η ∫₀¹ u(r, η τ) dτ`
  set v0_ext : ℝ → Plane → ℝ := fun r z => tr.v (max r 0) z 0
  have hv_cont : Continuous (fun p : ℝ × Plane => v0_ext p.1 p.2) := by
    have hsm : ContinuousOn (fun p : ℝ × Plane => tr.v p.1 p.2 0) (Ici 0 ×ˢ univ) :=
      ((PiLp.continuous_apply 2 _ 0).comp_continuousOn tr.isTrain.smooth_v.continuousOn)
    have hmap : Continuous (fun p : ℝ × Plane => ((max p.1 0, p.2) : ℝ × Plane)) :=
      (continuous_fst.max continuous_const).prodMk continuous_snd
    exact hsm.comp_continuous hmap (fun p => ⟨mem_Ici.2 (le_max_right p.1 0), mem_univ _⟩)
  have hu_cont : Continuous (Function.uncurry (fun r t : ℝ => hmean c (v0_ext r) t)) := by
    have hle : -c / 2 ≤ c / 2 := by linarith
    have hfun : Function.uncurry (fun r t : ℝ => hmean c (v0_ext r) t) =
        fun p : ℝ × ℝ => c⁻¹ * ∫ q in (-c / 2)..(c / 2), v0_ext p.1 (q, p.2) := by
      funext p
      simp only [hmean, smul_eq_mul, intervalIntegral.integral_of_le hle]
      rfl
    rw [hfun]
    have hcont_q : Continuous (Function.uncurry (fun (p : ℝ × ℝ) (q : ℝ) => v0_ext p.1 (q, p.2))) :=
      hv_cont.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))
    exact continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hcont_q (-c / 2) (c / 2))
  have hcomp_cont : Continuous (Function.uncurry
      (fun (x : ℝ × ℝ) (τ : ℝ) => hmean c (v0_ext x.1) (x.2 * τ))) :=
    hu_cont.comp (continuous_fst.fst.prodMk (continuous_fst.snd.mul continuous_snd))
  have hK_cont : Continuous (fun x : ℝ × ℝ =>
      x.2 * ∫ τ in (0 : ℝ)..1, hmean c (v0_ext x.1) (x.2 * τ)) :=
    continuous_snd.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcomp_cont 0 1)
  have hsum : ContinuousOn
      (fun x : ℝ × ℝ => meanStream tr x.1 0 -
        x.2 * ∫ τ in (0 : ℝ)..1, hmean c (v0_ext x.1) (x.2 * τ))
      (Ici 0 ×ˢ univ) :=
    (hS0_cont.comp continuousOn_fst (fun x hx => hx.1)).sub hK_cont.continuousOn
  refine hsum.congr fun x hx => ?_
  have hx1 : 0 ≤ x.1 := hx.1
  have hmax : max x.1 0 = x.1 := max_eq_left hx1
  have hsplit := msi_stream_split tr hx1 x.2
  have hscale : x.2 * ∫ τ in (0 : ℝ)..1, meanVel1 tr x.1 (x.2 * τ) =
      ∫ t in (0 : ℝ)..x.2, meanVel1 tr x.1 t := by
    have h := intervalIntegral.smul_integral_comp_mul_left (meanVel1 tr x.1) x.2 (a := 0) (b := 1)
    simp only [mul_zero, mul_one, smul_eq_mul] at h
    exact h
  simp only [v0_ext, hmax]
  change meanStream tr x.1 x.2 =
    meanStream tr x.1 0 - x.2 * ∫ τ in (0 : ℝ)..1, meanVel1 tr x.1 (x.2 * τ)
  rw [hscale]
  linarith

end UnforcedLeray.Short.PartI
