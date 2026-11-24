import UnforcedLeray.Short.PartIIb.Sub.PartIIb_B3_2
import UnforcedLeray.Short.PartIIb.Sub.B3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2
import UnforcedLeray.Short.PartIIb.Compose
import UnforcedLeray.Short.PartIIb.Tasks.DatumFacts
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderUL4
import UnforcedLeray.Lib.HeatR3.SubSelf
import UnforcedLeray.Cons.L2.BackgroundConcrete.HeatL4
import UnforcedLeray.Loc.L02FreeEvolution
import UnforcedLeray.Loc.L03Evolution.Free
import UnforcedLeray.Loc.L10Nonlinear.Pairing
import UnforcedLeray.Loc.L10Nonlinear.WeakProduct
import UnforcedLeray.Infra.HalfLineGreen.Continuity

/-!
# `PartII-b:B3/2/1` support and leaf decomposition (`Sub/PartII-b_B3_2_1.lean`, SP 2584-2628)

Source of record: `the November 2 reference manuscript`, lines 2584-2628:
1. Gaussian-increment decay `|D^j(e^{νΔ}a_τ - a_τ)(y)| ≤ C|y|^{-3-j}` (`|y| ≥ 1`, `j ≤ 2`, SP 2588)
   and raw-heat comparison `V - H_a ∈ C_per H^k ∩ X_p` (`short-bg:raw-heat`, SP 2586-2603);
2. Stress tensor columns `𝕋 = U ⊗ U ∈ C_per H²` from `D^jU ∈ C_per L⁴` (`j ≤ 2`, SP 2607-2612),
   with `-𝐏 div 𝕋 = -𝐏(U·∇U)` for solenoidal `U`;
3. Free similarity Duhamel integral `Q(τ) = -∫₀^∞ S₀(t) 𝐏 div 𝕋(τ - t) dt` in `H²(ℝ³)`, its
   short-time `t^{-1/2}` and long-time exponential majorants, continuity `Q : ℝ → H²`, and
   identification with `U - H_a` via free uniqueness in `Y_p` (`p = 11/4`, SP 2613-2629), upgraded
   from almost every phase to every phase `τ : ℝ` by `L⁴` slice continuity.

## Proved outright here (zero `sorry`)

* `exists_invDistClass4_of_isB3Datum` and `heatProfile_sub_scaledDatum_decay`: order-4 inverse
  distance class of any `IsB3Datum` and the uniform-in-`τ` Gaussian-increment bound of SP 2588;
* `stressCol`, `stressColH2`, `norm_stressColH2_le`, `sum_dpart_eq_zero_of_isSolenoidal`, and
  `Xclass_minusLerayDivX_stressColH2`: `H²(ℝ³)` construction and uniform norm bound of the stress
  columns `(U_m U)_{m < 3}` from `UL4` (`j ≤ 2`), and the solenoidal identity
  `-𝐏 div(U ⊗ U) = -𝐏(U·∇U)`;
* `minusLerayDivXCLM`, `norm_S0Z_le_large`, `freeDuhamelKernel`, `freeStressDuhamelH2`,
  `continuous_freeStressDuhamelH2`, and `value_freeStressDuhamelH2`: full `H²(ℝ³)` convergence,
  continuity on `ℝ`, and `L²(ℝ³)` Bochner evaluation of `-∫₀^∞ S₀(t) 𝐏 div 𝕋(τ - t) dt`;
* `remainder_eLpNorm_q0E_le`, `exists_continuous_bgField_L4`, and `ae_eq_every_phase_of_aem_phase`:
  uniform `L^{11/4}` bound on `U - H_a = (V - H_a) + w`, continuous `L⁴` path of `bgField p z`, and
  upgrade of `(Q τ).value =ᵐ U τ - H_a τ` from almost every `τ` to every `τ : ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0412 UnforcedLeray.Blueprint
  UnforcedLeray.SobolevGraph

namespace B3RemH2Sub

local instance fact_one_le_four_rem : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-! ## 1. Datum `InvDistClass 4` and Gaussian-increment decay (SP 2584-2593) -/

/-- Any `IsB3Datum` belongs to `Heat.InvDistClass 4 C` for some `C ≥ 0`. -/
theorem exists_invDistClass4_of_isB3Datum {P : ℝ} {a : SpatialField}
    (ha : Cons.C03.IsB3Datum P a) : ∃ C : ℝ, Heat.InvDistClass 4 C a := by
  choose Ck hCk using fun (k : Fin 5) => ha.bounds k.1 (Nat.le_of_lt_succ k.2)
  let C : ℝ := Finset.univ.sup' Finset.univ_nonempty Ck
  refine ⟨max C 0, ⟨ha.smooth.of_le (by simp), ?_⟩⟩
  intro j hj x hx
  have hj5 : j < 5 := Nat.lt_succ_of_le hj
  have h1 := hCk ⟨j, hj5⟩ x hx
  have hle : Ck ⟨j, hj5⟩ ≤ max C 0 :=
    (Finset.le_sup' Ck (Finset.mem_univ ⟨j, hj5⟩)).trans (le_max_left _ _)
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hpow : 0 < ‖x‖ ^ (j + 1) := pow_pos hxn _
  have hdiv : ‖iteratedFDeriv ℝ j a x‖ ≤ max C 0 / ‖x‖ ^ (j + 1) := by
    rw [le_div_iff₀ hpow]
    exact h1.trans hle
  have he : -(1 + (j : ℝ)) = -((j + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg hxn.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact hdiv

/-- **SP 2588**: for `a` satisfying `IsB3Datum P a`, `ν > 0`, and `j ≤ 2`, the heat increment
`H_a(τ) - a_τ` (`a_τ(y) = e^{τ/2} a(e^{τ/2} y)`) satisfies
`‖D^j(H_a(τ) - a_τ)(y)‖ ≤ K ‖y‖^{-3-j}` for all `|y| ≥ 1`, uniformly in `τ ∈ ℝ`. -/
theorem heatProfile_sub_scaledDatum_decay {P ν : ℝ} (hν : 0 < ν) {a : SpatialField}
    (ha : Cons.C03.IsB3Datum P a) {j : ℕ} (hj : j ≤ 2) :
    ∃ K : ℝ, ∀ (τ : ℝ) (y : Space), 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ j (fun y' =>
        UnforcedLeray.Blueprint.heatProfile ν a τ y' -
          Real.exp (τ / 2) • a (Real.exp (τ / 2) • y')) y‖ ≤
        K * ‖y‖ ^ (-((3 + j : ℕ) : ℝ)) := by
  obtain ⟨C, hInv⟩ := exists_invDistClass4_of_isB3Datum ha
  obtain ⟨K, hK⟩ := Heat.heat_sub_self_decay (E := Space) C hν hj
  refine ⟨K, fun τ y hy => ?_⟩
  let aτ : SpatialField := fun y' => Real.exp (τ / 2) • a (Real.exp (τ / 2) • y')
  have haτ : Heat.InvDistClass 4 C aτ := hInv.dilate (Real.exp_pos (τ / 2))
  have hEq : (fun y' => UnforcedLeray.Blueprint.heatProfile ν a τ y' - aτ y') =
      fun y' => Heat.average ν aτ y' - aτ y' := by
    funext y'
    have hs : UnforcedLeray.Blueprint.heatProfile ν a τ y' = Heat.simHeat ν a τ y' := rfl
    rw [hs, Heat.simHeat_eq hν a τ]
  rw [hEq]
  exact hK aτ haτ y hy

/-! ## 2. Stress tensor columns `𝕋 = U ⊗ U ∈ H²(ℝ³)` and `-𝐏 div 𝕋 = -𝐏(U·∇U)` (SP 2607-2612) -/

/-- Column `m` of `f ⊗ f`: `(f_m) f`. -/
def stressCol (f : SpatialField) (m : Fin 3) : SpatialField :=
  fun y => (f y m) • f y

theorem contDiff_stressCol {n : WithTop ℕ∞} {f : SpatialField} (hf : ContDiff ℝ n f) (m : Fin 3) :
    ContDiff ℝ n (stressCol f m) :=
  ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).contDiff.comp hf).smul hf

/-- First coordinate derivative of `stressCol f m`: `(∂_i f_m) f + f_m (∂_i f)`. -/
theorem dpart_stressCol {f : SpatialField} (hf : ContDiff ℝ 1 f) (m i : Fin 3) (y : Space) :
    Blueprint.L10.dpart (stressCol f m) i y =
      (Blueprint.L10.dpart f i y m) • f y + (f y m) • Blueprint.L10.dpart f i y := by
  have hfd : HasFDerivAt f (fderiv ℝ f y) y := (hf.differentiable one_ne_zero y).hasFDerivAt
  have hmd : HasFDerivAt (fun x => f x m) ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).comp (fderiv ℝ f y)) y :=
    (EuclideanSpace.proj m : Space →L[ℝ] ℝ).hasFDerivAt.comp y hfd
  have hprod : HasFDerivAt (stressCol f m)
      ((f y m) • fderiv ℝ f y +
        ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).comp (fderiv ℝ f y)).smulRight (f y)) y :=
    hmd.smul hfd
  unfold Blueprint.L10.dpart
  rw [hprod.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.comp_apply]
  change (f y m) • fderiv ℝ f y (coordinateVector i) +
      (fderiv ℝ f y (coordinateVector i) m) • f y = _
  abel

/-- Second coordinate derivative of `stressCol f m`. -/
theorem dpart_dpart_stressCol {f : SpatialField} (hf : ContDiff ℝ 2 f) (m i j : Fin 3)
    (y : Space) :
    Blueprint.L10.dpart (Blueprint.L10.dpart (stressCol f m) i) j y =
      (Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y m) • f y +
        (Blueprint.L10.dpart f i y m) • Blueprint.L10.dpart f j y +
        (Blueprint.L10.dpart f j y m) • Blueprint.L10.dpart f i y +
        (f y m) • Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hdi : ContDiff ℝ 1 (Blueprint.L10.dpart f i) := by
    unfold Blueprint.L10.dpart
    exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have heq : Blueprint.L10.dpart (stressCol f m) i =
      fun x => (Blueprint.L10.dpart f i x m) • f x + (f x m) • Blueprint.L10.dpart f i x :=
    funext (dpart_stressCol hf1 m i)
  have hfd : HasFDerivAt f (fderiv ℝ f y) y := (hf1.differentiable one_ne_zero y).hasFDerivAt
  have hdid : HasFDerivAt (Blueprint.L10.dpart f i) (fderiv ℝ (Blueprint.L10.dpart f i) y) y :=
    (hdi.differentiable one_ne_zero y).hasFDerivAt
  have hm1 : HasFDerivAt (fun x => Blueprint.L10.dpart f i x m)
      ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).comp (fderiv ℝ (Blueprint.L10.dpart f i) y)) y :=
    (EuclideanSpace.proj m : Space →L[ℝ] ℝ).hasFDerivAt.comp y hdid
  have hm0 : HasFDerivAt (fun x => f x m)
      ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).comp (fderiv ℝ f y)) y :=
    (EuclideanSpace.proj m : Space →L[ℝ] ℝ).hasFDerivAt.comp y hfd
  have hsum : HasFDerivAt
      (fun x => (Blueprint.L10.dpart f i x m) • f x + (f x m) • Blueprint.L10.dpart f i x)
      ((Blueprint.L10.dpart f i y m) • fderiv ℝ f y +
        ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).comp
          (fderiv ℝ (Blueprint.L10.dpart f i) y)).smulRight (f y) +
        ((f y m) • fderiv ℝ (Blueprint.L10.dpart f i) y +
          ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).comp
            (fderiv ℝ f y)).smulRight (Blueprint.L10.dpart f i y))) y :=
    (hm1.smul hfd).add (hm0.smul hdid)
  change fderiv ℝ (Blueprint.L10.dpart (stressCol f m) i) y (coordinateVector j) = _
  rw [heq, hsum.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.comp_apply]
  change ((Blueprint.L10.dpart f i y m) • Blueprint.L10.dpart f j y +
      (Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y m) • f y) +
      ((f y m) • Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y +
        (Blueprint.L10.dpart f j y m) • Blueprint.L10.dpart f i y) = _
  abel

private theorem norm_coord_le (v : Space) (m : Fin 3) : |v m| ≤ ‖v‖ := by
  simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v m)

/-- Hölder `(4, 4, 2)` helper: a continuous vector field dominated pointwise by `c * (a y * b y)`
with `‖a‖_{L⁴}, ‖b‖_{L⁴} ≤ C` lies in `L²(ℝ³)` with `l2Norm ≤ c * max C 0 ^ 2`. -/
theorem memLp_two_of_mul_l4 {g : SpatialField} (hg : Continuous g)
    {a b : Space → ℝ} (ha : Continuous a) (hb : Continuous b)
    {c C : ℝ} (hc : 0 ≤ c)
    (ha4 : eLpNorm a 4 volume ≤ ENNReal.ofReal C)
    (hb4 : eLpNorm b 4 volume ≤ ENNReal.ofReal C)
    (hpt : ∀ y : Space, ‖g y‖ ≤ c * (a y * b y)) :
    MemLp g 2 volume ∧ l2Norm g ≤ c * max C 0 ^ 2 := by
  have holder : ENNReal.HolderTriple 4 4 2 := by
    apply ENNReal.HolderTriple.of_toReal
    norm_num [Real.holderTriple_iff]
  let C' : ℝ := max C 0
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have ha4' : eLpNorm a 4 volume ≤ ENNReal.ofReal C' :=
    ha4.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hb4' : eLpNorm b 4 volume ≤ ENNReal.ofReal C' :=
    hb4.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  let cnn : ℝ≥0 := ⟨c, hc⟩
  have hmono : eLpNorm g 2 volume ≤ eLpNorm (fun y => c * (a y * b y)) 2 volume :=
    eLpNorm_mono_real hpt
  have hbilin : eLpNorm (fun y => c * (a y * b y)) 2 volume ≤
      (cnn : ℝ≥0∞) * eLpNorm a 4 volume * eLpNorm b 4 volume :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm ha.aestronglyMeasurable hb.aestronglyMeasurable
      (fun x y : ℝ => c * (x * y)) cnn
      (Filter.Eventually.of_forall fun y => by
        rw [norm_mul, norm_mul, Real.norm_of_nonneg hc, ← mul_assoc]
        exact le_rfl)
      (hpqr := holder)
  have hbd : eLpNorm g 2 volume ≤ ENNReal.ofReal (c * C' ^ 2) := by
    refine (hmono.trans hbilin).trans ?_
    have h1 : (cnn : ℝ≥0∞) * eLpNorm a 4 volume * eLpNorm b 4 volume ≤
        ENNReal.ofReal c * ENNReal.ofReal C' * ENNReal.ofReal C' := by
      rw [ENNReal.ofReal_eq_coe_nnreal hc]
      gcongr
      exact le_rfl
    refine h1.trans ?_
    rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (mul_nonneg hc hC'0)]
    exact ENNReal.ofReal_le_ofReal (by ring_nf; rfl)
  refine ⟨⟨hg.aestronglyMeasurable, lt_of_le_of_lt hbd ENNReal.ofReal_lt_top⟩, ?_⟩
  unfold l2Norm
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbd

private theorem norm_dpart_dpart_c2_le {f : SpatialField} (hf : ContDiff ℝ 2 f) (i j : Fin 3)
    (y : Space) : ‖Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y‖ ≤
      ‖iteratedFDeriv ℝ 2 f y‖ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) y
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector i) y)
  have eq1 : Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y =
      fderiv ℝ (fderiv ℝ f) y (coordinateVector j) (coordinateVector i) := by
    unfold Blueprint.L10.dpart
    rw [h.fderiv]
    simp
  have eq2 : ‖fderiv ℝ (fderiv ℝ f) y‖ = ‖iteratedFDeriv ℝ 2 f y‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  rw [eq1, ← eq2]
  calc ‖fderiv ℝ (fderiv ℝ f) y (coordinateVector j) (coordinateVector i)‖
      ≤ ‖fderiv ℝ (fderiv ℝ f) y (coordinateVector j)‖ * ‖coordinateVector i‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) y‖ * ‖coordinateVector j‖ * ‖coordinateVector i‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (fderiv ℝ f) y‖ := by
        rw [Blueprint.L10.norm_coordinateVector, Blueprint.L10.norm_coordinateVector,
          mul_one, mul_one]

theorem memLp_stressCol {f : SpatialField} {C : ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : eLpNorm f 4 volume ≤ ENNReal.ofReal C) (m : Fin 3) :
    MemLp (stressCol f m) 2 volume ∧ l2Norm (stressCol f m) ≤ max C 0 ^ 2 := by
  have ha0 : eLpNorm (fun y => ‖f y‖) 4 volume ≤ ENNReal.ofReal C := by
    rwa [eLpNorm_norm]
  have h := memLp_two_of_mul_l4 (contDiff_stressCol hf m).continuous
    hf.continuous.norm hf.continuous.norm
    zero_le_one ha0 ha0 fun y => by
      rw [stressCol, norm_smul, Real.norm_eq_abs, one_mul]
      exact mul_le_mul_of_nonneg_right (norm_coord_le (f y) m) (norm_nonneg _)
  simpa only [one_mul] using h

theorem memLp_dpart_stressCol {f : SpatialField} {C : ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : eLpNorm f 4 volume ≤ ENNReal.ofReal C)
    (h1 : eLpNorm (fun y => fderiv ℝ f y) 4 volume ≤ ENNReal.ofReal C) (m i : Fin 3) :
    MemLp (Blueprint.L10.dpart (stressCol f m) i) 2 volume ∧
      l2Norm (Blueprint.L10.dpart (stressCol f m) i) ≤ 2 * max C 0 ^ 2 := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hcd : Continuous (Blueprint.L10.dpart (stressCol f m) i) :=
    (((contDiff_stressCol hf m).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous
  have hc0 : Continuous (fun y => ‖f y‖) := hf.continuous.norm
  have hc1 : Continuous (fun y => ‖fderiv ℝ f y‖) := (hf.continuous_fderiv (by norm_num)).norm
  have ha0 : eLpNorm (fun y => ‖f y‖) 4 volume ≤ ENNReal.ofReal C := by rwa [eLpNorm_norm]
  have ha1 : eLpNorm (fun y => ‖fderiv ℝ f y‖) 4 volume ≤ ENNReal.ofReal C := by rwa [eLpNorm_norm]
  refine memLp_two_of_mul_l4 hcd hc1 hc0
    (by norm_num) ha1 ha0 fun y => ?_
  rw [dpart_stressCol hf1 m i y]
  have b1 : ‖(Blueprint.L10.dpart f i y m) • f y‖ ≤ ‖fderiv ℝ f y‖ * ‖f y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      ((norm_coord_le _ m).trans (Blueprint.L10.norm_dpart_le f i y)) (norm_nonneg _)
  have b2 : ‖(f y m) • Blueprint.L10.dpart f i y‖ ≤ ‖fderiv ℝ f y‖ * ‖f y‖ := by
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul (Blueprint.L10.norm_dpart_le f i y) (norm_coord_le _ m)
      (abs_nonneg _) (norm_nonneg _)
  linarith [norm_add_le ((Blueprint.L10.dpart f i y m) • f y)
    ((f y m) • Blueprint.L10.dpart f i y)]

theorem memLp_dpart_dpart_stressCol {f : SpatialField} {C : ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : eLpNorm f 4 volume ≤ ENNReal.ofReal C)
    (h1 : eLpNorm (fun y => fderiv ℝ f y) 4 volume ≤ ENNReal.ofReal C)
    (h2 : eLpNorm (fun y => iteratedFDeriv ℝ 2 f y) 4 volume ≤ ENNReal.ofReal C)
    (m i j : Fin 3) :
    MemLp (Blueprint.L10.dpart (Blueprint.L10.dpart (stressCol f m) i) j) 2 volume ∧
      l2Norm (Blueprint.L10.dpart (Blueprint.L10.dpart (stressCol f m) i) j) ≤
        4 * max C 0 ^ 2 := by
  have hc0 : Continuous (fun y => ‖f y‖) := hf.continuous.norm
  have hc1 : Continuous (fun y => ‖fderiv ℝ f y‖) := (hf.continuous_fderiv (by norm_num)).norm
  have hc2 : Continuous (fun y => ‖iteratedFDeriv ℝ 2 f y‖) :=
    (hf.continuous_iteratedFDeriv (m := 2) le_rfl).norm
  have ha0 : eLpNorm (fun y => ‖f y‖) 4 volume ≤ ENNReal.ofReal C := by rwa [eLpNorm_norm]
  have ha1 : eLpNorm (fun y => ‖fderiv ℝ f y‖) 4 volume ≤ ENNReal.ofReal C := by rwa [eLpNorm_norm]
  have ha2 : eLpNorm (fun y => ‖iteratedFDeriv ℝ 2 f y‖) 4 volume ≤ ENNReal.ofReal C := by
    rwa [eLpNorm_norm]
  let t1 : SpatialField := fun y =>
    (Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y m) • f y +
      (f y m) • Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y
  let t2 : SpatialField := fun y =>
    (Blueprint.L10.dpart f i y m) • Blueprint.L10.dpart f j y +
      (Blueprint.L10.dpart f j y m) • Blueprint.L10.dpart f i y
  have hdd_cont : Continuous (Blueprint.L10.dpart (Blueprint.L10.dpart f i) j) := by
    have hdi : ContDiff ℝ 1 (Blueprint.L10.dpart f i) :=
      (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact (hdi.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hd_cont : ∀ k, Continuous (Blueprint.L10.dpart f k) := fun k =>
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have ht1c : Continuous t1 :=
    (((EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous.comp hdd_cont).smul hf.continuous).add
      (((EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous.comp hf.continuous).smul hdd_cont)
  have ht2c : Continuous t2 :=
    (((EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous.comp (hd_cont i)).smul (hd_cont j)).add
      (((EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous.comp (hd_cont j)).smul (hd_cont i))
  obtain ⟨m1, l1⟩ := memLp_two_of_mul_l4 ht1c hc2 hc0
    (by norm_num : (0 : ℝ) ≤ 2) ha2 ha0 fun y => by
      have b1 : ‖(Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y m) • f y‖ ≤
          ‖iteratedFDeriv ℝ 2 f y‖ * ‖f y‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          ((norm_coord_le _ m).trans (norm_dpart_dpart_c2_le hf i j y)) (norm_nonneg _)
      have b2 : ‖(f y m) • Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y‖ ≤
          ‖iteratedFDeriv ℝ 2 f y‖ * ‖f y‖ := by
        rw [norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul (norm_dpart_dpart_c2_le hf i j y) (norm_coord_le _ m)
          (abs_nonneg _) (norm_nonneg _)
      linarith [norm_add_le ((Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y m) • f y)
        ((f y m) • Blueprint.L10.dpart (Blueprint.L10.dpart f i) j y)]
  obtain ⟨m2, l2⟩ := memLp_two_of_mul_l4 ht2c hc1 hc1
    (by norm_num : (0 : ℝ) ≤ 2) ha1 ha1 fun y => by
      have b1 : ‖(Blueprint.L10.dpart f i y m) • Blueprint.L10.dpart f j y‖ ≤
          ‖fderiv ℝ f y‖ * ‖fderiv ℝ f y‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul ((norm_coord_le _ m).trans (Blueprint.L10.norm_dpart_le f i y))
          (Blueprint.L10.norm_dpart_le f j y) (norm_nonneg _) (norm_nonneg _)
      have b2 : ‖(Blueprint.L10.dpart f j y m) • Blueprint.L10.dpart f i y‖ ≤
          ‖fderiv ℝ f y‖ * ‖fderiv ℝ f y‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul ((norm_coord_le _ m).trans (Blueprint.L10.norm_dpart_le f j y))
          (Blueprint.L10.norm_dpart_le f i y) (norm_nonneg _) (norm_nonneg _)
      linarith [norm_add_le ((Blueprint.L10.dpart f i y m) • Blueprint.L10.dpart f j y)
        ((Blueprint.L10.dpart f j y m) • Blueprint.L10.dpart f i y)]
  have heq : Blueprint.L10.dpart (Blueprint.L10.dpart (stressCol f m) i) j = t1 + t2 := by
    funext y
    rw [dpart_dpart_stressCol hf m i j y]
    simp only [t1, t2, Pi.add_apply]
    abel
  rw [heq]
  refine ⟨m1.add m2, ?_⟩
  have htri : l2Norm (t1 + t2) ≤ l2Norm t1 + l2Norm t2 := by
    rw [← norm_toL2 (m1.add m2), ← norm_toL2 m1, ← norm_toL2 m2, Blueprint.L10.toL2_add' m1 m2]
    exact norm_add_le _ _
  linarith

/-- The `H²(ℝ³)` columns `(f_m f)_{m < 3}` of `𝕋 = f ⊗ f` for `C²` fields bounded in `W^{2,4}`. -/
def stressColH2 (f : SpatialField) {C : ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : eLpNorm f 4 volume ≤ ENNReal.ofReal C)
    (h1 : eLpNorm (fun y => fderiv ℝ f y) 4 volume ≤ ENNReal.ofReal C)
    (h2 : eLpNorm (fun y => iteratedFDeriv ℝ 2 f y) 4 volume ≤ ENNReal.ofReal C)
    (m : Fin 3) : SobolevGraph.H2 :=
  H2.ofFields (stressCol f m)
    (fun i => Blueprint.L10.dpart (stressCol f m) i)
    (fun i j => Blueprint.L10.dpart (Blueprint.L10.dpart (stressCol f m) i) j)
    (memLp_stressCol hf h0 m).1
    (fun i => (memLp_dpart_stressCol hf h0 h1 m i).1)
    (fun i j => (memLp_dpart_dpart_stressCol hf h0 h1 h2 m i j).1)
    (fun i => hasWeakSpatialDerivative_of_contDiff ((contDiff_stressCol hf m).of_le (by norm_num)) i)
    (fun i j => hasWeakSpatialDerivative_of_contDiff
      (((contDiff_stressCol hf m).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const) j)

theorem norm_stressColH2_le (f : SpatialField) {C : ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : eLpNorm f 4 volume ≤ ENNReal.ofReal C)
    (h1 : eLpNorm (fun y => fderiv ℝ f y) 4 volume ≤ ENNReal.ofReal C)
    (h2 : eLpNorm (fun y => iteratedFDeriv ℝ 2 f y) 4 volume ≤ ENNReal.ofReal C)
    (m : Fin 3) :
    ‖stressColH2 f hf h0 h1 h2 m‖ ≤ 43 * max C 0 ^ 2 := by
  let M : ℝ := max C 0 ^ 2
  have hM : 0 ≤ M := sq_nonneg _
  have hv : ‖(stressColH2 f hf h0 h1 h2 m).value‖ ≤ M := by
    change ‖toL2 (stressCol f m)‖ ≤ M
    rw [norm_toL2 (memLp_stressCol hf h0 m).1]
    exact (memLp_stressCol hf h0 m).2
  have h1' : ∀ i, ‖(stressColH2 f hf h0 h1 h2 m).first i‖ ≤ 2 * M := by
    intro i
    change ‖toL2 (Blueprint.L10.dpart (stressCol f m) i)‖ ≤ 2 * M
    rw [norm_toL2 (memLp_dpart_stressCol hf h0 h1 m i).1]
    exact (memLp_dpart_stressCol hf h0 h1 m i).2
  have h2' : ∀ i j, ‖(stressColH2 f hf h0 h1 h2 m).second i j‖ ≤ 4 * M := by
    intro i j
    change ‖toL2 (Blueprint.L10.dpart (Blueprint.L10.dpart (stressCol f m) i) j)‖ ≤ 4 * M
    rw [norm_toL2 (memLp_dpart_dpart_stressCol hf h0 h1 h2 m i j).1]
    exact (memLp_dpart_dpart_stressCol hf h0 h1 h2 m i j).2
  have hb := Loc.L02.h2_norm_le_of hM (by positivity) (by positivity) hv h1' h2'
  linarith

/-- A `C¹` distributionally solenoidal field has pointwise vanishing divergence. -/
theorem sum_dpart_eq_zero_of_isSolenoidal {f : SpatialField} (hf : ContDiff ℝ 1 f)
    (hsol : IsSolenoidal f) (y : Space) :
    ∑ m : Fin 3, Blueprint.L10.dpart f m y m = 0 := by
  let divf : Space → ℝ := fun x => ∑ m : Fin 3, Blueprint.L10.dpart f m x m
  have hdiv_cont : Continuous divf := by
    refine continuous_finsetSum Finset.univ fun m _ => ?_
    exact (EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous.comp
      ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hae : divf =ᵐ[volume] (0 : Space → ℝ) := by
    apply ae_eq_of_integral_contDiff_smul_eq hdiv_cont.locallyIntegrable
      (locallyIntegrable_const (0 : ℝ))
    intro φ hφs hφc
    have hφ : IsSpatialTest φ := ⟨hφs, hφc⟩
    simp only [smul_zero, integral_zero]
    have hwk : ∀ m : Fin 3, HasWeakSpatialDerivative m f (Blueprint.L10.dpart f m) :=
      fun m => hasWeakSpatialDerivative_of_contDiff hf m
    have hterm : ∀ m : Fin 3,
        ∫ x, φ x * (Blueprint.L10.dpart f m x m) =
          -(∫ x, f x m * spatialTestDerivative m φ x) := by
      intro m
      let pm : Space →L[ℝ] ℝ := EuclideanSpace.proj m
      have hp1 : (∫ x, pm (spatialTestDerivative m φ x • f x)) =
          pm (∫ x, spatialTestDerivative m φ x • f x) :=
        pm.integral_comp_comm ((hwk m).left_integrable φ hφ)
      have hp2 : (∫ x, pm (φ x • Blueprint.L10.dpart f m x)) =
          pm (∫ x, φ x • Blueprint.L10.dpart f m x) :=
        pm.integral_comp_comm ((hwk m).right_integrable φ hφ)
      have hpm : pm (∫ x, spatialTestDerivative m φ x • f x) =
          -pm (∫ x, φ x • Blueprint.L10.dpart f m x) := by
        rw [(hwk m).identity φ hφ, map_neg]
      rw [← hp1, ← hp2] at hpm
      change (∫ x, spatialTestDerivative m φ x * f x m) =
        -(∫ x, φ x * Blueprint.L10.dpart f m x m) at hpm
      have hcomm : (∫ x, spatialTestDerivative m φ x * f x m) =
          ∫ x, f x m * spatialTestDerivative m φ x := by
        congr 1; funext x; ring
      linarith
    have hint_m : ∀ m ∈ (Finset.univ : Finset (Fin 3)),
        Integrable (fun x => φ x * Blueprint.L10.dpart f m x m) := by
      intro m _
      exact (EuclideanSpace.proj m : Space →L[ℝ] ℝ).integrable_comp
        ((hwk m).right_integrable φ hφ)
    have hint_f : ∀ m ∈ (Finset.univ : Finset (Fin 3)),
        Integrable (fun x => f x m * spatialTestDerivative m φ x) := by
      intro m _
      have hL : Integrable (fun x => spatialTestDerivative m φ x * f x m) :=
        (EuclideanSpace.proj m : Space →L[ℝ] ℝ).integrable_comp ((hwk m).left_integrable φ hφ)
      exact hL.congr (Filter.Eventually.of_forall fun x => mul_comm _ _)
    have hsum1 : (∫ x, φ x • divf x) =
        ∑ m : Fin 3, ∫ x, φ x * Blueprint.L10.dpart f m x m := by
      have heq : (fun x => φ x • divf x) =
          fun x => ∑ m : Fin 3, φ x * Blueprint.L10.dpart f m x m := by
        funext x
        simp only [divf, smul_eq_mul, Finset.mul_sum]
      rw [heq, integral_finsetSum Finset.univ hint_m]
    rw [hsum1, Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_neg_distrib,
      ← integral_finsetSum Finset.univ hint_f, hsol.identity φ hφ, neg_zero]
  have hfun : divf = 0 := (Continuous.ae_eq_iff_eq volume hdiv_cont continuous_const).mp hae
  exact congrFun hfun y

/-- For `C²` solenoidal `f`, `-𝐏 div(f ⊗ f)` in `X = H¹_div` has `L²` class `-𝐏(f·∇f)`. -/
theorem Xclass_minusLerayDivX_stressColH2 (f : SpatialField) {C : ℝ} (hf : ContDiff ℝ 2 f)
    (hsol : IsSolenoidal f)
    (h0 : eLpNorm f 4 volume ≤ ENNReal.ofReal C)
    (h1 : eLpNorm (fun y => fderiv ℝ f y) 4 volume ≤ ENNReal.ofReal C)
    (h2 : eLpNorm (fun y => iteratedFDeriv ℝ 2 f y) 4 volume ≤ ENNReal.ofReal C) :
    Blueprint.Xclass (Blueprint.L10.minusLerayDivX (stressColH2 f hf h0 h1 h2)) =
      -Leray.projection (toL2 (fun y => fderiv ℝ f y (f y))) := by
  rw [Blueprint.L10.Xclass_minusLerayDivX]
  congr 2
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hm : ∀ m : Fin 3, (stressColH2 f hf h0 h1 h2 m).first m =
      toL2 (Blueprint.L10.dpart (stressCol f m) m) := fun _ => rfl
  simp_rw [hm]
  have hpt : (fun y => ∑ m : Fin 3, Blueprint.L10.dpart (stressCol f m) m y) =
      fun y => fderiv ℝ f y (f y) := by
    funext y
    simp_rw [dpart_stressCol hf1 _ _ y]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, sum_dpart_eq_zero_of_isSolenoidal hf1 hsol y,
      zero_smul, zero_add]
    unfold Blueprint.L10.dpart coordinateVector
    simp_rw [← map_smul, ← map_sum, Blueprint.L10.space_sum_single (f y)]
  have hsum_toL2 : (∑ m : Fin 3, toL2 (Blueprint.L10.dpart (stressCol f m) m)) =
      toL2 (fun y => ∑ m : Fin 3, Blueprint.L10.dpart (stressCol f m) m y) := by
    apply Lp.ext
    have hmem : MemLp (fun y => ∑ m : Fin 3, Blueprint.L10.dpart (stressCol f m) m y) 2 volume :=
      memLp_finsetSum Finset.univ fun m _ => (memLp_dpart_stressCol hf h0 h1 m m).1
    have hall := (ae_ball_iff (Finset.univ : Finset (Fin 3)).countable_toSet).mpr
      fun m _ => coeFn_toL2 (memLp_dpart_stressCol hf h0 h1 m m).1
    filter_upwards [Blueprint.L10.coeFn_finsetSum Finset.univ
        (fun m : Fin 3 => toL2 (Blueprint.L10.dpart (stressCol f m) m)),
      coeFn_toL2 hmem, hall] with y h1' h2' h3'
    rw [h1', h2']
    exact Finset.sum_congr rfl fun m hm => h3' m hm
  rw [hsum_toL2, hpt]

/-! ## 3. Free similarity Duhamel `H²` integral and continuity (SP 2614-2629) -/

/-- Continuous linear lift of `Blueprint.L10.minusLerayDivX : (Fin 3 → H2) → X`. -/
def minusLerayDivXLinear : (Fin 3 → SobolevGraph.H2) →ₗ[ℝ] Blueprint.X where
  toFun := Blueprint.L10.minusLerayDivX
  map_add' P Q := by
    apply Blueprint.L10.Xclass_injective
    rw [Blueprint.L10.Xclass_add, Blueprint.L10.Xclass_minusLerayDivX,
      Blueprint.L10.Xclass_minusLerayDivX, Blueprint.L10.Xclass_minusLerayDivX]
    have h : (∑ j : Fin 3, (P j + Q j).first j) =
        (∑ j : Fin 3, (P j).first j) + ∑ j : Fin 3, (Q j).first j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => rfl
    rw [Pi.add_def, h, map_add, neg_add]
  map_smul' c P := by
    apply Blueprint.L10.Xclass_injective
    rw [RingHom.id_apply, Blueprint.L10.Xclass_smul, Blueprint.L10.Xclass_minusLerayDivX,
      Blueprint.L10.Xclass_minusLerayDivX]
    have h : (∑ j : Fin 3, (c • P j).first j) = c • ∑ j : Fin 3, (P j).first j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => rfl
    rw [Pi.smul_def, h, map_smul, smul_neg]

def minusLerayDivXCLM : (Fin 3 → SobolevGraph.H2) →L[ℝ] Blueprint.X :=
  minusLerayDivXLinear.mkContinuous 3 fun P => by
    refine (Blueprint.L10.norm_minusLerayDivX_le P).trans ?_
    calc ∑ j : Fin 3, ‖P j‖ ≤ ∑ _j : Fin 3, ‖P‖ :=
          Finset.sum_le_sum fun j _ => norm_le_pi_norm P j
      _ = 3 * ‖P‖ := by simp

@[simp] theorem minusLerayDivXCLM_apply (P : Fin 3 → SobolevGraph.H2) :
    minusLerayDivXCLM P = Blueprint.L10.minusLerayDivX P := rfl

/-- Long-time `X → Z` exponential decay of `S₀(r)` for `r ≥ 1` via `S₀(r) = S₀(1) S₀(r - 1)`. -/
theorem norm_S0Z_le_large {ν : ℝ} (hν : 0 < ν) {r : ℝ} (hr : 1 ≤ r) :
    ‖Loc.L02.S0Z ν r‖ ≤
      Loc.L02.Cconst ν ^ 2 * Real.exp (1 / 4) * Real.exp (-(1 / 4 : ℝ) * r) := by
  have hS := Loc.L02.isFreeEvolution_freeEvolutionOps hν
  have hcomp : Loc.L02.S0Z ν r = (Loc.L02.S0Z ν 1).comp (Loc.L02.S0X ν (r - 1)) := by
    have h := Loc.L03Evolution.S0Z_comp_S0 hS hν.le zero_lt_one (sub_nonneg.2 hr)
    change (Loc.L02.S0Z ν 1).comp (Loc.L02.S0X ν (r - 1)) = Loc.L02.S0Z ν (1 + (r - 1)) at h
    rw [add_sub_cancel] at h
    exact h.symm
  rw [hcomp]
  have h1 : ‖Loc.L02.S0Z ν 1‖ ≤ Loc.L02.Cconst ν := by
    simpa using Loc.L02.norm_S0Z_le hν zero_lt_one le_rfl
  have h2 : ‖Loc.L02.S0X ν (r - 1)‖ ≤ Loc.L02.Cconst ν * Real.exp (-((r - 1) / 4)) :=
    Loc.L02.norm_S0X_le hν (r - 1)
  calc ‖(Loc.L02.S0Z ν 1).comp (Loc.L02.S0X ν (r - 1))‖
      ≤ ‖Loc.L02.S0Z ν 1‖ * ‖Loc.L02.S0X ν (r - 1)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Loc.L02.Cconst ν * (Loc.L02.Cconst ν * Real.exp (-((r - 1) / 4))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (Loc.L02.Cconst_pos ν).le
    _ = Loc.L02.Cconst ν ^ 2 * Real.exp (1 / 4) * Real.exp (-(1 / 4 : ℝ) * r) := by
        have hexp : Real.exp (-((r - 1) / 4)) = Real.exp (1 / 4) * Real.exp (-(1 / 4 : ℝ) * r) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hexp]
        ring

/-- Combined `X → Z` kernel bound on `(0, ∞)` for `S₀(r)`. -/
theorem norm_S0Z_pastKernel_le {ν : ℝ} (hν : 0 < ν) {r : ℝ} (hr : 0 < r) :
    ‖Loc.L02.S0Z ν r‖ ≤
      (max (Loc.L02.Cconst ν) (Loc.L02.Cconst ν ^ 2) * Real.exp (1 / 4)) *
        (1 + r ^ (-(1 / 2 : ℝ))) * Real.exp (-(1 / 4 : ℝ) * r) := by
  let K : ℝ := max (Loc.L02.Cconst ν) (Loc.L02.Cconst ν ^ 2) * Real.exp (1 / 4)
  have hC0 : 0 < Loc.L02.Cconst ν := Loc.L02.Cconst_pos ν
  rcases le_total r 1 with hr1 | hr1
  · have hs : ‖Loc.L02.S0Z ν r‖ ≤ Loc.L02.Cconst ν * r ^ (-(1 / 2 : ℝ)) := by
      have h := Loc.L02.norm_S0Z_le hν hr hr1
      have hsq : 1 / Real.sqrt r = r ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hr.le]
      rwa [div_eq_mul_one_div, hsq] at h
    have hexp : 1 ≤ Real.exp (1 / 4) * Real.exp (-(1 / 4 : ℝ) * r) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have hK1 : Loc.L02.Cconst ν ≤ max (Loc.L02.Cconst ν) (Loc.L02.Cconst ν ^ 2) := le_max_left _ _
    have hrp : r ^ (-(1 / 2 : ℝ)) ≤ 1 + r ^ (-(1 / 2 : ℝ)) := by linarith
    calc ‖Loc.L02.S0Z ν r‖ ≤ Loc.L02.Cconst ν * r ^ (-(1 / 2 : ℝ)) := hs
      _ ≤ max (Loc.L02.Cconst ν) (Loc.L02.Cconst ν ^ 2) * (1 + r ^ (-(1 / 2 : ℝ))) * 1 := by
          rw [mul_one]
          exact mul_le_mul hK1 hrp (Real.rpow_nonneg hr.le _) (hC0.le.trans hK1)
      _ ≤ max (Loc.L02.Cconst ν) (Loc.L02.Cconst ν ^ 2) * (1 + r ^ (-(1 / 2 : ℝ))) *
            (Real.exp (1 / 4) * Real.exp (-(1 / 4 : ℝ) * r)) := by
          apply mul_le_mul_of_nonneg_left hexp
          exact mul_nonneg (hC0.le.trans hK1) (by positivity)
      _ = K * (1 + r ^ (-(1 / 2 : ℝ))) * Real.exp (-(1 / 4 : ℝ) * r) := by
          dsimp [K]; ring
  · have hl := norm_S0Z_le_large hν hr1
    have hK2 : Loc.L02.Cconst ν ^ 2 ≤ max (Loc.L02.Cconst ν) (Loc.L02.Cconst ν ^ 2) :=
      le_max_right _ _
    have h1 : (1 : ℝ) ≤ 1 + r ^ (-(1 / 2 : ℝ)) :=
      le_add_of_nonneg_right (Real.rpow_nonneg hr.le _)
    calc ‖Loc.L02.S0Z ν r‖
        ≤ Loc.L02.Cconst ν ^ 2 * Real.exp (1 / 4) * Real.exp (-(1 / 4 : ℝ) * r) := hl
      _ ≤ K * 1 * Real.exp (-(1 / 4 : ℝ) * r) := by
          rw [mul_one]
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right hK2 (Real.exp_pos _).le
      _ ≤ K * (1 + r ^ (-(1 / 2 : ℝ))) * Real.exp (-(1 / 4 : ℝ) * r) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- Past-only `HalfLineGreen.GreenKernel` packaging `S₀(τ - s) : X → Z` with `βm = -1/4 < 0`. -/
def freeDuhamelKernel (ν : ℝ) (hν : 0 < ν) :
    Infra.HalfLineGreen.GreenKernel ℝ Blueprint.X Blueprint.Z where
  Km τ s := Loc.L02.S0Z ν (τ - s)
  Kp _ _ := 0
  C := max (Loc.L02.Cconst ν) (Loc.L02.Cconst ν ^ 2) * Real.exp (1 / 4)
  βm := -(1 / 4 : ℝ)
  βp := 1
  norm_Km_le _ _ hs := norm_S0Z_pastKernel_le hν (sub_pos.2 hs)
  norm_Kp_le _ _ _ := by
    rw [ContinuousLinearMap.opNorm_zero]
    have := Loc.L02.Cconst_pos ν
    have : 0 ≤ max (Loc.L02.Cconst ν) (Loc.L02.Cconst ν ^ 2) :=
      this.le.trans (le_max_left _ _)
    positivity
  continuousOn_Km τ x := by
    have hS := Loc.L02.isFreeEvolution_freeEvolutionOps hν
    exact (Loc.L03Evolution.continuousOn_S0Z hS hν.le x).comp
      (continuousOn_const.sub continuousOn_id) fun s (hs : s < τ) => sub_pos.2 hs
  continuousOn_Kp _ _ := continuousOn_const

theorem freeDuhamelKernel_timeContinuous {ν : ℝ} (hν : 0 < ν) :
    (freeDuhamelKernel ν hν).TimeContinuous where
  Km_shift r _ x := by
    have heq : (fun τ : ℝ => (freeDuhamelKernel ν hν).Km τ (τ - r) x) =
        fun _ => Loc.L02.S0Z ν r x := by
      funext τ
      simp [freeDuhamelKernel]
    rw [heq]
    exact continuous_const
  Kp _ _ := continuousOn_const

/-- The `H²(ℝ³)` free Duhamel integral `-∫₀^∞ S₀(r) 𝐏 div 𝕋(τ - r) dr`. -/
def freeStressDuhamelH2 (ν : ℝ) (P : ℝ → Fin 3 → SobolevGraph.H2) (τ : ℝ) : SobolevGraph.H2 :=
  Blueprint.Zincl (∫ r in Ioi (0 : ℝ), Loc.L02.S0Z ν r (minusLerayDivXCLM (P (τ - r))))

/-- **SP 2622-2629**: for any continuous bounded `H²` column path `P`, `freeStressDuhamelH2 ν P`
is continuous into `H²(ℝ³)` on all of `ℝ`. -/
theorem continuous_freeStressDuhamelH2 {ν : ℝ} (hν : 0 < ν)
    {P : ℝ → Fin 3 → SobolevGraph.H2} (hPcont : Continuous P)
    (hPbdd : ∃ B : ℝ, ∀ (τ : ℝ) (m : Fin 3), ‖P τ m‖ ≤ B) :
    Continuous (freeStressDuhamelH2 ν P) := by
  obtain ⟨B, hB⟩ := hPbdd
  let u : ℝ → Blueprint.X := fun s => minusLerayDivXCLM (P s)
  have hu_cont : Continuous u := minusLerayDivXCLM.continuous.comp hPcont
  let M : ℝ := 3 * max B 0
  have hu_bdd : ∀ s : ℝ, ‖u s‖ ≤ M * Real.exp ((0 : ℝ) * s) := by
    intro s
    rw [zero_mul, Real.exp_zero, mul_one]
    refine (Blueprint.L10.norm_minusLerayDivX_le (P s)).trans ?_
    calc ∑ m : Fin 3, ‖P s m‖ ≤ ∑ _m : Fin 3, max B 0 :=
          Finset.sum_le_sum fun m _ => (hB s m).trans (le_max_left _ _)
      _ = M := by simp [M]
  let K := freeDuhamelKernel ν hν
  have htc := freeDuhamelKernel_timeContinuous hν
  have hβ : K.βm < (0 : ℝ) := by simp [K, freeDuhamelKernel]
  have heq : freeStressDuhamelH2 ν P =
      fun τ => Blueprint.Zincl (∫ s in Iio τ, K.Km τ s (u s)) := by
    funext τ
    unfold freeStressDuhamelH2
    congr 1
    rw [Infra.HalfLineGreen.setIntegral_Iio_eq_Ioi τ (fun s => K.Km τ s (u s))]
    congr 1
    funext r
    simp [K, freeDuhamelKernel, u]
  rw [heq]
  refine Blueprint.Zincl.continuous.comp (continuous_iff_continuousAt.2 fun τ₀ => ?_)
  have hcOn := K.continuousOn_pastIntegral htc hβ (τ₀ := τ₀ + 1) hu_cont fun s _ => hu_bdd s
  exact hcOn.continuousAt (Iic_mem_nhds (lt_add_one τ₀))

/-- `L²(ℝ³)` evaluation of `freeStressDuhamelH2 ν P τ` commutes `Zincl` and `H2.valueCLM` inside
the Bochner integral. -/
theorem value_freeStressDuhamelH2 {ν : ℝ} (hν : 0 < ν)
    {P : ℝ → Fin 3 → SobolevGraph.H2} (hPcont : Continuous P)
    (hPbdd : ∃ B : ℝ, ∀ (τ : ℝ) (m : Fin 3), ‖P τ m‖ ≤ B) (τ : ℝ) :
    (freeStressDuhamelH2 ν P τ).value =
      ∫ r in Ioi (0 : ℝ), Loc.L02.freeL2 ν r (Blueprint.Xclass (minusLerayDivXCLM (P (τ - r)))) := by
  obtain ⟨B, hB⟩ := hPbdd
  let u : ℝ → Blueprint.X := fun s => minusLerayDivXCLM (P s)
  have hu_cont : Continuous u := minusLerayDivXCLM.continuous.comp hPcont
  let M : ℝ := 3 * max B 0
  have hu_bdd : ∀ s : ℝ, ‖u s‖ ≤ M * Real.exp ((0 : ℝ) * s) := by
    intro s
    rw [zero_mul, Real.exp_zero, mul_one]
    refine (Blueprint.L10.norm_minusLerayDivX_le (P s)).trans ?_
    calc ∑ m : Fin 3, ‖P s m‖ ≤ ∑ _m : Fin 3, max B 0 :=
          Finset.sum_le_sum fun m _ => (hB s m).trans (le_max_left _ _)
      _ = M := by simp [M]
  let K := freeDuhamelKernel ν hν
  have hβ : K.βm < (0 : ℝ) := by simp [K, freeDuhamelKernel]
  have hint_Iio : IntegrableOn (fun s => K.Km τ s (u s)) (Iio τ) volume :=
    K.integrableOn_Km_apply hβ hu_cont fun s _ => hu_bdd s
  have hint_Ioi : IntegrableOn (fun r => Loc.L02.S0Z ν r (u (τ - r))) (Ioi 0) volume := by
    have h := (Infra.HalfLineGreen.integrableOn_Iio_iff τ
      (g := fun s => K.Km τ s (u s))).mp hint_Iio
    refine h.congr_fun (fun r (_ : 0 < r) => ?_) measurableSet_Ioi
    simp [K, freeDuhamelKernel]
  change (H2.valueCLM.comp Blueprint.Zincl)
      (∫ r in Ioi (0 : ℝ), Loc.L02.S0Z ν r (u (τ - r))) = _
  rw [← (H2.valueCLM.comp Blueprint.Zincl).integral_comp_comm hint_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
  change Blueprint.Zclass (Loc.L02.S0Z ν r (u (τ - r))) = _
  exact Loc.L02.Zclass_S0Z (Loc.L02.heatTime_pos hν hr) (u (τ - r))

/-! ## 4. `L^{11/4}` remainder bound, `L⁴` background continuity, and `∀ᵐ τ → ∀ τ` upgrade -/

/-- At `p.period ≤ 1`, combining `V - H_a ∈ L^{11/4}` (`RawHeatComparison`) with `w ∈ L^{11/4}`
(`S1Sub.corr_eLpNorm_bgp_le_of_period_le_one`) gives a uniform `L^{11/4}` bound on `U - H_a`. -/
theorem remainder_eLpNorm_q0E_le (p : Params) (hP1 : p.period ≤ 1) (z : p.Z)
    (hRaw : IsBoundedBackground p.raw) (hIn : ∀ i : Fin 2, IsBoundedBackground (p.inlet i))
    (ha : Cons.C03.IsB3Datum p.period (p.datum (p.coord z)))
    {M_V : ℝ}
    (hMV : ∀ τ : ℝ,
      eLpNorm ((fun y => p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y) -
        UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ) q0E volume ≤
        ENNReal.ofReal M_V) :
    ∀ τ : ℝ,
      eLpNorm (bgField p z τ -
        UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ) q0E volume ≤
        ENNReal.ofReal (max M_V 0 + ‖z‖) := by
  obtain ⟨C, hInv⟩ := exists_invDistClass4_of_isB3Datum ha
  intro τ
  let V : SpatialField := fun y => p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y
  let Ha : SpatialField := UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ
  have hV_cont : Continuous V :=
    (hRaw.differentiable τ).continuous.add (continuous_finsetSum Finset.univ fun i _ =>
      ((hIn i).differentiable τ).continuous.const_smul (p.coord z i))
  have hHa_cont : Continuous Ha :=
    (Heat.simHeat_contDiff p.ν_pos hInv.heatAdmissible τ).continuous
  have hw_meas : AEStronglyMeasurable (p.corr z τ) volume :=
    (p.corr_memLp_four hP1 z τ).1
  have hsplit : bgField p z τ - Ha = (V - Ha) + p.corr z τ := by
    funext y
    simp only [bgField, V, Pi.sub_apply, Pi.add_apply]
    abel
  have hp1 : (1 : ℝ≥0∞) ≤ q0E := Fact.out
  have hw_bd : eLpNorm (p.corr z τ) q0E volume ≤ ENNReal.ofReal ‖z‖ := by
    have h := S1Sub.corr_eLpNorm_bgp_le_of_period_le_one p hP1 z τ
    rwa [S1Sub.s1_ofReal_bgp_eq_q0E] at h
  rw [hsplit]
  calc eLpNorm ((V - Ha) + p.corr z τ) q0E volume
      ≤ eLpNorm (V - Ha) q0E volume + eLpNorm (p.corr z τ) q0E volume :=
        eLpNorm_add_le (hV_cont.sub hHa_cont).aestronglyMeasurable hw_meas hp1
    _ ≤ ENNReal.ofReal (max M_V 0) + ENNReal.ofReal ‖z‖ :=
        add_le_add ((hMV τ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) hw_bd
    _ = ENNReal.ofReal (max M_V 0 + ‖z‖) :=
        (ENNReal.ofReal_add (le_max_right _ _) (norm_nonneg z)).symm

/-- Decomposing `bgField p z = H_a + (V - H_a) + p.corr z` produces a continuous `L⁴(ℝ³)` path
representing `bgField p z` from `R_V : ℝ → H²` representing `V - H_a`. -/
theorem exists_continuous_bgField_L4 (p : Params) (hP1 : p.period ≤ 1) (z : p.Z)
    (ha : Cons.C03.IsB3Datum p.period (p.datum (p.coord z)))
    {R_V : ℝ → SobolevGraph.H2} (hRV_cont : Continuous R_V)
    (hRV_ae : ∀ τ : ℝ, ((R_V τ).value : SpatialField) =ᵐ[volume]
      (fun y => p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y) -
        UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ) :
    ∃ (W_U W_H : ℝ → Lp Space 4 volume),
      Continuous W_U ∧ Continuous W_H ∧
      (∀ τ : ℝ, (W_U τ : SpatialField) =ᵐ[volume] bgField p z τ) ∧
      (∀ τ : ℝ, (W_H τ : SpatialField) =ᵐ[volume]
        UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ) := by
  obtain ⟨W_H, hWH_cont, hWH_ae⟩ :=
    exists_continuous_heatProfile_L4_of_datum p.ν_pos ha.smooth ha.bounds
  let W_U : ℝ → Lp Space 4 volume :=
    fun τ => (W_H τ + h2ValueL4 (R_V τ)) + p.corrL4Path hP1 z τ
  have hWU_cont : Continuous W_U :=
    (hWH_cont.add (continuous_h2Value_L4 R_V hRV_cont)).add (p.continuous_corrL4Path hP1 z)
  refine ⟨W_U, W_H, hWU_cont, hWH_cont, fun τ => ?_, hWH_ae⟩
  filter_upwards [Lp.coeFn_add (W_H τ + h2ValueL4 (R_V τ)) (p.corrL4Path hP1 z τ),
    Lp.coeFn_add (W_H τ) (h2ValueL4 (R_V τ)),
    hWH_ae τ, h2Value_L4_ae (R_V τ), hRV_ae τ,
    (p.corr_memLp_four hP1 z τ).coeFn_toLp] with y h1 h2 hH hRval hRV hcorr
  have hcorr' : (p.corrL4Path hP1 z τ : SpatialField) y = p.corr z τ y := hcorr
  rw [h1, Pi.add_apply, h2, Pi.add_apply, hH, hRval, hRV, hcorr']
  simp only [bgField, Pi.sub_apply]
  abel

/-- Two continuous paths into `Lp Space 4 volume` (`h2ValueL4 ∘ Q` and `W_U - W_H`) that agree at
almost every phase `τ : ℝ` agree at **every** phase `τ : ℝ`. -/
theorem ae_eq_every_phase_of_aem_phase {U H : ℝ → SpatialField}
    {Q : ℝ → SobolevGraph.H2} (hQ_cont : Continuous Q)
    {W_U W_H : ℝ → Lp Space 4 volume} (hWU_cont : Continuous W_U) (hWH_cont : Continuous W_H)
    (hWU_ae : ∀ τ : ℝ, (W_U τ : SpatialField) =ᵐ[volume] U τ)
    (hWH_ae : ∀ τ : ℝ, (W_H τ : SpatialField) =ᵐ[volume] H τ)
    (h_aem : ∀ᵐ τ : ℝ, ((Q τ).value : SpatialField) =ᵐ[volume] U τ - H τ) :
    ∀ τ : ℝ, ((Q τ).value : SpatialField) =ᵐ[volume] U τ - H τ := by
  have hLp_aem : (fun τ : ℝ => h2ValueL4 (Q τ)) =ᵐ[volume] fun τ : ℝ => W_U τ - W_H τ := by
    filter_upwards [h_aem] with τ hτ
    apply Lp.ext
    filter_upwards [h2Value_L4_ae (Q τ), hτ, Lp.coeFn_sub (W_U τ) (W_H τ),
      hWU_ae τ, hWH_ae τ] with y h1 h2 hsub hU hH
    rw [h1, h2, hsub, Pi.sub_apply, Pi.sub_apply, hU, hH]
  have hLp_eq : (fun τ : ℝ => h2ValueL4 (Q τ)) = fun τ : ℝ => W_U τ - W_H τ :=
    (Continuous.ae_eq_iff_eq volume (continuous_h2Value_L4 Q hQ_cont)
      (hWU_cont.sub hWH_cont)).mp hLp_aem
  intro τ
  have hτ_eq : h2ValueL4 (Q τ) = W_U τ - W_H τ := congrFun hLp_eq τ
  filter_upwards [h2Value_L4_ae (Q τ), Lp.coeFn_sub (W_U τ) (W_H τ),
    hWU_ae τ, hWH_ae τ] with y h1 hsub hU hH
  have hval : (h2ValueL4 (Q τ) : SpatialField) y = ((W_U τ - W_H τ : Lp Space 4 volume) : SpatialField) y := by
    rw [hτ_eq]
  rw [← h1, hval, hsub, Pi.sub_apply, Pi.sub_apply, hU, hH]

end B3RemH2Sub

/-! ## 5. Named `Prop` leaves for the remaining >100-line analytic sub-steps -/

/-- **Leaf 1 (`short-bg:raw-heat`, SP 2586-2603)**: at contraction-ball states, the raw+inlet minus
heat profile `V - H_a` (`V = p.raw + ∑ i, p.coord z i • p.inlet i`,
`H_a = Blueprint.heatProfile p.ν (p.datum (p.coord z))`) admits a continuous `H²(ℝ³)` path `R_V`
representing `V(τ) - H_a(τ)` a.e. at every phase and is uniformly bounded in `L^{11/4}(ℝ³)`
(`q0E`).  Proved from `B3RemH2Sub.heatProfile_sub_scaledDatum_decay` (`Lib/HeatR3/SubSelf.lean`),
the `O(s)` inlet expansion at large radius, and the all-age train axial decay on bounded radii. -/
def RawHeatComparison : Prop :=
  B3Stmt.AtBallStates fun p z =>
    (∃ R_V : ℝ → SobolevGraph.H2, Continuous R_V ∧
      ∀ τ : ℝ, ((R_V τ).value : SpatialField) =ᵐ[volume]
        (fun y => p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y) -
          UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ) ∧
    ∃ M_V : ℝ, ∀ τ : ℝ,
      eLpNorm ((fun y => p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y) -
        UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ) q0E volume ≤
        ENNReal.ofReal M_V

/-- **Leaf 2 (`𝕋 = U ⊗ U ∈ C_per H²`, SP 2607-2612)**: for a jointly smooth `W^{k,4}`-bounded
family `U : ℝ → SpatialField` (`IsUniformSmoothL4SliceFamily U`) whose comoving derivative `U₁`
also belongs to `IsUniformSmoothL4SliceFamily`, the `H²(ℝ³)` stress-column map
`τ ↦ B3RemH2Sub.stressColH2 (U τ) ...` is continuous in phase `τ : ℝ`. -/
def StressColsContinuousH2 : Prop :=
  ∀ (U : ℝ → SpatialField),
    ContDiff ℝ ∞ (fun x : ℝ × Space => U x.1 x.2) →
    IsUniformSmoothL4SliceFamily U →
    (∃ U₁ : ℝ → SpatialField, IsUniformSmoothL4SliceFamily U₁ ∧ HasComovingJetDeriv U U₁) →
    ∀ (C : ℝ) (hf : ∀ τ : ℝ, ContDiff ℝ 2 (U τ))
      (h0 : ∀ τ : ℝ, eLpNorm (U τ) 4 volume ≤ ENNReal.ofReal C)
      (h1 : ∀ τ : ℝ, eLpNorm (fun y => fderiv ℝ (U τ) y) 4 volume ≤ ENNReal.ofReal C)
      (h2 : ∀ τ : ℝ, eLpNorm (fun y => iteratedFDeriv ℝ 2 (U τ) y) 4 volume ≤ ENNReal.ofReal C),
      Continuous (fun τ : ℝ => fun m : Fin 3 =>
        B3RemH2Sub.stressColH2 (U τ) (hf τ) (h0 τ) (h1 τ) (h2 τ) m)

/-- **Leaf 3 (Free uniqueness identification in `Y_p`, SP 2613-2619)**: for `ν > 0`, `0 < P ≤ 1`,
a datum `a` satisfying `Cons.C03.IsB3Datum P a`, and a jointly smooth `P`-periodic solenoidal
family `U` in `IsUniformSmoothL4SliceFamily`, if `W = U - Blueprint.heatProfile ν a` is uniformly
bounded in `L^{11/4}(ℝ³)` (`q0E`) and satisfies `(∂_τ - ½y·∇ - νΔ - ½)W = -𝐏(U·∇U)` a.e. at every
phase, then free uniqueness on `Y_{11/4}` (`PartIIa.bodyResolvent_exists`,
`PartIIa.bodyResolvent_solves`, `PartIIa.bodyOp_uniqueness`) identifies `W(τ)` for almost every
phase `τ : ℝ` with the `L²` Bochner integral `∫₀^∞ S₀(r)[-𝐏(U·∇U)(τ - r)] dr`. -/
def FreeDuhamelUniquenessAe : Prop :=
  ∀ (ν P : ℝ), 0 < ν → 0 < P → P ≤ 1 →
  ∀ (a : SpatialField), Cons.C03.IsB3Datum P a →
  ∀ (U : ℝ → SpatialField),
    ContDiff ℝ ∞ (fun x : ℝ × Space => U x.1 x.2) →
    IsUniformSmoothL4SliceFamily U →
    Function.Periodic U P →
    (∀ τ : ℝ, IsSolenoidal (U τ)) →
    (∃ M_q : ℝ, ∀ τ : ℝ,
      eLpNorm (U τ - UnforcedLeray.Blueprint.heatProfile ν a τ) q0E volume ≤ ENNReal.ofReal M_q) →
    (∀ τ : ℝ,
      (fun y => deriv (fun t => U t y - UnforcedLeray.Blueprint.heatProfile ν a t y) τ -
          (1 / 2 : ℝ) • fderiv ℝ (fun y' => U τ y' - UnforcedLeray.Blueprint.heatProfile ν a τ y') y y -
          ν • UnforcedLeray.Heat.vlap (fun y' => U τ y' - UnforcedLeray.Blueprint.heatProfile ν a τ y') y -
          (1 / 2 : ℝ) • (U τ y - UnforcedLeray.Blueprint.heatProfile ν a τ y))
        =ᵐ[volume] ⇑(-(UnforcedLeray.Leray.projection (UnforcedLeray.toL2
          (fun y => fderiv ℝ (U τ) y (U τ y)))))) →
    ∀ᵐ τ : ℝ,
      (((∫ r in Ioi (0 : ℝ), Loc.L02.freeL2 ν r
          (-(UnforcedLeray.Leray.projection (UnforcedLeray.toL2
            (fun y => fderiv ℝ (U (τ - r)) y (U (τ - r) y)))) : L2Space) : L2Space) : SpatialField)
        =ᵐ[volume] U τ - UnforcedLeray.Blueprint.heatProfile ν a τ)

end UnforcedLeray.Short.IIb

end
