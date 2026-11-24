import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.MainDiff2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.ZPrimRegular.RayPrim
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Leibniz
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.Comm

/-!
# `PartIII-b:C/rep/8/1/1/2/5/2/1/4` (`YBWidth.sepCommPsiDiff`): outward stream-primitive commutator difference

Source `the November 2 reference manuscript`
lines 4178-4215, 5383-5387, 5415-5432; SP 3604-3610, 3700-3712, 3735-3766.

Proves `YBWidth.sepCommPsiDiff : YBWidth.SepCommPsiDiff`: on the transition annulus
`ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4` (`r = √(xo 0 ^ 2 + xo 1 ^ 2)`),
`‖fderiv ℝ (commPsi ν μ ε⁻¹ χy (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G))) τ) (ε⁻¹ • xo) -
    fderiv ℝ (commPsi ν μ ε⁻¹ χy (newtonX0 ε μ G) τ) (ε⁻¹ • xo)‖ ≤
  C₃ * (1 + ν⁻¹ + c) ^ k * ε ^ 4 * r ^ (-5 : ℝ) *
    ∫ w, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi ContinuousMultilinearMap
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIIa

namespace YBWidth

open YBComm PhasePrim GeomXAsm GeomXAsm.RayFTCAux GeomXAsm.RayPrimAux

/-! ## 1. Partial-derivative bounds and `HasDecay45` -/

private theorem contDiffAt_physPd {g : Space → Space} {y : Space} (hg : ContDiffAt ℝ ∞ g y)
    (j : Fin 3) : ContDiffAt ℝ ∞ (physPd g j) y := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ g) y :=
    hg.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤))
  exact (ContinuousLinearMap.apply ℝ Space (coordinateVector j)).contDiff.contDiffAt.comp y hd

private theorem norm_iteratedFDeriv_physPd_le (m : ℕ) {g : Space → Space} {y : Space}
    (hg : ContDiffAt ℝ ∞ g y) (j : Fin 3) :
    ‖iteratedFDeriv ℝ m (physPd g j) y‖ ≤ ‖iteratedFDeriv ℝ (m + 1) g y‖ := by
  let L : (Space →L[ℝ] Space) →L[ℝ] Space :=
    ContinuousLinearMap.apply ℝ Space (coordinateVector j)
  have hd : ContDiffAt ℝ m (fderiv ℝ g) y :=
    hg.fderiv_right (m := m) (by exact_mod_cast le_top)
  have hcomp : iteratedFDeriv ℝ m (physPd g j) y =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ m (fderiv ℝ g) y) :=
    L.iteratedFDeriv_comp_left (f := fderiv ℝ g) hd le_rfl
  have hiso : iteratedFDeriv ℝ m (fderiv ℝ g) y =
      (continuousMultilinearCurryRightEquiv' ℝ m Space Space)
        (iteratedFDeriv ℝ (m + 1) g y) := by
    rw [iteratedFDeriv_succ_eq_comp_right]; simp
  have hnorm_eq : ‖iteratedFDeriv ℝ m (fderiv ℝ g) y‖ = ‖iteratedFDeriv ℝ (m + 1) g y‖ := by
    rw [hiso, LinearIsometryEquiv.norm_map]
  rw [hcomp, ← hnorm_eq]
  set M := iteratedFDeriv ℝ m (fderiv ℝ g) y
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg M) fun v => ?_
  change ‖M v (coordinateVector j)‖ ≤ ‖M‖ * ∏ i : Fin m, ‖v i‖
  calc ‖M v (coordinateVector j)‖
      ≤ ‖M v‖ * ‖(coordinateVector j : Space)‖ := (M v).le_opNorm _
    _ = ‖M v‖ := by rw [norm_e j, mul_one]
    _ ≤ ‖M‖ * ∏ i : Fin m, ‖v i‖ := M.le_opNorm v

private theorem norm_fderiv_le_iter1 {g : Space → Space} {y : Space} :
    ‖fderiv ℝ g y‖ ≤ ‖iteratedFDeriv ℝ 1 g y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  have h := (iteratedFDeriv ℝ 1 g y).le_opNorm ![v]
  simpa [iteratedFDeriv_one_apply] using h

private theorem norm_self_le_iter0 {g : Space → Space} {y : Space} :
    ‖g y‖ ≤ ‖iteratedFDeriv ℝ 0 g y‖ := by
  rw [norm_iteratedFDeriv_zero]

/-- A τ-independent field on `{y' : Space | r₁ < ϱ y'}` with `O(ϱ⁻⁴)` value and `O(ϱ⁻⁵)` gradient. -/
structure HasDecay45 (r₁ A₀ A₁ : ℝ) (W : ℝ → Space → Space) : Prop where
  A0_nonneg : 0 ≤ A₀
  A1_nonneg : 0 ≤ A₁
  tau_indep : ∀ t, W t = W 0
  diff : ∀ y', r₁ < ϱ y' → DifferentiableAt ℝ (W 0) y'
  bound0 : ∀ y', r₁ < ϱ y' → ‖W 0 y'‖ ≤ A₀ * (ϱ y') ^ (-4 : ℝ)
  bound1 : ∀ y', r₁ < ϱ y' → ‖fderiv ℝ (W 0) y'‖ ≤ A₁ * (ϱ y') ^ (-5 : ℝ)

private theorem ϱ_hpt_of_pos {ρ : ℝ} (hρ : 0 < ρ) (z : ℝ) : ϱ (hpt ρ z) = ρ := by
  unfold ϱ hpt
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hρ.le]

namespace HasDecay45

variable {r₁ A₀ A₁ : ℝ} {W : ℝ → Space → Space}

theorem rayDecay (hW : HasDecay45 r₁ A₀ A₁ W) (hr₁ : 0 < r₁) {r₀ : ℝ} (hr₀ : r₁ < r₀)
    (z : ℝ) : RayDecay W 0 r₀ z 1 (max A₀ A₁) := by
  refine ⟨fun ρ hρ z' _ => ?_, fun ρ hρ z' _ => ?_, fun ρ hρ z' _ => ?_⟩
  · have hρ1 : r₁ < ρ := lt_of_lt_of_le hr₀ hρ
    have hρ0 : 0 < ρ := lt_trans hr₁ hρ1
    exact hW.diff (hpt ρ z') (by rw [ϱ_hpt_of_pos hρ0]; exact hρ1)
  · have hρ1 : r₁ < ρ := lt_of_lt_of_le hr₀ hρ
    have hρ0 : 0 < ρ := lt_trans hr₁ hρ1
    have hb := hW.bound0 (hpt ρ z') (by rw [ϱ_hpt_of_pos hρ0]; exact hρ1)
    rw [ϱ_hpt_of_pos hρ0] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hρ0.le _))
  · have hρ1 : r₁ < ρ := lt_of_lt_of_le hr₀ hρ
    have hρ0 : 0 < ρ := lt_trans hr₁ hρ1
    have hb := hW.bound1 (hpt ρ z') (by rw [ϱ_hpt_of_pos hρ0]; exact hρ1)
    rw [ϱ_hpt_of_pos hρ0] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hρ0.le _))

theorem primData (hW : HasDecay45 r₁ A₀ A₁ W) (hr₁ : 0 < r₁) {r : ℝ} (hr : r₁ < r) (z : ℝ) :
    PrimData W 0 r z := by
  let r₀ := (r₁ + r) / 2
  have hr₀1 : r₁ < r₀ := by dsimp [r₀]; linarith
  have hr₀r : r₀ < r := by dsimp [r₀]; linarith
  have hr₀0 : 0 < r₀ := lt_trans hr₁ hr₀1
  exact primData_of_decay (hW.rayDecay hr₁ hr₀1 z) hr₀0 one_pos hr₀r

theorem outPrim_le (hW : HasDecay45 r₁ A₀ A₁ W) (hr₁ : 0 < r₁) {r : ℝ} (hr : r₁ < r) (z : ℝ) :
    |outPrim W 0 r z| ≤ A₀ * r ^ (-2 : ℝ) := by
  have hr0 : 0 < r := lt_trans hr₁ hr
  have hP := hW.primData hr₁ hr z
  have hdom : IntegrableOn (fun ρ : ℝ => A₀ * ρ ^ (-3 : ℝ)) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hr0).const_mul A₀
  have hbd : ∀ᵐ ρ ∂(volume.restrict (Ioi r)), ‖ρ * W 0 (hpt ρ z) 2‖ ≤ A₀ * ρ ^ (-3 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    have hρ1 : r₁ < ρ := lt_trans hr hρ
    have hρ0 : 0 < ρ := lt_trans hr0 hρ
    have h1 := hW.bound0 (hpt ρ z) (by rw [ϱ_hpt_of_pos hρ0]; exact hρ1)
    rw [ϱ_hpt_of_pos hρ0] at h1
    have h2 : |W 0 (hpt ρ z) 2| ≤ ‖W 0 (hpt ρ z)‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (W 0 (hpt ρ z)) 2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ0]
    calc ρ * |W 0 (hpt ρ z) 2| ≤ ρ * (A₀ * ρ ^ (-4 : ℝ)) := by gcongr; exact h2.trans h1
      _ = A₀ * ρ ^ (-3 : ℝ) := by
          rw [← mul_assoc, mul_comm ρ A₀, mul_assoc, rpow_mul_rpow ρ hρ0]; norm_num
  have hint_le := norm_integral_le_of_norm_le hdom hbd
  have hval : ∫ ρ in Ioi r, A₀ * ρ ^ (-3 : ℝ) = (A₀ / 2) * r ^ (-2 : ℝ) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hr0,
      show (-3 : ℝ) + 1 = -2 by norm_num]
    ring
  unfold outPrim
  rw [abs_neg, ← Real.norm_eq_abs]
  have hA0 := hW.A0_nonneg
  have hrp : 0 ≤ r ^ (-2 : ℝ) := Real.rpow_nonneg hr0.le _
  calc ‖∫ ρ in Ioi r, ρ * W 0 !₂[ρ, 0, z] 2‖
      ≤ ∫ ρ in Ioi r, A₀ * ρ ^ (-3 : ℝ) := hint_le
    _ = (A₀ / 2) * r ^ (-2 : ℝ) := hval
    _ ≤ A₀ * r ^ (-2 : ℝ) := by nlinarith

theorem primDz_le (hW : HasDecay45 r₁ A₀ A₁ W) (hr₁ : 0 < r₁) {r : ℝ} (hr : r₁ < r) (z : ℝ) :
    |primDz W 0 r z| ≤ A₁ * r ^ (-3 : ℝ) := by
  have hr0 : 0 < r := lt_trans hr₁ hr
  have hdom : IntegrableOn (fun ρ : ℝ => A₁ * ρ ^ (-4 : ℝ)) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hr0).const_mul A₁
  have hbd : ∀ᵐ ρ ∂(volume.restrict (Ioi r)),
      ‖ρ * fderiv ℝ (W 0) (hpt ρ z) (coordinateVector 2) 2‖ ≤ A₁ * ρ ^ (-4 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    have hρ1 : r₁ < ρ := lt_trans hr hρ
    have hρ0 : 0 < ρ := lt_trans hr0 hρ
    have h1 := hW.bound1 (hpt ρ z) (by rw [ϱ_hpt_of_pos hρ0]; exact hρ1)
    rw [ϱ_hpt_of_pos hρ0] at h1
    have h2 : |fderiv ℝ (W 0) (hpt ρ z) (coordinateVector 2) 2| ≤ ‖fderiv ℝ (W 0) (hpt ρ z)‖ := by
      have hp := PiLp.norm_apply_le (fderiv ℝ (W 0) (hpt ρ z) (coordinateVector 2)) 2
      rw [Real.norm_eq_abs] at hp
      refine hp.trans ?_
      calc ‖fderiv ℝ (W 0) (hpt ρ z) (coordinateVector 2)‖
          ≤ ‖fderiv ℝ (W 0) (hpt ρ z)‖ * ‖(coordinateVector 2 : Space)‖ :=
            (fderiv ℝ (W 0) (hpt ρ z)).le_opNorm _
        _ = ‖fderiv ℝ (W 0) (hpt ρ z)‖ := by rw [norm_e 2, mul_one]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ0]
    calc ρ * |fderiv ℝ (W 0) (hpt ρ z) (coordinateVector 2) 2|
        ≤ ρ * (A₁ * ρ ^ (-5 : ℝ)) := by gcongr; exact h2.trans h1
      _ = A₁ * ρ ^ (-4 : ℝ) := by
          rw [← mul_assoc, mul_comm ρ A₁, mul_assoc, rpow_mul_rpow ρ hρ0]; norm_num
  have hint_le := norm_integral_le_of_norm_le hdom hbd
  have hval : ∫ ρ in Ioi r, A₁ * ρ ^ (-4 : ℝ) = (A₁ / 3) * r ^ (-3 : ℝ) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hr0,
      show (-4 : ℝ) + 1 = -3 by norm_num]
    ring
  unfold primDz
  rw [← Real.norm_eq_abs]
  have hA1 := hW.A1_nonneg
  have hrp : 0 ≤ r ^ (-3 : ℝ) := Real.rpow_nonneg hr0.le _
  calc ‖∫ ρ in Ioi r, ρ * fderiv ℝ (W 0) (hpt ρ z) (coordinateVector 2) 2‖
      ≤ ∫ ρ in Ioi r, A₁ * ρ ^ (-4 : ℝ) := hint_le
    _ = (A₁ / 3) * r ^ (-3 : ℝ) := hval
    _ ≤ A₁ * r ^ (-3 : ℝ) := by nlinarith

theorem hasFDerivAt_outPrim (hW : HasDecay45 r₁ A₀ A₁ W) (hr₁ : 0 < r₁) {y : Space}
    (hy : r₁ < ϱ y) :
    HasFDerivAt (fun y' : Space => outPrim W 0 (ϱ y') (y' 2))
      ((ϱ y * W 0 (hpt (ϱ y) (y 2)) 2) • ϱD y +
        (-primDz W 0 (ϱ y) (y 2)) • (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)) y := by
  have hρ : 0 < ϱ y := lt_trans hr₁ hy
  have hP := (hW.primData hr₁ hy (y 2)).2.2
  have hG := (hasFDerivAt_ϱ (tcle_notaxis hρ)).prodMk
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have hcomp := hP.comp y hG
  refine hcomp.congr_fderiv ?_
  ext v
  simp

theorem hasFDerivAt_hpt_eval2 (hW : HasDecay45 r₁ A₀ A₁ W) (hr₁ : 0 < r₁) {y : Space}
    (hy : r₁ < ϱ y) :
    HasFDerivAt (fun y' : Space => W 0 (hpt (ϱ y') (y' 2)) 2)
      ((physPd (W 0) 0 (hpt (ϱ y) (y 2)) 2) • ϱD y +
        (physPd (W 0) 2 (hpt (ϱ y) (y 2)) 2) •
          (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)) y := by
  have hρ : 0 < ϱ y := lt_trans hr₁ hy
  have hhpt : (fun y' : Space => hpt (ϱ y') (y' 2)) =
      fun y' : Space => ϱ y' • (coordinateVector 0 : Space) +
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) y' • (coordinateVector 2 : Space) :=
    funext fun y' => hpt_eq_lin (ϱ y') (y' 2)
  have hG : HasFDerivAt (fun y' : Space => hpt (ϱ y') (y' 2))
      ((ϱD y).smulRight (coordinateVector 0) +
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight (coordinateVector 2)) y := by
    rw [hhpt]
    exact ((hasFDerivAt_ϱ (tcle_notaxis hρ)).smul_const (coordinateVector 0)).add
      ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.smul_const
        (coordinateVector 2))
  have hdW : HasFDerivAt (W 0) (fderiv ℝ (W 0) (hpt (ϱ y) (y 2))) (hpt (ϱ y) (y 2)) :=
    (hW.diff (hpt (ϱ y) (y 2)) (by rw [ϱ_hpt_of_pos hρ]; exact hy)).hasFDerivAt
  have hcomp := (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp y
    (hdW.comp y hG)
  refine hcomp.congr_fderiv ?_
  ext v
  simp [physPd, map_smul]
  ring

theorem hasFDerivAt_coeff_mul_outPrim (hW : HasDecay45 r₁ A₀ A₁ W) (hr₁ : 0 < r₁)
    {g : ℝ → ℝ} {g' : ℝ} {y : Space} (hy : r₁ < ϱ y) (hg : HasDerivAt g g' (ϱ y)) :
    ∃ L : Space →L[ℝ] ℝ,
      HasFDerivAt (fun y' : Space => g (ϱ y') * outPrim W 0 (ϱ y') (y' 2)) L y ∧
      ‖L‖ ≤ |g'| * A₀ * (ϱ y) ^ (-2 : ℝ) + |g (ϱ y)| * (A₀ + A₁) * (ϱ y) ^ (-3 : ℝ) := by
  have hρ : 0 < ϱ y := lt_trans hr₁ hy
  have hA0 := hW.A0_nonneg
  have hA1 := hW.A1_nonneg
  have hgc : HasFDerivAt (fun y' : Space => g (ϱ y')) (g' • ϱD y) y :=
    hg.comp_hasFDerivAt y (hasFDerivAt_ϱ (tcle_notaxis hρ))
  have hu := hW.hasFDerivAt_outPrim hr₁ hy
  refine ⟨_, hgc.mul hu, ?_⟩
  have hϱn : ‖ϱD y‖ ≤ 1 := wgx_norm_ϱD_le hρ
  have hp2n : ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v 2
  have hu_val := hW.outPrim_le hr₁ hy (y 2)
  have hdz_val := hW.primDz_le hr₁ hy (y 2)
  have hW_val : |W 0 (hpt (ϱ y) (y 2)) 2| ≤ A₀ * (ϱ y) ^ (-4 : ℝ) := by
    have h1 := hW.bound0 (hpt (ϱ y) (y 2)) (by rw [ϱ_hpt_of_pos hρ]; exact hy)
    rw [ϱ_hpt_of_pos hρ] at h1
    have h2 : |W 0 (hpt (ϱ y) (y 2)) 2| ≤ ‖W 0 (hpt (ϱ y) (y 2))‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (W 0 (hpt (ϱ y) (y 2))) 2
    exact h2.trans h1
  have hrW : |ϱ y * W 0 (hpt (ϱ y) (y 2)) 2| ≤ A₀ * (ϱ y) ^ (-3 : ℝ) := by
    rw [abs_mul, abs_of_pos hρ]
    calc ϱ y * |W 0 (hpt (ϱ y) (y 2)) 2| ≤ ϱ y * (A₀ * (ϱ y) ^ (-4 : ℝ)) := by gcongr
      _ = A₀ * (ϱ y) ^ (-3 : ℝ) := by
          rw [← mul_assoc, mul_comm (ϱ y) A₀, mul_assoc, rpow_mul_rpow (ϱ y) hρ]; norm_num
  have hdu_norm : ‖(ϱ y * W 0 (hpt (ϱ y) (y 2)) 2) • ϱD y +
      (-primDz W 0 (ϱ y) (y 2)) • (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤
      (A₀ + A₁) * (ϱ y) ^ (-3 : ℝ) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    calc |ϱ y * W 0 (hpt (ϱ y) (y 2)) 2| * ‖ϱD y‖ +
          |primDz W 0 (ϱ y) (y 2)| * ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖
        ≤ (A₀ * (ϱ y) ^ (-3 : ℝ)) * 1 + (A₁ * (ϱ y) ^ (-3 : ℝ)) * 1 := by gcongr
      _ = (A₀ + A₁) * (ϱ y) ^ (-3 : ℝ) := by ring
  have h1 : ‖g (ϱ y) • ((ϱ y * W 0 (hpt (ϱ y) (y 2)) 2) • ϱD y +
      (-primDz W 0 (ϱ y) (y 2)) • (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ))‖ ≤
      |g (ϱ y)| * ((A₀ + A₁) * (ϱ y) ^ (-3 : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
  have h2 : ‖outPrim W 0 (ϱ y) (y 2) • (g' • ϱD y)‖ ≤
      (A₀ * (ϱ y) ^ (-2 : ℝ)) * (|g'| * 1) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    gcongr
  refine (norm_add_le _ _).trans ?_
  linarith [h1, h2]

theorem hasFDerivAt_coeff_mul_hpt (hW : HasDecay45 r₁ A₀ A₁ W) (hr₁ : 0 < r₁)
    {g : ℝ → ℝ} {g' : ℝ} {y : Space} (hy : r₁ < ϱ y) (hg : HasDerivAt g g' (ϱ y)) :
    ∃ L : Space →L[ℝ] ℝ,
      HasFDerivAt (fun y' : Space => g (ϱ y') * W 0 (hpt (ϱ y') (y' 2)) 2) L y ∧
      ‖L‖ ≤ |g'| * A₀ * (ϱ y) ^ (-4 : ℝ) + 2 * |g (ϱ y)| * A₁ * (ϱ y) ^ (-5 : ℝ) := by
  have hρ : 0 < ϱ y := lt_trans hr₁ hy
  have hA0 := hW.A0_nonneg
  have hA1 := hW.A1_nonneg
  have hgc : HasFDerivAt (fun y' : Space => g (ϱ y')) (g' • ϱD y) y :=
    hg.comp_hasFDerivAt y (hasFDerivAt_ϱ (tcle_notaxis hρ))
  have hz := hW.hasFDerivAt_hpt_eval2 hr₁ hy
  refine ⟨_, hgc.mul hz, ?_⟩
  have hϱn : ‖ϱD y‖ ≤ 1 := wgx_norm_ϱD_le hρ
  have hp2n : ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v 2
  have hW_val : |W 0 (hpt (ϱ y) (y 2)) 2| ≤ A₀ * (ϱ y) ^ (-4 : ℝ) := by
    have h1 := hW.bound0 (hpt (ϱ y) (y 2)) (by rw [ϱ_hpt_of_pos hρ]; exact hy)
    rw [ϱ_hpt_of_pos hρ] at h1
    have h2 : |W 0 (hpt (ϱ y) (y 2)) 2| ≤ ‖W 0 (hpt (ϱ y) (y 2))‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (W 0 (hpt (ϱ y) (y 2))) 2
    exact h2.trans h1
  have hpd_le : ∀ j : Fin 3, |physPd (W 0) j (hpt (ϱ y) (y 2)) 2| ≤ A₁ * (ϱ y) ^ (-5 : ℝ) := by
    intro j
    have h1 := hW.bound1 (hpt (ϱ y) (y 2)) (by rw [ϱ_hpt_of_pos hρ]; exact hy)
    rw [ϱ_hpt_of_pos hρ] at h1
    have h2 : |physPd (W 0) j (hpt (ϱ y) (y 2)) 2| ≤ ‖fderiv ℝ (W 0) (hpt (ϱ y) (y 2))‖ := by
      unfold physPd
      have hp := PiLp.norm_apply_le (fderiv ℝ (W 0) (hpt (ϱ y) (y 2)) (coordinateVector j)) 2
      rw [Real.norm_eq_abs] at hp
      refine hp.trans ?_
      calc ‖fderiv ℝ (W 0) (hpt (ϱ y) (y 2)) (coordinateVector j)‖
          ≤ ‖fderiv ℝ (W 0) (hpt (ϱ y) (y 2))‖ * ‖(coordinateVector j : Space)‖ :=
            (fderiv ℝ (W 0) (hpt (ϱ y) (y 2))).le_opNorm _
        _ = ‖fderiv ℝ (W 0) (hpt (ϱ y) (y 2))‖ := by rw [norm_e j, mul_one]
    exact h2.trans h1
  have hdz_norm : ‖(physPd (W 0) 0 (hpt (ϱ y) (y 2)) 2) • ϱD y +
      (physPd (W 0) 2 (hpt (ϱ y) (y 2)) 2) •
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤
      2 * A₁ * (ϱ y) ^ (-5 : ℝ) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hp0 := hpd_le 0
    have hp2 := hpd_le 2
    calc |physPd (W 0) 0 (hpt (ϱ y) (y 2)) 2| * ‖ϱD y‖ +
          |physPd (W 0) 2 (hpt (ϱ y) (y 2)) 2| * ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖
        ≤ (A₁ * (ϱ y) ^ (-5 : ℝ)) * 1 + (A₁ * (ϱ y) ^ (-5 : ℝ)) * 1 := by gcongr
      _ = 2 * A₁ * (ϱ y) ^ (-5 : ℝ) := by ring
  have h1 : ‖g (ϱ y) • ((physPd (W 0) 0 (hpt (ϱ y) (y 2)) 2) • ϱD y +
      (physPd (W 0) 2 (hpt (ϱ y) (y 2)) 2) •
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ))‖ ≤
      |g (ϱ y)| * (2 * A₁ * (ϱ y) ^ (-5 : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
  have h2 : ‖W 0 (hpt (ϱ y) (y 2)) 2 • (g' • ϱD y)‖ ≤
      (A₀ * (ϱ y) ^ (-4 : ℝ)) * (|g'| * 1) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    gcongr
  refine (norm_add_le _ _).trans ?_
  linarith [h1, h2]

end HasDecay45

/-! ## 2. `ValidPsiFieldWith` and the representation `commPsi = phiScalar • e₂` -/

/-- A τ-independent `C^∞` field on `{y' : Space | r₁ < ϱ y'}` with derivatives up to order 3
bounded by `B * (ϱ y') ^ (-4 - n)`. -/
structure ValidPsiFieldWith (r₁ B : ℝ) (Z : ℝ → Space → Space) : Prop where
  B_nonneg : 0 ≤ B
  tau_indep : ∀ t, Z t = Z 0
  smooth : ∀ y', r₁ < ϱ y' → ContDiffAt ℝ ∞ (Z 0) y'
  decay : ∀ n ≤ 3, ∀ y', r₁ < ϱ y' → ‖iteratedFDeriv ℝ n (Z 0) y'‖ ≤ B * (ϱ y') ^ (-4 - (n : ℝ))

namespace ValidPsiFieldWith

variable {r₁ B : ℝ} {Z : ℝ → Space → Space}

theorem add {B₁ B₂ : ℝ} {X Y : ℝ → Space → Space}
    (hX : ValidPsiFieldWith r₁ B₁ X) (hY : ValidPsiFieldWith r₁ B₂ Y) :
    ValidPsiFieldWith r₁ (B₁ + B₂) (fun t y' => X t y' + Y t y') where
  B_nonneg := add_nonneg hX.B_nonneg hY.B_nonneg
  tau_indep t := funext fun y' => by simp [hX.tau_indep t, hY.tau_indep t]
  smooth y' hy' := (hX.smooth y' hy').add (hY.smooth y' hy')
  decay n hn y' hy' := by
    have hXn : ContDiffAt ℝ n (X 0) y' := (hX.smooth y' hy').of_le (by exact_mod_cast le_top)
    have hYn : ContDiffAt ℝ n (Y 0) y' := (hY.smooth y' hy').of_le (by exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ n (X 0 + Y 0) y'‖ ≤ (B₁ + B₂) * (ϱ y') ^ (-4 - (n : ℝ))
    rw [iteratedFDeriv_add_apply hXn hYn]
    refine (norm_add_le _ _).trans ?_
    linarith [hX.decay n hn y' hy', hY.decay n hn y' hy']

theorem hasDecay45_self (hZ : ValidPsiFieldWith r₁ B Z) :
    HasDecay45 r₁ B B Z where
  A0_nonneg := hZ.B_nonneg
  A1_nonneg := hZ.B_nonneg
  tau_indep := hZ.tau_indep
  diff y' hy' := (hZ.smooth y' hy').differentiableAt (by simp)
  bound0 y' hy' := by
    have := hZ.decay 0 (by omega) y' hy'
    rw [norm_iteratedFDeriv_zero] at this
    simpa using this
  bound1 y' hy' := by
    have h := hZ.decay 1 (by omega) y' hy'
    exact norm_fderiv_le_iter1.trans (by simpa [show (-4 - (1 : ℝ)) = -5 by norm_num] using h)

private theorem rpow_step1 {r₁ ρ : ℝ} (hr₁ : 0 < r₁) (hρ : r₁ < ρ) (a : ℝ) :
    ρ ^ (a - 1) ≤ r₁⁻¹ * ρ ^ a := by
  have hρ0 : 0 < ρ := lt_trans hr₁ hρ
  rw [Real.rpow_sub hρ0, Real.rpow_one, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hr₁ hρ.le) (Real.rpow_nonneg hρ0.le a)

private theorem rpow_step2 {r₁ ρ : ℝ} (hr₁ : 0 < r₁) (hρ : r₁ < ρ) (a : ℝ) :
    ρ ^ (a - 2) ≤ (r₁⁻¹) ^ 2 * ρ ^ a := by
  have h1 := rpow_step1 hr₁ hρ (a - 1)
  have h2 := rpow_step1 hr₁ hρ a
  have hr10 : 0 ≤ r₁⁻¹ := inv_nonneg.2 hr₁.le
  calc ρ ^ (a - 2) = ρ ^ (a - 1 - 1) := by ring_nf
    _ ≤ r₁⁻¹ * ρ ^ (a - 1) := h1
    _ ≤ r₁⁻¹ * (r₁⁻¹ * ρ ^ a) := mul_le_mul_of_nonneg_left h2 hr10
    _ = (r₁⁻¹) ^ 2 * ρ ^ a := by ring

theorem hasDecay45_physPd (hZ : ValidPsiFieldWith r₁ B Z) (hr₁ : 0 < r₁) (j : Fin 3) :
    HasDecay45 r₁ (B * r₁⁻¹) (B * r₁⁻¹) (fun _ w => physPd (Z 0) j w) where
  A0_nonneg := mul_nonneg hZ.B_nonneg (inv_nonneg.2 hr₁.le)
  A1_nonneg := mul_nonneg hZ.B_nonneg (inv_nonneg.2 hr₁.le)
  tau_indep _ := rfl
  diff y' hy' := (contDiffAt_physPd (hZ.smooth y' hy') j).differentiableAt (by simp)
  bound0 y' hy' := by
    have h1 : ‖physPd (Z 0) j y'‖ ≤ ‖iteratedFDeriv ℝ 1 (Z 0) y'‖ :=
      norm_self_le_iter0.trans (norm_iteratedFDeriv_physPd_le 0 (hZ.smooth y' hy') j)
    have h2 : ‖iteratedFDeriv ℝ 1 (Z 0) y'‖ ≤ B * (ϱ y') ^ (-4 - (1 : ℝ)) := by
      simpa using hZ.decay 1 (by omega) y' hy'
    have h3 := rpow_step1 hr₁ hy' (-4 : ℝ)
    have hB := hZ.B_nonneg
    calc ‖physPd (Z 0) j y'‖ ≤ B * (ϱ y') ^ (-4 - (1 : ℝ)) := h1.trans h2
      _ = B * (ϱ y') ^ ((-4 : ℝ) - 1) := by ring_nf
      _ ≤ B * (r₁⁻¹ * (ϱ y') ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_left h3 hB
      _ = (B * r₁⁻¹) * (ϱ y') ^ (-4 : ℝ) := by ring
  bound1 y' hy' := by
    have h1 : ‖fderiv ℝ (physPd (Z 0) j) y'‖ ≤ ‖iteratedFDeriv ℝ 2 (Z 0) y'‖ :=
      norm_fderiv_le_iter1.trans (norm_iteratedFDeriv_physPd_le 1 (hZ.smooth y' hy') j)
    have h2 : ‖iteratedFDeriv ℝ 2 (Z 0) y'‖ ≤ B * (ϱ y') ^ (-4 - (2 : ℝ)) := by
      simpa using hZ.decay 2 (by omega) y' hy'
    have h3 := rpow_step1 hr₁ hy' (-5 : ℝ)
    have hB := hZ.B_nonneg
    calc ‖fderiv ℝ (physPd (Z 0) j) y'‖ ≤ B * (ϱ y') ^ (-4 - (2 : ℝ)) := h1.trans h2
      _ = B * (ϱ y') ^ ((-5 : ℝ) - 1) := by ring_nf
      _ ≤ B * (r₁⁻¹ * (ϱ y') ^ (-5 : ℝ)) := mul_le_mul_of_nonneg_left h3 hB
      _ = (B * r₁⁻¹) * (ϱ y') ^ (-5 : ℝ) := by ring

theorem hasDecay45_physPd2 (hZ : ValidPsiFieldWith r₁ B Z) (hr₁ : 0 < r₁) (j l : Fin 3) :
    HasDecay45 r₁ (B * (r₁⁻¹) ^ 2) (B * (r₁⁻¹) ^ 2) (fun _ w => physPd2 (Z 0) j l w) where
  A0_nonneg := mul_nonneg hZ.B_nonneg (sq_nonneg _)
  A1_nonneg := mul_nonneg hZ.B_nonneg (sq_nonneg _)
  tau_indep _ := rfl
  diff y' hy' :=
    (contDiffAt_physPd (contDiffAt_physPd (hZ.smooth y' hy') l) j).differentiableAt (by simp)
  bound0 y' hy' := by
    have hcd1 := contDiffAt_physPd (hZ.smooth y' hy') l
    have h1 : ‖physPd2 (Z 0) j l y'‖ ≤ ‖iteratedFDeriv ℝ 2 (Z 0) y'‖ :=
      (norm_self_le_iter0.trans (norm_iteratedFDeriv_physPd_le 0 hcd1 j)).trans
        (norm_iteratedFDeriv_physPd_le 1 (hZ.smooth y' hy') l)
    have h2 : ‖iteratedFDeriv ℝ 2 (Z 0) y'‖ ≤ B * (ϱ y') ^ (-4 - (2 : ℝ)) := by
      simpa using hZ.decay 2 (by omega) y' hy'
    have h3 := rpow_step2 hr₁ hy' (-4 : ℝ)
    have hB := hZ.B_nonneg
    calc ‖physPd2 (Z 0) j l y'‖ ≤ B * (ϱ y') ^ (-4 - (2 : ℝ)) := h1.trans h2
      _ = B * (ϱ y') ^ ((-4 : ℝ) - 2) := by ring_nf
      _ ≤ B * ((r₁⁻¹) ^ 2 * (ϱ y') ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_left h3 hB
      _ = (B * (r₁⁻¹) ^ 2) * (ϱ y') ^ (-4 : ℝ) := by ring
  bound1 y' hy' := by
    have hcd1 := contDiffAt_physPd (hZ.smooth y' hy') l
    have h1 : ‖fderiv ℝ (physPd2 (Z 0) j l) y'‖ ≤ ‖iteratedFDeriv ℝ 3 (Z 0) y'‖ :=
      (norm_fderiv_le_iter1.trans (norm_iteratedFDeriv_physPd_le 1 hcd1 j)).trans
        (norm_iteratedFDeriv_physPd_le 2 (hZ.smooth y' hy') l)
    have h2 : ‖iteratedFDeriv ℝ 3 (Z 0) y'‖ ≤ B * (ϱ y') ^ (-4 - (3 : ℝ)) := by
      simpa using hZ.decay 3 (by omega) y' hy'
    have h3 := rpow_step2 hr₁ hy' (-5 : ℝ)
    have hB := hZ.B_nonneg
    calc ‖fderiv ℝ (physPd2 (Z 0) j l) y'‖ ≤ B * (ϱ y') ^ (-4 - (3 : ℝ)) := h1.trans h2
      _ = B * (ϱ y') ^ ((-5 : ℝ) - 2) := by ring_nf
      _ ≤ B * ((r₁⁻¹) ^ 2 * (ϱ y') ^ (-5 : ℝ)) := mul_le_mul_of_nonneg_left h3 hB
      _ = (B * (r₁⁻¹) ^ 2) * (ϱ y') ^ (-5 : ℝ) := by ring

theorem hasDecay45_physLap (hZ : ValidPsiFieldWith r₁ B Z) (hr₁ : 0 < r₁) :
    HasDecay45 r₁ (3 * B * (r₁⁻¹) ^ 2) (3 * B * (r₁⁻¹) ^ 2) (fun _ w => physLap (Z 0) w) where
  A0_nonneg := by have := hZ.B_nonneg; positivity
  A1_nonneg := by have := hZ.B_nonneg; positivity
  tau_indep _ := rfl
  diff y' hy' := by
    unfold physLap
    exact DifferentiableAt.fun_sum fun j _ => (hZ.hasDecay45_physPd2 hr₁ j j).diff y' hy'
  bound0 y' hy' := by
    unfold physLap
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin 3, ‖physPd2 (Z 0) j j y'‖
        ≤ ∑ _j : Fin 3, (B * (r₁⁻¹) ^ 2) * (ϱ y') ^ (-4 : ℝ) :=
          Finset.sum_le_sum fun j _ => (hZ.hasDecay45_physPd2 hr₁ j j).bound0 y' hy'
      _ = (3 * B * (r₁⁻¹) ^ 2) * (ϱ y') ^ (-4 : ℝ) := by simp [Finset.sum_const]; ring
  bound1 y' hy' := by
    have hd : ∀ j : Fin 3, DifferentiableAt ℝ (physPd2 (Z 0) j j) y' :=
      fun j => (hZ.hasDecay45_physPd2 hr₁ j j).diff y' hy'
    have heq : fderiv ℝ (physLap (Z 0)) y' = ∑ j : Fin 3, fderiv ℝ (physPd2 (Z 0) j j) y' := by
      unfold physLap
      exact fderiv_fun_sum fun j _ => hd j
    rw [heq]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin 3, ‖fderiv ℝ (physPd2 (Z 0) j j) y'‖
        ≤ ∑ _j : Fin 3, (B * (r₁⁻¹) ^ 2) * (ϱ y') ^ (-5 : ℝ) :=
          Finset.sum_le_sum fun j _ => (hZ.hasDecay45_physPd2 hr₁ j j).bound1 y' hy'
      _ = (3 * B * (r₁⁻¹) ^ 2) * (ϱ y') ^ (-5 : ℝ) := by simp [Finset.sum_const]; ring

end ValidPsiFieldWith

/-- The explicit scalar coefficient of `coordinateVector 2` in `commPsi` for a τ-independent
field `Z`. -/
def phiScalar (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (y' : Space) : ℝ :=
  tcB1 ν R χy (ϱ y') * outPrim Z 0 (ϱ y') (y' 2) +
  tcB2 ν R χy (ϱ y') * Z 0 (hpt (ϱ y') (y' 2)) 2 -
  ν * (tcF0 ν R χy (ϱ y') * ϱ y') * physPd (Z 0) 0 (hpt (ϱ y') (y' 2)) 2 -
  ν * tcF0 ν R χy (ϱ y') * outPrim (fun _ w => physPd2 (Z 0) 2 2 w) 0 (ϱ y') (y' 2) +
  ν * tcF0 ν R χy (ϱ y') * outPrim (fun _ w => physLap (Z 0) w) 0 (ϱ y') (y' 2)

private theorem outPrim_congr_tau {Z : ℝ → Space → Space} (ht : ∀ t, Z t = Z 0) (τ r z : ℝ) :
    outPrim Z τ r z = outPrim Z 0 r z := by
  unfold outPrim
  rw [ht τ]

private theorem primDz_eq_neg_outPrim_physPd (Z : ℝ → Space → Space) (r z : ℝ) :
    -primDz Z 0 r z = outPrim (fun _ w => physPd (Z 0) 2 w) 0 r z := rfl

private theorem outPrim_euler_eq {r₁ B : ℝ} {Z : ℝ → Space → Space}
    (hZ : ValidPsiFieldWith r₁ B Z) (hr₁ : 0 < r₁) {r : ℝ} (hr : r₁ < r) (z : ℝ) :
    IntegrableOn (fun ρ : ℝ => ρ * (fderiv ℝ (Z 0) !₂[ρ, 0, z] !₂[ρ, 0, z]) 2) (Ioi r) ∧
    outPrim (fun t y' => fderiv ℝ (Z t) y' y') 0 r z =
      r ^ 2 * Z 0 (hpt r z) 2 - 2 * outPrim Z 0 r z - z * primDz Z 0 r z := by
  have hr0 : 0 < r := lt_trans hr₁ hr
  have hf_int : IntegrableOn (fun ρ : ℝ => ρ * Z 0 (hpt ρ z) 2) (Ioi r) :=
    (hZ.hasDecay45_self.primData hr₁ hr z).1
  have hg_int : IntegrableOn (fun ρ : ℝ => ρ * physPd (Z 0) 2 (hpt ρ z) 2) (Ioi r) :=
    (hZ.hasDecay45_self.primData hr₁ hr z).2.1
  have hA_cont : ContinuousOn (fun ρ : ℝ => ρ ^ 2 * physPd (Z 0) 0 (hpt ρ z) 2) (Ioi r) := by
    intro ρ hρ
    have hρ1 : r₁ < ρ := lt_trans hr hρ
    have hρ0 : 0 < ρ := lt_trans hr0 hρ
    have hd : ContinuousAt (physPd (Z 0) 0) (hpt ρ z) :=
      ((hZ.hasDecay45_physPd hr₁ 0).diff (hpt ρ z) (by rw [ϱ_hpt_of_pos hρ0]; exact hρ1)).continuousAt
    have hc : ContinuousAt (fun s : ℝ => physPd (Z 0) 0 (hpt s z) 2) ρ :=
      ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.continuousAt).comp
        (ContinuousAt.comp (g := physPd (Z 0) 0) (f := fun s => hpt s z) hd
          (continuous_hpt' z).continuousAt)
    exact ((continuousAt_id.pow 2).mul hc).continuousWithinAt
  have hA_int : IntegrableOn (fun ρ : ℝ => ρ ^ 2 * physPd (Z 0) 0 (hpt ρ z) 2) (Ioi r) := by
    have hdom : IntegrableOn (fun ρ : ℝ => B * ρ ^ (-3 : ℝ)) (Ioi r) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hr0).const_mul B
    refine Integrable.mono' hdom (hA_cont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    have hρ1 : r₁ < ρ := lt_trans hr hρ
    have hρ0 : 0 < ρ := lt_trans hr0 hρ
    have h1 := hZ.hasDecay45_self.bound1 (hpt ρ z) (by rw [ϱ_hpt_of_pos hρ0]; exact hρ1)
    rw [ϱ_hpt_of_pos hρ0] at h1
    have h2 : |physPd (Z 0) 0 (hpt ρ z) 2| ≤ ‖fderiv ℝ (Z 0) (hpt ρ z)‖ := by
      unfold physPd
      have hp := PiLp.norm_apply_le (fderiv ℝ (Z 0) (hpt ρ z) (coordinateVector 0)) 2
      rw [Real.norm_eq_abs] at hp
      refine hp.trans ?_
      calc ‖fderiv ℝ (Z 0) (hpt ρ z) (coordinateVector 0)‖
          ≤ ‖fderiv ℝ (Z 0) (hpt ρ z)‖ * ‖(coordinateVector 0 : Space)‖ :=
            (fderiv ℝ (Z 0) (hpt ρ z)).le_opNorm _
        _ = ‖fderiv ℝ (Z 0) (hpt ρ z)‖ := by rw [norm_e 0, mul_one]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hρ0 2)]
    calc ρ ^ 2 * |physPd (Z 0) 0 (hpt ρ z) 2|
        ≤ ρ ^ 2 * (B * ρ ^ (-5 : ℝ)) := by gcongr; exact h2.trans h1
      _ = B * (ρ * (ρ * ρ ^ (-5 : ℝ))) := by ring
      _ = B * ρ ^ (-3 : ℝ) := by
          rw [rpow_mul_rpow ρ hρ0, rpow_mul_rpow ρ hρ0]; norm_num
  have hlin : ∀ ρ : ℝ, ρ * (fderiv ℝ (Z 0) !₂[ρ, 0, z] !₂[ρ, 0, z]) 2 =
      ρ ^ 2 * physPd (Z 0) 0 (hpt ρ z) 2 + z * (ρ * physPd (Z 0) 2 (hpt ρ z) 2) := by
    intro ρ
    have hhpt : (!₂[ρ, 0, z] : Space) = hpt ρ z := rfl
    rw [hhpt, hpt_eq_lin ρ z, map_add, map_smul, map_smul, ← hpt_eq_lin ρ z]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, physPd]
    ring
  have hint_full : IntegrableOn (fun ρ : ℝ => ρ * (fderiv ℝ (Z 0) !₂[ρ, 0, z] !₂[ρ, 0, z]) 2)
      (Ioi r) := by
    refine (hA_int.add (hg_int.const_mul z)).congr_fun (fun ρ _ => (hlin ρ).symm)
      measurableSet_Ioi
  refine ⟨hint_full, ?_⟩
  have hd_f : ∀ ρ ∈ Ici r, HasDerivAt (fun s => Z 0 (hpt s z) 2)
      (physPd (Z 0) 0 (hpt ρ z) 2) ρ := by
    intro ρ hρ
    have hρ1 : r₁ < ρ := lt_of_lt_of_le hr hρ
    have hρ0 : 0 < ρ := lt_trans hr₁ hρ1
    have h1 := ((hZ.hasDecay45_self.diff (hpt ρ z)
      (by rw [ϱ_hpt_of_pos hρ0]; exact hρ1)).hasFDerivAt).comp_hasDerivAt ρ (hasDerivAt_hpt z ρ)
    exact ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt ρ h1
  have hibp := tcg_ibp hd_f hf_int hA_int
  unfold outPrim primDz
  have hfun : (fun ρ : ℝ => ρ * (fderiv ℝ (Z 0) !₂[ρ, 0, z] !₂[ρ, 0, z]) 2) =
      fun ρ : ℝ => ρ ^ 2 * physPd (Z 0) 0 (hpt ρ z) 2 +
        z * (ρ * physPd (Z 0) 2 (hpt ρ z) 2) :=
    funext hlin
  have hpd2_def : (fun ρ : ℝ => ρ * fderiv ℝ (Z 0) (hpt ρ z) (coordinateVector 2) 2) =
      fun ρ : ℝ => ρ * physPd (Z 0) 2 (hpt ρ z) 2 := rfl
  rw [hfun, hpd2_def, integral_add hA_int (hg_int.const_mul z), integral_const_mul, hibp]
  have hhpt_eq : (fun x : ℝ => x * Z 0 (hpt x z) 2) = fun x : ℝ => x * Z 0 !₂[x, 0, z] 2 := rfl
  rw [hhpt_eq]
  ring

set_option maxHeartbeats 800000 in
private theorem physLap_cutPsi_eq (ν R : ℝ) {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    {r₁ B : ℝ} {Z : ℝ → Space → Space} (hZ : ValidPsiFieldWith r₁ B Z) (hr₁ : 0 < r₁)
    (τ : ℝ) {y : Space} (hy : r₁ < ϱ y) :
    physLap (cutPsi ν R χy Z τ) y =
      ((deriv (deriv (tcF0 ν R χy)) (ϱ y) + deriv (tcF0 ν R χy) (ϱ y) / ϱ y) *
          outPrim Z 0 (ϱ y) (y 2) +
        (2 * ϱ y * deriv (tcF0 ν R χy) (ϱ y) + 2 * tcF0 ν R χy (ϱ y)) *
          Z 0 (hpt (ϱ y) (y 2)) 2 +
        ϱ y * tcF0 ν R χy (ϱ y) * physPd (Z 0) 0 (hpt (ϱ y) (y 2)) 2 +
        tcF0 ν R χy (ϱ y) *
          outPrim (fun _ w => physPd2 (Z 0) 2 2 w) 0 (ϱ y) (y 2)) •
        (coordinateVector 2 : Space) := by
  set F := tcF0 ν R χy
  set u : Space → ℝ := fun y' => F (ϱ y') * outPrim Z 0 (ϱ y') (y' 2)
  set H : Space → ℝ := fun y' =>
    (deriv F (ϱ y') / ϱ y') * outPrim Z 0 (ϱ y') (y' 2) +
      F (ϱ y') * Z 0 (hpt (ϱ y') (y' 2)) 2
  let d : Fin 3 → Space → ℝ :=
    ![fun y' => y' 0 * H y',
      fun y' => y' 1 * H y',
      fun y' => F (ϱ y') * outPrim (fun _ w => physPd (Z 0) 2 w) 0 (ϱ y') (y' 2)]
  set U : Set Space := {y' : Space | r₁ < ϱ y'}
  have hU_open : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hU_nhds : U ∈ 𝓝 y := hU_open.mem_nhds hy
  have hF_c2 : ∀ y' ∈ U, ContDiffAt ℝ 2 F (ϱ y') := fun y' hy' =>
    tcle_f0_smooth hχ ν R (lt_trans hr₁ hy').ne'
  have hF_diff : ∀ y' ∈ U, DifferentiableAt ℝ F (ϱ y') := fun y' hy' =>
    (hF_c2 y' hy').differentiableAt (by norm_num)
  have hu_fderiv : ∀ y' ∈ U, HasFDerivAt u
      (outPrim Z 0 (ϱ y') (y' 2) • (deriv F (ϱ y') • ϱD y') +
        F (ϱ y') • ((ϱ y' * Z 0 (hpt (ϱ y') (y' 2)) 2) • ϱD y' +
          (-primDz Z 0 (ϱ y') (y' 2)) •
            (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ))) y' := by
    intro y' hy'
    have hρ' : 0 < ϱ y' := lt_trans hr₁ hy'
    have h1 := tcle_hasFDeriv_comp hρ' (hF_diff y' hy')
    have h2 := hZ.hasDecay45_self.hasFDerivAt_outPrim hr₁ hy'
    exact (h1.mul h2).congr_fderiv (by ext v; simp [add_comm])
  have hu_diff : ∀ y' ∈ U, DifferentiableAt ℝ u y' := fun y' hy' =>
    (hu_fderiv y' hy').differentiableAt
  have hd_eq : ∀ (j : Fin 3), ∀ y' ∈ U, fderiv ℝ u y' (coordinateVector j) = d j y' := by
    intro j y' hy'
    have hρ' : 0 < ϱ y' := lt_trans hr₁ hy'
    have hρ'ne : ϱ y' ≠ 0 := hρ'.ne'
    rw [(hu_fderiv y' hy').fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul,
      ϱD_apply, EuclideanSpace.coe_proj, primDz_eq_neg_outPrim_physPd]
    fin_cases j
    · simp [d, H, coordinateVector]; field_simp
    · simp [d, H, coordinateVector]; field_simp
    · simp [d, H, coordinateVector]
  have hρ : 0 < ϱ y := lt_trans hr₁ hy
  have hρne : ϱ y ≠ 0 := hρ.ne'
  have hdF_diff : DifferentiableAt ℝ (deriv F) (ϱ y) := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ F) (ϱ y) :=
      ((hF_c2 y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have : deriv F = fun r => fderiv ℝ F r 1 := rfl
    rw [this]
    exact h1.clm_apply (differentiableAt_const _)
  set κ : ℝ → ℝ := fun r => deriv F r / r with hκ
  have hκd : HasDerivAt κ (deriv (deriv F) (ϱ y) / ϱ y - deriv F (ϱ y) / ϱ y ^ 2) (ϱ y) := by
    have h := hdF_diff.hasDerivAt.div (hasDerivAt_id (ϱ y)) hρne
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hκ_comp : HasFDerivAt (fun y' : Space => κ (ϱ y'))
      ((deriv (deriv F) (ϱ y) / ϱ y - deriv F (ϱ y) / ϱ y ^ 2) • ϱD y) y :=
    hκd.comp_hasFDerivAt y (hasFDerivAt_ϱ (tcle_notaxis hρ))
  have hF_comp : HasFDerivAt (fun y' : Space => F (ϱ y')) (deriv F (ϱ y) • ϱD y) y :=
    tcle_hasFDeriv_comp hρ (hF_diff y hy)
  have hu0_fd := hZ.hasDecay45_self.hasFDerivAt_outPrim hr₁ hy
  have hz0_fd := hZ.hasDecay45_self.hasFDerivAt_hpt_eval2 hr₁ hy
  have hH_fd : HasFDerivAt H _ y := (hκ_comp.mul hu0_fd).add (hF_comp.mul hz0_fd)
  have hd2_fd : HasFDerivAt (d 2) _ y :=
    hF_comp.mul ((hZ.hasDecay45_physPd hr₁ 2).hasFDerivAt_outPrim hr₁ hy)
  have hdy : ∀ j : Fin 3, DifferentiableAt ℝ (d j) y := by
    intro j
    fin_cases j
    · exact (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt.mul
        hH_fd.differentiableAt
    · exact (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt.mul
        hH_fd.differentiableAt
    · exact hd2_fd.differentiableAt
  have hcut_eq : cutPsi ν R χy Z τ = fun y' => u y' • (coordinateVector 2 : Space) := by
    funext y'
    unfold cutPsi psiFld u
    rw [outPrim_congr_tau hZ.tau_indep, mul_smul]
  rw [hcut_eq, tcl_physLap_smul u d (coordinateVector 2 : Space) hU_nhds hu_diff hd_eq hdy]
  congr 1
  rw [Fin.sum_univ_three]
  have f0 := tcl_fd_mul 0 hH_fd.differentiableAt (coordinateVector 0)
  have f1 := tcl_fd_mul 1 hH_fd.differentiableAt (coordinateVector 1)
  change fderiv ℝ (fun y' : Space => y' 0 * H y') y (coordinateVector 0) +
      fderiv ℝ (fun y' : Space => y' 1 * H y') y (coordinateVector 1) +
      fderiv ℝ (d 2) y (coordinateVector 2) = _
  rw [f0, f1, hH_fd.fderiv, hd2_fd.fderiv]
  have hsq := tcl_sqsum hρ
  have hp22 : -primDz (fun _ w => physPd (Z 0) 2 w) 0 (ϱ y) (y 2) =
      outPrim (fun _ w => physPd2 (Z 0) 2 2 w) 0 (ϱ y) (y 2) := rfl
  simp only [add_apply, smul_apply, smul_eq_mul,
    ϱD_apply, EuclideanSpace.coe_proj, coordinateVector, PiLp.single_apply,
    Fin.isValue, ite_true, show ¬((1 : Fin 3) = 0) from by decide,
    show ¬((0 : Fin 3) = 1) from by decide,
    show ¬((2 : Fin 3) = 0) from by decide,
    show ¬((2 : Fin 3) = 1) from by decide,
    show ¬((0 : Fin 3) = 2) from by decide,
    show ¬((1 : Fin 3) = 2) from by decide, ite_false, hp22, H, hκ]
  field_simp
  linear_combination
    (deriv (deriv F) (ϱ y) * ϱ y * outPrim Z 0 (ϱ y) (y 2) -
      deriv F (ϱ y) * outPrim Z 0 (ϱ y) (y 2) +
      2 * deriv F (ϱ y) * (ϱ y) ^ 2 * Z 0 (hpt (ϱ y) (y 2)) 2 +
      F (ϱ y) * (ϱ y) ^ 2 * physPd (Z 0) 0 (hpt (ϱ y) (y 2)) 2) * hsq

/-- On `{y' : Space | r₁ < ϱ y'}`, `commPsi ν μ R χy Z τ y' = phiScalar ν R χy Z y' • e₂`. -/
theorem commPsi_eq_phiScalar (ν μ R : ℝ) {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    {r₁ B : ℝ} {Z : ℝ → Space → Space} (hZ : ValidPsiFieldWith r₁ B Z) (hr₁ : 0 < r₁)
    (τ : ℝ) {y : Space} (hy : r₁ < ϱ y) :
    commPsi ν μ R χy Z τ y = phiScalar ν R χy Z y • (coordinateVector 2 : Space) := by
  have hρ : 0 < ϱ y := lt_trans hr₁ hy
  set F := tcF0 ν R χy
  set r := ϱ y
  set z := y 2
  have hF_c2 : ContDiffAt ℝ 2 F r := tcle_f0_smooth hχ ν R hρ.ne'
  have hF_diff : DifferentiableAt ℝ F r := hF_c2.differentiableAt (by norm_num)
  -- 1. Time derivative of `cutPsi` is 0
  have ht_cut : deriv (fun t => cutPsi ν R χy Z t y) τ = 0 := by
    have hc : (fun t => cutPsi ν R χy Z t y) = fun _ => cutPsi ν R χy Z 0 y := by
      funext t; unfold cutPsi psiFld; rw [outPrim_congr_tau hZ.tau_indep]
    rw [hc, deriv_const]
  -- 2. Dilation derivative `fderiv ℝ (cutPsi ν R χy Z τ) y y`
  have hcut_tau : cutPsi ν R χy Z τ =
      fun y' => (F (ϱ y') * outPrim Z 0 (ϱ y') (y' 2)) • (coordinateVector 2 : Space) := by
    funext y'; unfold cutPsi psiFld; rw [outPrim_congr_tau hZ.tau_indep, mul_smul]
  have hF_comp : HasFDerivAt (fun y' : Space => F (ϱ y')) (deriv F r • ϱD y) y :=
    tcle_hasFDeriv_comp hρ hF_diff
  have hu0_fd := hZ.hasDecay45_self.hasFDerivAt_outPrim hr₁ hy
  have hcut_fd := (hF_comp.mul hu0_fd).smul_const (coordinateVector 2 : Space)
  have hD_cut : fderiv ℝ (cutPsi ν R χy Z τ) y y =
      (r * deriv F r * outPrim Z 0 r z +
        F r * (r ^ 2 * Z 0 (hpt r z) 2 - z * primDz Z 0 r z)) • (coordinateVector 2 : Space) := by
    rw [hcut_tau]
    change fderiv ℝ (fun y' => ((fun y'' => F (ϱ y'')) * fun y'' => outPrim Z 0 (ϱ y'') (y'' 2)) y' •
      (coordinateVector 2 : Space)) y y = _
    rw [hcut_fd.fderiv]
    have hϱy : ϱD y y = r := by
      rw [ϱD_apply, tcl_sqsum hρ]
      dsimp [r]
      field_simp
    simp only [ContinuousLinearMap.smulRight_apply, add_apply,
      smul_apply, smul_eq_mul, hϱy, EuclideanSpace.coe_proj]
    congr 1
    ring
  -- 3. Laplacian `physLap (cutPsi ν R χy Z τ) y`
  have hLap_cut := physLap_cutPsi_eq ν R hχ hZ hr₁ τ hy
  -- 4. `outPrim (physDmu ν (μ + 1) Z) τ r z`
  have hDZ_tau : physDmu ν (μ + 1) Z τ = physDmu ν (μ + 1) Z 0 := by
    funext w
    have hdt : (fun s => Z s w) = fun _ => Z 0 w := funext fun s => by rw [hZ.tau_indep s]
    unfold physDmu
    rw [hdt, hZ.tau_indep τ, deriv_const, deriv_const]
  have hout_DZ : outPrim (physDmu ν (μ + 1) Z) τ r z = outPrim (physDmu ν (μ + 1) Z) 0 r z := by
    unfold outPrim; rw [hDZ_tau]
  have i1 : IntegrableOn (fun ρ : ℝ => ρ * Z 0 !₂[ρ, 0, z] 2) (Ioi r) :=
    (hZ.hasDecay45_self.primData hr₁ hy z).1
  have hdt0 : ∀ ρ : ℝ, deriv (fun s => Z s !₂[ρ, 0, z]) 0 = 0 := by
    intro ρ
    have : (fun s => Z s !₂[ρ, 0, z]) = fun _ => Z 0 !₂[ρ, 0, z] :=
      funext fun s => by rw [hZ.tau_indep s]
    rw [this, deriv_const]
  have i2 : IntegrableOn (fun ρ : ℝ => ρ * (deriv (fun s => Z s !₂[ρ, 0, z]) 0) 2) (Ioi r) := by
    simp_rw [hdt0, PiLp.zero_apply, mul_zero]
    exact integrableOn_zero
  obtain ⟨i3, heuler⟩ := outPrim_euler_eq hZ hr₁ hy z
  have i4 : IntegrableOn (fun ρ : ℝ => ρ * (physLap (Z 0) !₂[ρ, 0, z]) 2) (Ioi r) :=
    ((hZ.hasDecay45_physLap hr₁).primData hr₁ hy z).1
  have hout_lin := tcle_outPrim_lin ν (μ + 1) Z 0 r z i1 i2 i3 i4
  have hout_t0 : outPrim (fun t y' => deriv (fun s => Z s y') t) 0 r z = 0 := by
    unfold outPrim
    simp_rw [hdt0, PiLp.zero_apply, mul_zero, integral_zero, neg_zero]
  have hout_D : outPrim (fun t y' => fderiv ℝ (Z t) y' y') 0 r z =
      r ^ 2 * Z 0 (hpt r z) 2 - 2 * outPrim Z 0 r z - z * primDz Z 0 r z := heuler
  have hout_L : outPrim (fun t y' => physLap (Z t) y') 0 r z =
      outPrim (fun _ w => physLap (Z 0) w) 0 r z := by
    unfold outPrim; rw [hZ.tau_indep 0]
  -- 5. Combine into `commPsi`
  unfold commPsi
  have hDW : physDmu ν (μ + 1) (cutPsi ν R χy Z) τ y =
      deriv (fun t => cutPsi ν R χy Z t y) τ -
        (1 / 2 : ℝ) • fderiv ℝ (cutPsi ν R χy Z τ) y y -
          ν • physLap (cutPsi ν R χy Z τ) y +
            (μ + 1 - 1 / 2) • cutPsi ν R χy Z τ y := rfl
  have hcut_DZ : cutPsi ν R χy (physDmu ν (μ + 1) Z) τ y =
      (F r * outPrim (physDmu ν (μ + 1) Z) τ r z) • (coordinateVector 2 : Space) := by
    unfold cutPsi psiFld; rw [mul_smul]
  have hcut_Z : cutPsi ν R χy Z τ y =
      (F r * outPrim Z 0 r z) • (coordinateVector 2 : Space) := by
    rw [hcut_tau]
  rw [hDW, hcut_DZ, ht_cut, hD_cut, hLap_cut, hcut_Z, hout_DZ, hout_lin, hout_t0, hout_D, hout_L]
  simp only [zero_sub, ← mul_smul, ← sub_smul, ← add_smul, ← neg_smul]
  congr 1
  unfold phiScalar tcB1 tcB2
  change _ = (-(1 / 2) * (r * deriv F r + 2 * F r) -
        ν * (deriv (deriv F) r + deriv F r / r)) * outPrim Z 0 r z +
      (-2 * ν * (r * deriv F r + F r)) * Z 0 (hpt r z) 2 -
      ν * (F r * r) * physPd (Z 0) 0 (hpt r z) 2 -
      ν * F r * outPrim (fun _ w => physPd2 (Z 0) 2 2 w) 0 r z +
      ν * F r * outPrim (fun _ w => physLap (Z 0) w) 0 r z
  ring

/-! ## 3. Linearity and transition-annulus derivative bound for `phiScalar` -/

theorem phiScalar_sub (ν R : ℝ) (χy : ℝ → ℝ) {r₁ B₁ B₂ : ℝ} {Z₁ Z₂ : ℝ → Space → Space}
    (hZ₁ : ValidPsiFieldWith r₁ B₁ Z₁) (hZ₂ : ValidPsiFieldWith r₁ B₂ Z₂) (hr₁ : 0 < r₁)
    {y' : Space} (hy' : r₁ < ϱ y') :
    phiScalar ν R χy Z₁ y' - phiScalar ν R χy Z₂ y' =
      phiScalar ν R χy (fun t w => Z₁ t w - Z₂ t w) y' := by
  set r := ϱ y'
  set z := y' 2
  have hu0 : outPrim Z₁ 0 r z - outPrim Z₂ 0 r z =
      outPrim (fun t w => Z₁ t w - Z₂ t w) 0 r z := by
    rw [outPrim_diff_eq Z₁ Z₂ 0 r z (hZ₁.hasDecay45_self.primData hr₁ hy' z).1
      (hZ₂.hasDecay45_self.primData hr₁ hy' z).1]
    rfl
  have hpd0 : physPd (fun w => Z₁ 0 w - Z₂ 0 w) 0 (hpt r z) 2 =
      physPd (Z₁ 0) 0 (hpt r z) 2 - physPd (Z₂ 0) 0 (hpt r z) 2 := by
    have hρ : 0 < r := lt_trans hr₁ hy'
    have h1 := hZ₁.hasDecay45_self.diff (hpt r z) (by rw [ϱ_hpt_of_pos hρ]; exact hy')
    have h2 := hZ₂.hasDecay45_self.diff (hpt r z) (by rw [ϱ_hpt_of_pos hρ]; exact hy')
    unfold physPd
    change (fderiv ℝ (Z₁ 0 - Z₂ 0) (hpt r z) (coordinateVector 0)) 2 = _
    rw [fderiv_sub h1 h2]
    rfl
  have hpd22_eq : ∀ w, r₁ < ϱ w →
      physPd2 (fun x => Z₁ 0 x - Z₂ 0 x) 2 2 w =
        physPd2 (Z₁ 0) 2 2 w - physPd2 (Z₂ 0) 2 2 w := by
    intro w hw
    have hev : physPd (fun x => Z₁ 0 x - Z₂ 0 x) 2 =ᶠ[𝓝 w]
        physPd (Z₁ 0) 2 - physPd (Z₂ 0) 2 := by
      have hopen : IsOpen {x : Space | r₁ < ϱ x} := isOpen_lt continuous_const continuous_ϱ
      filter_upwards [hopen.mem_nhds hw] with x hx
      unfold physPd
      change fderiv ℝ (Z₁ 0 - Z₂ 0) x (coordinateVector 2) = _
      rw [fderiv_sub (hZ₁.hasDecay45_self.diff x hx) (hZ₂.hasDecay45_self.diff x hx)]
      rfl
    unfold physPd2
    change fderiv ℝ (physPd (fun x => Z₁ 0 x - Z₂ 0 x) 2) w (coordinateVector 2) = _
    rw [hev.fderiv_eq, fderiv_sub ((hZ₁.hasDecay45_physPd hr₁ 2).diff w hw)
      ((hZ₂.hasDecay45_physPd hr₁ 2).diff w hw)]
    rfl
  have hlap_eq : ∀ w, r₁ < ϱ w →
      physLap (fun x => Z₁ 0 x - Z₂ 0 x) w =
        physLap (Z₁ 0) w - physLap (Z₂ 0) w := by
    intro w hw
    unfold physLap
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hev : physPd (fun x => Z₁ 0 x - Z₂ 0 x) j =ᶠ[𝓝 w]
        physPd (Z₁ 0) j - physPd (Z₂ 0) j := by
      have hopen : IsOpen {x : Space | r₁ < ϱ x} := isOpen_lt continuous_const continuous_ϱ
      filter_upwards [hopen.mem_nhds hw] with x hx
      unfold physPd
      change fderiv ℝ (Z₁ 0 - Z₂ 0) x (coordinateVector j) = _
      rw [fderiv_sub (hZ₁.hasDecay45_self.diff x hx) (hZ₂.hasDecay45_self.diff x hx)]
      rfl
    unfold physPd2
    change fderiv ℝ (physPd (fun x => Z₁ 0 x - Z₂ 0 x) j) w (coordinateVector j) = _
    rw [hev.fderiv_eq, fderiv_sub ((hZ₁.hasDecay45_physPd hr₁ j).diff w hw)
      ((hZ₂.hasDecay45_physPd hr₁ j).diff w hw)]
    rfl
  have hu22 : outPrim (fun _ w => physPd2 (Z₁ 0) 2 2 w) 0 r z -
      outPrim (fun _ w => physPd2 (Z₂ 0) 2 2 w) 0 r z =
      outPrim (fun _ w => physPd2 (fun x => Z₁ 0 x - Z₂ 0 x) 2 2 w) 0 r z := by
    rw [outPrim_diff_eq (fun _ w => physPd2 (Z₁ 0) 2 2 w) (fun _ w => physPd2 (Z₂ 0) 2 2 w) 0 r z
      ((hZ₁.hasDecay45_physPd2 hr₁ 2 2).primData hr₁ hy' z).1
      ((hZ₂.hasDecay45_physPd2 hr₁ 2 2).primData hr₁ hy' z).1]
    unfold outPrim
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    have hρ1 : r₁ < ρ := lt_trans hy' hρ
    have hρ0 : 0 < ρ := lt_trans hr₁ hρ1
    have hw : r₁ < ϱ (hpt ρ z) := by rw [ϱ_hpt_of_pos hρ0]; exact hρ1
    dsimp only
    rw [← hpd22_eq (hpt ρ z) hw]
    rfl
  have huL : outPrim (fun _ w => physLap (Z₁ 0) w) 0 r z -
      outPrim (fun _ w => physLap (Z₂ 0) w) 0 r z =
      outPrim (fun _ w => physLap (fun x => Z₁ 0 x - Z₂ 0 x) w) 0 r z := by
    rw [outPrim_diff_eq (fun _ w => physLap (Z₁ 0) w) (fun _ w => physLap (Z₂ 0) w) 0 r z
      ((hZ₁.hasDecay45_physLap hr₁).primData hr₁ hy' z).1
      ((hZ₂.hasDecay45_physLap hr₁).primData hr₁ hy' z).1]
    unfold outPrim
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    have hρ1 : r₁ < ρ := lt_trans hy' hρ
    have hρ0 : 0 < ρ := lt_trans hr₁ hρ1
    have hw : r₁ < ϱ (hpt ρ z) := by rw [ϱ_hpt_of_pos hρ0]; exact hρ1
    dsimp only
    rw [← hlap_eq (hpt ρ z) hw]
    rfl
  unfold phiScalar
  rw [hpd0, ← hu0, ← hu22, ← huL]
  simp only [PiLp.sub_apply]
  ring

set_option maxHeartbeats 800000 in
theorem fderiv_phiScalar_bound {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν R B : ℝ) (Z : ℝ → Space → Space),
      0 < ν → ν ≤ 1 → 1 ≤ R →
      ValidPsiFieldWith ((23 / 24 : ℝ) * (R * Real.sqrt ν)) B Z →
      ∀ y : Space, y ∈ streamAnn ν R →
        DifferentiableAt ℝ (phiScalar ν R χy Z) y ∧
        ‖fderiv ℝ (phiScalar ν R χy Z) y‖ ≤ C * B * ((R * Real.sqrt ν)⁻¹) ^ 5 := by
  obtain ⟨C0, hC0, hcoef⟩ := tcCoeff χy hχ
  obtain ⟨C1, hC1, hder⟩ := wgy_coeff_deriv hχ
  obtain ⟨M, hM0, hM⟩ := wgyc_profile χy hχ
  refine ⟨80 * (C0 + C1 + M), by positivity, ?_⟩
  intro ν R B Z hν hν1 hR1 hZ y hyann
  have hR : 0 < R := by linarith
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hL : 0 < L := by rw [hLdef]; positivity
  have hLsq : ν * R ^ 2 = L ^ 2 := by rw [hLdef, mul_pow, Real.sq_sqrt hν.le]; ring
  set r₁ : ℝ := (23 / 24 : ℝ) * L with hr1def
  have hr₁ : 0 < r₁ := by rw [hr1def]; positivity
  set s : ℝ := L⁻¹ with hsdef
  have hs0 : 0 < s := inv_pos.2 hL
  have hsL : s * L = 1 := inv_mul_cancel₀ hL.ne'
  obtain ⟨hr1, hr2'⟩ := hyann
  have hQ2L : R * Real.sqrt (5 * ν / 4) ≤ 2 * L := by
    rw [hLdef]
    have : Real.sqrt (5 * ν / 4) ≤ 2 * Real.sqrt ν := by
      rw [show (2 : ℝ) * Real.sqrt ν = Real.sqrt (2 ^ 2 * ν) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    calc R * Real.sqrt (5 * ν / 4) ≤ R * (2 * Real.sqrt ν) := by gcongr
      _ = 2 * (R * Real.sqrt ν) := by ring
  have hr2 : ϱ y ≤ 2 * L := hr2'.trans hQ2L
  have hy : r₁ < ϱ y := by rw [hr1def]; linarith
  have hρ : 0 < ϱ y := lt_trans hr₁ hy
  have hsr1 : 1 ≤ s * ϱ y := by
    calc 1 = s * L := hsL.symm
      _ ≤ s * ϱ y := by gcongr
  have hsr2 : s * ϱ y ≤ 2 := by
    calc s * ϱ y ≤ s * (2 * L) := by gcongr
      _ = 2 := by rw [mul_left_comm, hsL]; ring
  have hνs : ν * s ^ 2 ≤ 1 := by
    have h1 : ν * R ^ 2 * s ^ 2 = 1 := by
      rw [hLsq, show L ^ 2 * s ^ 2 = (s * L) ^ 2 by ring, hsL]; norm_num
    have hR2 : 1 ≤ R ^ 2 := by nlinarith
    have : ν * s ^ 2 ≤ ν * R ^ 2 * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hR2 hν.le
      nlinarith [sq_nonneg s]
    linarith
  have hys : (ϱ y)⁻¹ ≤ s := inv_anti₀ hL hr1
  have hr1s : r₁⁻¹ ≤ 2 * s := by
    rw [hr1def, mul_inv, ← hsdef]
    nlinarith
  have hrpow_le : ∀ k : ℕ, (ϱ y) ^ (-(k : ℝ)) ≤ s ^ k := by
    intro k
    rw [Real.rpow_neg hρ.le, Real.rpow_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hρ.le) hys k
  have hrp2 : (ϱ y) ^ (-2 : ℝ) ≤ s ^ 2 := by simpa using hrpow_le 2
  have hrp3 : (ϱ y) ^ (-3 : ℝ) ≤ s ^ 3 := by simpa using hrpow_le 3
  have hrp4 : (ϱ y) ^ (-4 : ℝ) ≤ s ^ 4 := by simpa using hrpow_le 4
  have hrp5 : (ϱ y) ^ (-5 : ℝ) ≤ s ^ 5 := by simpa using hrpow_le 5
  -- Cutoff coefficient bounds at `ϱ y`
  obtain ⟨_, _, cB1, cB2⟩ := hcoef ν R hν hν1 hR1 (ϱ y) hr1 hr2'
  obtain ⟨_, _, b1, b2, _, _, hB1, hB2, _, _, bb1, bb2⟩ := hder ν R hν hν1 hR1 (ϱ y) hr1 hr2
  have hf_scale : tcF0 ν R χy = fun r => s ^ 2 * tcF0 1 1 χy (s * r) :=
    wgyc_f_scale ν R χy hL hLsq
  have hf1_scale : deriv (tcF0 ν R χy) = fun r => s ^ 2 * (s * deriv (tcF0 1 1 χy) (s * r)) := by
    rw [hf_scale]; exact wgyc_e1 _ _ _
  obtain ⟨_, _, _, n0, n1, _, _⟩ := hM (s * ϱ y) ⟨hsr1, hsr2⟩
  have bF0 : |tcF0 ν R χy (ϱ y)| ≤ M * s ^ 2 := by
    rw [hf_scale]; simp only; rw [abs_mul, abs_of_pos (pow_pos hs0 2), mul_comm]
    exact mul_le_mul_of_nonneg_right n0 (by positivity)
  have bF1 : |deriv (tcF0 ν R χy) (ϱ y)| ≤ M * s ^ 3 := by
    rw [hf1_scale]; simp only; rw [abs_mul, abs_mul, abs_of_pos (pow_pos hs0 2), abs_of_pos hs0]
    calc s ^ 2 * (s * |deriv (tcF0 1 1 χy) (s * ϱ y)|) ≤ s ^ 2 * (s * M) := by gcongr
      _ = M * s ^ 3 := by ring
  have hF_hd : HasDerivAt (tcF0 ν R χy) (deriv (tcF0 ν R χy) (ϱ y)) (ϱ y) :=
    ((tcle_f0_smooth hχ ν R hρ.ne').differentiableAt (by norm_num)).hasDerivAt
  -- Term 1: `tcB1 * outPrim Z`
  obtain ⟨L1, hL1, hL1b⟩ :=
    hZ.hasDecay45_self.hasFDerivAt_coeff_mul_outPrim hr₁ hy hB1
  -- Term 2: `tcB2 * Z 0 (hpt (ϱ y') (y' 2)) 2`
  obtain ⟨L2, hL2, hL2b⟩ :=
    hZ.hasDecay45_self.hasFDerivAt_coeff_mul_hpt hr₁ hy hB2
  -- Term 3: `(-ν * (tcF0 r * r)) * physPd (Z 0) 0`
  have hg3_hd : HasDerivAt (fun r => -ν * (tcF0 ν R χy r * r))
      (-ν * (deriv (tcF0 ν R χy) (ϱ y) * ϱ y + tcF0 ν R χy (ϱ y) * 1)) (ϱ y) :=
    (hF_hd.mul (hasDerivAt_id (ϱ y))).const_mul (-ν)
  obtain ⟨L3, hL3, hL3b⟩ :=
    (hZ.hasDecay45_physPd hr₁ 0).hasFDerivAt_coeff_mul_hpt hr₁ hy hg3_hd
  -- Term 4: `(-ν * tcF0 r) * outPrim (physPd2 (Z 0) 2 2)`
  have hg4_hd : HasDerivAt (fun r => -ν * tcF0 ν R χy r)
      (-ν * deriv (tcF0 ν R χy) (ϱ y)) (ϱ y) :=
    hF_hd.const_mul (-ν)
  obtain ⟨L4, hL4, hL4b⟩ :=
    (hZ.hasDecay45_physPd2 hr₁ 2 2).hasFDerivAt_coeff_mul_outPrim hr₁ hy hg4_hd
  -- Term 5: `(ν * tcF0 r) * outPrim (physLap (Z 0))`
  have hg5_hd : HasDerivAt (fun r => ν * tcF0 ν R χy r)
      (ν * deriv (tcF0 ν R χy) (ϱ y)) (ϱ y) :=
    hF_hd.const_mul ν
  obtain ⟨L5, hL5, hL5b⟩ :=
    (hZ.hasDecay45_physLap hr₁).hasFDerivAt_coeff_mul_outPrim hr₁ hy hg5_hd
  have hphi_eq : phiScalar ν R χy Z = fun y' =>
      (tcB1 ν R χy (ϱ y') * outPrim Z 0 (ϱ y') (y' 2) +
        tcB2 ν R χy (ϱ y') * Z 0 (hpt (ϱ y') (y' 2)) 2 +
        (-ν * (tcF0 ν R χy (ϱ y') * ϱ y')) * physPd (Z 0) 0 (hpt (ϱ y') (y' 2)) 2 +
        (-ν * tcF0 ν R χy (ϱ y')) * outPrim (fun _ w => physPd2 (Z 0) 2 2 w) 0 (ϱ y') (y' 2)) +
      (ν * tcF0 ν R χy (ϱ y')) * outPrim (fun _ w => physLap (Z 0) w) 0 (ϱ y') (y' 2) := by
    funext y'; unfold phiScalar; ring
  have h_all : HasFDerivAt (phiScalar ν R χy Z) ((((L1 + L2) + L3) + L4) + L5) y := by
    rw [hphi_eq]
    exact (((hL1.add hL2).add hL3).add hL4).add hL5
  refine ⟨h_all.differentiableAt, ?_⟩
  rw [h_all.fderiv]
  have hB0 := hZ.B_nonneg
  -- Bound each `‖L_i‖`
  have t1 : ‖L1‖ ≤ (C1 + 2 * C0) * B * s ^ 5 := by
    calc ‖L1‖ ≤ |b1| * B * (ϱ y) ^ (-2 : ℝ) + |tcB1 ν R χy (ϱ y)| * (B + B) * (ϱ y) ^ (-3 : ℝ) := hL1b
      _ ≤ (C1 * s ^ 3) * B * s ^ 2 + (C0 * s ^ 2) * (B + B) * s ^ 3 := by gcongr
      _ = (C1 + 2 * C0) * B * s ^ 5 := by ring
  have t2 : ‖L2‖ ≤ (C1 + 2 * C0) * B * s ^ 5 := by
    calc ‖L2‖ ≤ |b2| * B * (ϱ y) ^ (-4 : ℝ) + 2 * |tcB2 ν R χy (ϱ y)| * B * (ϱ y) ^ (-5 : ℝ) := hL2b
      _ ≤ (C1 * s) * B * s ^ 4 + 2 * C0 * B * s ^ 5 := by gcongr
      _ = (C1 + 2 * C0) * B * s ^ 5 := by ring
  have bg3_val : |-ν * (tcF0 ν R χy (ϱ y) * ϱ y)| ≤ 2 * ν * M * s := by
    rw [abs_mul, abs_neg, abs_of_pos hν, abs_mul, abs_of_pos hρ]
    calc ν * (|tcF0 ν R χy (ϱ y)| * ϱ y)
        ≤ ν * (M * s ^ 2 * ϱ y) := by gcongr
      _ = ν * M * s * (s * ϱ y) := by ring
      _ ≤ ν * M * s * 2 := by gcongr
      _ = 2 * ν * M * s := by ring
  have bg3_der : |-ν * (deriv (tcF0 ν R χy) (ϱ y) * ϱ y + tcF0 ν R χy (ϱ y) * 1)| ≤
      3 * ν * M * s ^ 2 := by
    rw [abs_mul, abs_neg, abs_of_pos hν, mul_one]
    have hd_rho : |deriv (tcF0 ν R χy) (ϱ y) * ϱ y| ≤ 2 * M * s ^ 2 := by
      rw [abs_mul, abs_of_pos hρ]
      calc |deriv (tcF0 ν R χy) (ϱ y)| * ϱ y ≤ (M * s ^ 3) * ϱ y := by gcongr
        _ = M * s ^ 2 * (s * ϱ y) := by ring
        _ ≤ M * s ^ 2 * 2 := by gcongr
        _ = 2 * M * s ^ 2 := by ring
    have htri : |deriv (tcF0 ν R χy) (ϱ y) * ϱ y + tcF0 ν R χy (ϱ y)| ≤
        2 * M * s ^ 2 + M * s ^ 2 :=
      (abs_add_le _ _).trans (add_le_add hd_rho bF0)
    calc ν * |deriv (tcF0 ν R χy) (ϱ y) * ϱ y + tcF0 ν R χy (ϱ y)|
        ≤ ν * (2 * M * s ^ 2 + M * s ^ 2) := by gcongr
      _ = 3 * ν * M * s ^ 2 := by ring
  have t3 : ‖L3‖ ≤ 14 * M * B * s ^ 5 := by
    calc ‖L3‖
        ≤ |-ν * (deriv (tcF0 ν R χy) (ϱ y) * ϱ y + tcF0 ν R χy (ϱ y) * 1)| *
            (B * r₁⁻¹) * (ϱ y) ^ (-4 : ℝ) +
          2 * |-ν * (tcF0 ν R χy (ϱ y) * ϱ y)| * (B * r₁⁻¹) * (ϱ y) ^ (-5 : ℝ) := hL3b
      _ ≤ (3 * ν * M * s ^ 2) * (B * (2 * s)) * s ^ 4 +
            2 * (2 * ν * M * s) * (B * (2 * s)) * s ^ 5 := by gcongr
      _ = 14 * M * B * s ^ 5 * (ν * s ^ 2) := by ring
      _ ≤ 14 * M * B * s ^ 5 * 1 := by gcongr
      _ = 14 * M * B * s ^ 5 := mul_one _
  have bg4_val : |-ν * tcF0 ν R χy (ϱ y)| ≤ ν * M * s ^ 2 := by
    rw [abs_mul, abs_neg, abs_of_pos hν, mul_assoc]; gcongr
  have bg4_der : |-ν * deriv (tcF0 ν R χy) (ϱ y)| ≤ ν * M * s ^ 3 := by
    rw [abs_mul, abs_neg, abs_of_pos hν, mul_assoc]; gcongr
  have hr1s_sq : (r₁⁻¹) ^ 2 ≤ 4 * s ^ 2 := by
    calc (r₁⁻¹) ^ 2 ≤ (2 * s) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hr₁.le) hr1s 2
      _ = 4 * s ^ 2 := by ring
  have t4 : ‖L4‖ ≤ 12 * M * B * s ^ 5 := by
    calc ‖L4‖
        ≤ |-ν * deriv (tcF0 ν R χy) (ϱ y)| * (B * (r₁⁻¹) ^ 2) * (ϱ y) ^ (-2 : ℝ) +
          |-ν * tcF0 ν R χy (ϱ y)| * (B * (r₁⁻¹) ^ 2 + B * (r₁⁻¹) ^ 2) * (ϱ y) ^ (-3 : ℝ) := hL4b
      _ ≤ (ν * M * s ^ 3) * (B * (4 * s ^ 2)) * s ^ 2 +
            (ν * M * s ^ 2) * (B * (4 * s ^ 2) + B * (4 * s ^ 2)) * s ^ 3 := by gcongr
      _ = 12 * M * B * s ^ 5 * (ν * s ^ 2) := by ring
      _ ≤ 12 * M * B * s ^ 5 * 1 := by gcongr
      _ = 12 * M * B * s ^ 5 := mul_one _
  have bg5_val : |ν * tcF0 ν R χy (ϱ y)| ≤ ν * M * s ^ 2 := by
    rw [abs_mul, abs_of_pos hν, mul_assoc]; gcongr
  have bg5_der : |ν * deriv (tcF0 ν R χy) (ϱ y)| ≤ ν * M * s ^ 3 := by
    rw [abs_mul, abs_of_pos hν, mul_assoc]; gcongr
  have t5 : ‖L5‖ ≤ 36 * M * B * s ^ 5 := by
    calc ‖L5‖
        ≤ |ν * deriv (tcF0 ν R χy) (ϱ y)| * (3 * B * (r₁⁻¹) ^ 2) * (ϱ y) ^ (-2 : ℝ) +
          |ν * tcF0 ν R χy (ϱ y)| * (3 * B * (r₁⁻¹) ^ 2 + 3 * B * (r₁⁻¹) ^ 2) *
            (ϱ y) ^ (-3 : ℝ) := hL5b
      _ ≤ (ν * M * s ^ 3) * (3 * B * (4 * s ^ 2)) * s ^ 2 +
            (ν * M * s ^ 2) * (3 * B * (4 * s ^ 2) + 3 * B * (4 * s ^ 2)) * s ^ 3 := by gcongr
      _ = 36 * M * B * s ^ 5 * (ν * s ^ 2) := by ring
      _ ≤ 36 * M * B * s ^ 5 * 1 := by gcongr
      _ = 36 * M * B * s ^ 5 := mul_one _
  have hsum : ‖(((L1 + L2) + L3) + L4) + L5‖ ≤ ‖L1‖ + ‖L2‖ + ‖L3‖ + ‖L4‖ + ‖L5‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  have p0 : 0 ≤ C0 * B * s ^ 5 := by positivity
  have p1 : 0 ≤ C1 * B * s ^ 5 := by positivity
  have pM : 0 ≤ M * B * s ^ 5 := by positivity
  linarith [hsum, t1, t2, t3, t4, t5]

/-! ## 4. Verification of `ValidPsiFieldWith` for `D = Z₁ - Z₂` and `Z₂ = newtonX0` -/

private theorem mpVdIter_norm_le (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℂ) (ρo ρi : ℝ), -(1 / 4) < μ.re → 0 ≤ ρo → ρo < ρi →
      ∀ (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ),
        (∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
      ∀ (xo : Space), ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ (m : Fin n → Space) (i : Fin 3)
        (p : ℝ × ((ℝ × ℝ) × ℝ)), p.1 ∈ Ioo (0 : ℝ) 1 →
        ‖mpVdIter n μ G p xo m i‖ ≤
          C * (ρi - ρo) ^ (-4 - (n : ℝ)) * (∏ l : Fin n, ‖m l‖) *
            IIIa.tensorNorm (G p.2.1 p.2.2) := by
  obtain ⟨CK, hCK⟩ := IIIa.sepKernelBounds n
  refine ⟨18 * max CK 0, by positivity, ?_⟩
  intro μ ρo ρi hμ hρo hρ G hGs xo hxo m i p hp
  obtain ⟨l, w⟩ := p
  simp only at hp
  have hD : 0 < ρi - ρo := by linarith
  have hDp : 0 ≤ (ρi - ρo) ^ (-4 - (n : ℝ)) := Real.rpow_nonneg hD.le _
  have hCM0 : 0 ≤ max CK 0 := le_max_right _ _
  have hprod0 : 0 ≤ ∏ idx : Fin n, ‖m idx‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have htn0 : 0 ≤ IIIa.tensorNorm (G w.1 w.2) := tn_nonneg _
  by_cases hw : Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) ≤ ρo
  · have hgap := IIIa.mp_gap ρo ρi xo xo hxo l hp w hw
    simp only [sub_self, norm_zero, sub_zero] at hgap
    set u0 : Space := xo - l • IIIa.mpV3 w
    have hnorm : ρi - ρo ≤ ‖u0‖ := hgap.trans (IIIa.rho_le_norm u0)
    have hne : u0 ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hnorm; linarith
    have hw1 := IIIa.mp_norm_cpow_le μ hμ l hp
    unfold mpVdIter
    rw [norm_mul, norm_mul, show ‖(-2 : ℂ)‖ = 2 by simp]
    have hsum : ‖∑ j : Fin 3, ∑ k : Fin 3,
        ((iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK0 i j x) u0
          (Fin.snoc m (coordinateVector k)) : ℝ) : ℂ) * ((G w.1 w.2 j k : ℝ) : ℂ)‖ ≤
        9 * (max CK 0 * (ρi - ρo) ^ (-4 - (n : ℝ)) * (∏ idx : Fin n, ‖m idx‖) *
          IIIa.tensorNorm (G w.1 w.2)) := by
      have hjk : ∀ j k : Fin 3,
          ‖((iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK0 i j x) u0
            (Fin.snoc m (coordinateVector k)) : ℝ) : ℂ) * ((G w.1 w.2 j k : ℝ) : ℂ)‖ ≤
          max CK 0 * (ρi - ρo) ^ (-4 - (n : ℝ)) * (∏ idx : Fin n, ‖m idx‖) *
            IIIa.tensorNorm (G w.1 w.2) := by
        intro j k
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs]
        have h1 := (iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK0 i j x) u0).le_opNorm
          (Fin.snoc m (coordinateVector k))
        rw [Fin.prod_univ_castSucc] at h1
        simp only [Fin.snoc_castSucc, Fin.snoc_last, IIIa.mp_norm_e, mul_one] at h1
        have h2 := (hCK u0 hne i j).2.1
        have hpow : ‖u0‖ ^ (-4 - (n : ℝ)) ≤ (ρi - ρo) ^ (-4 - (n : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hD hnorm (by have := n.cast_nonneg (α := ℝ); linarith)
        have hK_le : ‖iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK0 i j x) u0‖ ≤
            max CK 0 * (ρi - ρo) ^ (-4 - (n : ℝ)) := by
          calc ‖iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK0 i j x) u0‖
              ≤ CK * ‖u0‖ ^ (-4 - (n : ℝ)) := h2
            _ ≤ max CK 0 * ‖u0‖ ^ (-4 - (n : ℝ)) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
            _ ≤ max CK 0 * (ρi - ρo) ^ (-4 - (n : ℝ)) :=
                mul_le_mul_of_nonneg_left hpow hCM0
        have h1' : ‖iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK0 i j x) u0
            (Fin.snoc m (coordinateVector k))‖ ≤
            max CK 0 * (ρi - ρo) ^ (-4 - (n : ℝ)) * ∏ idx : Fin n, ‖m idx‖ :=
          h1.trans (mul_le_mul_of_nonneg_right hK_le hprod0)
        have hG := IIIa.mp_entry_le (G w.1 w.2) j k
        exact mul_le_mul h1' hG (abs_nonneg _) (mul_nonneg (mul_nonneg hCM0 hDp) hprod0)
      refine (norm_sum_le _ _).trans ?_
      have hj : ∀ j : Fin 3,
          ‖∑ k : Fin 3, ((iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK0 i j x) u0
            (Fin.snoc m (coordinateVector k)) : ℝ) : ℂ) * ((G w.1 w.2 j k : ℝ) : ℂ)‖ ≤
          3 * (max CK 0 * (ρi - ρo) ^ (-4 - (n : ℝ)) * (∏ idx : Fin n, ‖m idx‖) *
            IIIa.tensorNorm (G w.1 w.2)) := by
        intro j
        refine (norm_sum_le _ _).trans ?_
        calc ∑ k : Fin 3, _ ≤ ∑ _k : Fin 3, _ := Finset.sum_le_sum fun k _ => hjk j k
          _ = _ := by simp [Finset.sum_const]
      calc ∑ j : Fin 3, _ ≤ ∑ _j : Fin 3, _ := Finset.sum_le_sum fun j _ => hj j
        _ = _ := by simp [Finset.sum_const]; ring
    have hmul := mul_le_mul hw1 hsum (norm_nonneg _) zero_le_one
    calc 2 * (‖(l : ℂ) ^ (2 * μ + 2)‖ * ‖∑ j : Fin 3, ∑ k : Fin 3, _‖)
        ≤ 2 * (1 * (9 * (max CK 0 * (ρi - ρo) ^ (-4 - (n : ℝ)) * (∏ idx : Fin n, ‖m idx‖) *
            IIIa.tensorNorm (G w.1 w.2)))) := mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 18 * max CK 0 * (ρi - ρo) ^ (-4 - (n : ℝ)) * (∏ idx : Fin n, ‖m idx‖) *
            IIIa.tensorNorm (G w.1 w.2) := by ring
  · have hw' : ρo < Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) := lt_of_not_ge hw
    have h0 : G w.1 w.2 = 0 := hGs _ _ hw'
    have hV0 : mpVdIter n μ G (l, w) xo m i = 0 := by
      unfold mpVdIter
      simp [h0, Matrix.zero_apply]
    rw [hV0, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hDp) hprod0) htn0

private theorem iteratedFDeriv_sepVmu0_le (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℂ) (ρo ρi : ℝ), -(1 / 4) < μ.re → 0 ≤ ρo → ρo < ρi →
      ∀ (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ),
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume →
      ∀ (xo : Space), ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) →
        ‖iteratedFDeriv ℝ n (IIIa.sepVmu0 μ G) xo‖ ≤
          C * (ρi - ρo) ^ (-4 - (n : ℝ)) * ∫ w : (ℝ × ℝ) × ℝ, IIIa.tensorNorm (G w.1 w.2) := by
  obtain ⟨C0, hC0, hpt⟩ := mpVdIter_norm_le n
  refine ⟨C0, hC0, ?_⟩
  intro μ ρo ρi hμ hρo hρ G hGm hGs hint xo hxo
  have hD : 0 < ρi - ρo := by linarith
  set N0 : ℝ := ∫ w : (ℝ × ℝ) × ℝ, IIIa.tensorNorm (G w.1 w.2) with hN0
  have hN0_nn : 0 ≤ N0 := integral_nonneg fun _ => Real.sqrt_nonneg _
  obtain ⟨_, hVf⟩ := mp_V_iter_eval n μ hμ ρo ρi hρo hρ G hGm hGs hint xo hxo
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have hprod0 : 0 ≤ ∏ l : Fin n, ‖m l‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) hprod0)).2 fun i => ?_
  obtain ⟨hVe, hVi⟩ := hVf m i
  rw [hVe]
  set K := C0 * (ρi - ρo) ^ (-4 - (n : ℝ)) * ∏ l : Fin n, ‖m l‖
  have hB : Integrable (fun p : ℝ × ((ℝ × ℝ) × ℝ) => K * IIIa.tensorNorm (G p.2.1 p.2.2))
      IIIa.mpRho2 := (IIIa.mp_tn_integrable G hint).const_mul K
  have hnorm : ‖∫ p, mpVdIter n μ G p xo m i ∂IIIa.mpRho2‖ ≤
      ∫ p, K * IIIa.tensorNorm (G p.2.1 p.2.2) ∂IIIa.mpRho2 := by
    refine norm_integral_le_of_norm_le hB ?_
    filter_upwards [IIIa.mpRho2_ae_mem] with p hp
    exact hpt μ ρo ρi hμ hρo hρ G hGs xo hxo m i p hp
  have hI : ∫ p, K * IIIa.tensorNorm (G p.2.1 p.2.2) ∂IIIa.mpRho2 = K * N0 := by
    rw [integral_const_mul]
    congr 1
    have := integral_prod_mul (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (ν := (volume : Measure ((ℝ × ℝ) × ℝ)))
      (fun _ => (1 : ℝ)) (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2))
    simp only [one_mul, integral_const, smul_eq_mul] at this
    unfold IIIa.mpRho2
    rw [hN0]
    simpa using this
  calc ‖∫ p, mpVdIter n μ G p xo m i ∂IIIa.mpRho2‖
      ≤ K * N0 := hI ▸ hnorm
    _ = C0 * (ρi - ρo) ^ (-4 - (n : ℝ)) * N0 * ∏ l : Fin n, ‖m l‖ := by unfold K; ring

private theorem gap_bounds_of_gt {ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) {y' : Space}
    (hy' : (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν) < ϱ y') :
    Real.sqrt (5 * ν / 6) < ε * ϱ y' ∧
    Real.sqrt ν / 24 ≤ ε * ϱ y' - Real.sqrt (5 * ν / 6) ∧
    (ε * ϱ y') / 23 ≤ ε * ϱ y' - Real.sqrt (5 * ν / 6) := by
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hρo_le : Real.sqrt (5 * ν / 6) ≤ (11 / 12 : ℝ) * Real.sqrt ν := by
    rw [show (11 / 12 : ℝ) * Real.sqrt ν = Real.sqrt ((11 / 12) ^ 2 * ν) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hεy : (23 / 24 : ℝ) * Real.sqrt ν < ε * ϱ y' := by
    have h1 := mul_lt_mul_of_pos_left hy' hε
    have h2 : ε * ((23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν)) = (23 / 24 : ℝ) * Real.sqrt ν := by
      calc ε * ((23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν))
          = (23 / 24 : ℝ) * (ε * ε⁻¹) * Real.sqrt ν := by ring
        _ = (23 / 24 : ℝ) * Real.sqrt ν := by rw [mul_inv_cancel₀ hε.ne', mul_one]
    linarith
  refine ⟨by linarith, by linarith, by linarith⟩

private theorem d_rpow_bound (n : ℕ) {ν ε ρ d : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hε : 0 < ε) (hρ : 0 < ρ) (hd1 : Real.sqrt ν / 24 ≤ d) (hd2 : (ε * ρ) / 23 ≤ d) :
    ε ^ (3 + n) * (d ^ (-6 - (n : ℝ)) + d ^ (-5 - (n : ℝ))) ≤
      (24 ^ 2 + 24) * (23 : ℝ) ^ (4 + n) * (1 + ν⁻¹) ^ 2 * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) := by
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd1
  have h1nu : 1 ≤ 1 + ν⁻¹ := le_add_of_nonneg_right (inv_nonneg.2 hν.le)
  have hsν_inv : (Real.sqrt ν)⁻¹ ≤ 1 + ν⁻¹ := by
    have hsq : Real.sqrt ν ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hν1
    have hle : Real.sqrt ν ^ 2 ≤ Real.sqrt ν * 1 := by
      nlinarith [Real.sqrt_pos.2 hν, hsq]
    rw [Real.sq_sqrt hν.le, mul_one] at hle
    have := inv_anti₀ hν hle
    linarith [inv_nonneg.2 hν.le]
  have hd_inv : d⁻¹ ≤ 24 * (1 + ν⁻¹) := by
    have h1 : d⁻¹ ≤ (Real.sqrt ν / 24)⁻¹ := inv_anti₀ (by positivity) hd1
    rw [inv_div] at h1
    calc d⁻¹ ≤ 24 / Real.sqrt ν := h1
      _ = 24 * (Real.sqrt ν)⁻¹ := div_eq_mul_inv _ _
      _ ≤ 24 * (1 + ν⁻¹) := by gcongr
  have hd_inv2 : (d⁻¹) ^ 2 ≤ 24 ^ 2 * (1 + ν⁻¹) ^ 2 := by
    calc (d⁻¹) ^ 2 ≤ (24 * (1 + ν⁻¹)) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hd0.le) hd_inv 2
      _ = 24 ^ 2 * (1 + ν⁻¹) ^ 2 := by ring
  have hd_inv1' : d⁻¹ ≤ 24 * (1 + ν⁻¹) ^ 2 := by
    calc d⁻¹ ≤ 24 * (1 + ν⁻¹) * 1 := by rw [mul_one]; exact hd_inv
      _ ≤ 24 * (1 + ν⁻¹) * (1 + ν⁻¹) := by gcongr
      _ = 24 * (1 + ν⁻¹) ^ 2 := by ring
  have h5 : d ^ (-5 - (n : ℝ)) = d⁻¹ * d ^ (-4 - (n : ℝ)) := by
    rw [show (-5 - (n : ℝ)) = -1 + (-4 - (n : ℝ)) by ring, Real.rpow_add hd0, Real.rpow_neg_one]
  have h6 : d ^ (-6 - (n : ℝ)) = (d⁻¹) ^ 2 * d ^ (-4 - (n : ℝ)) := by
    rw [show (-6 - (n : ℝ)) = -2 + (-4 - (n : ℝ)) by ring, Real.rpow_add hd0,
      show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hd0.le, Real.rpow_natCast, inv_pow]
  have hd4 : d ^ (-4 - (n : ℝ)) ≤ (23 : ℝ) ^ (4 + n) * ε ^ (-4 - (n : ℝ)) * ρ ^ (-4 - (n : ℝ)) := by
    have h1 : d ^ (-4 - (n : ℝ)) ≤ ((ε * ρ) / 23) ^ (-4 - (n : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hd2 (by have := n.cast_nonneg (α := ℝ); linarith)
    have h2 : ((ε * ρ) / 23) ^ (-4 - (n : ℝ)) =
        (23 : ℝ) ^ (4 + n) * ε ^ (-4 - (n : ℝ)) * ρ ^ (-4 - (n : ℝ)) := by
      rw [div_eq_mul_inv, Real.mul_rpow (mul_nonneg hε.le hρ.le) (by norm_num),
        Real.mul_rpow hε.le hρ.le, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      have he : -(-4 - (n : ℝ)) = ((4 + n : ℕ) : ℝ) := by push_cast; ring
      rw [he, Real.rpow_natCast]
      ring
    exact h1.trans_eq h2
  have hε_pow : ε ^ (3 + n) * ε ^ (-4 - (n : ℝ)) = ε⁻¹ := by
    rw [← Real.rpow_natCast ε (3 + n), ← Real.rpow_add hε]
    have he : ((3 + n : ℕ) : ℝ) + (-4 - (n : ℝ)) = -1 := by push_cast; ring
    rw [he, Real.rpow_neg_one]
  have hd4_nn : 0 ≤ d ^ (-4 - (n : ℝ)) := Real.rpow_nonneg hd0.le _
  have hsum : d ^ (-6 - (n : ℝ)) + d ^ (-5 - (n : ℝ)) ≤
      (24 ^ 2 + 24) * (1 + ν⁻¹) ^ 2 * d ^ (-4 - (n : ℝ)) := by
    rw [h6, h5, ← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ hd4_nn
    linarith [hd_inv2, hd_inv1']
  calc ε ^ (3 + n) * (d ^ (-6 - (n : ℝ)) + d ^ (-5 - (n : ℝ)))
      ≤ ε ^ (3 + n) * ((24 ^ 2 + 24) * (1 + ν⁻¹) ^ 2 *
          ((23 : ℝ) ^ (4 + n) * ε ^ (-4 - (n : ℝ)) * ρ ^ (-4 - (n : ℝ)))) := by
        gcongr
        exact hsum.trans (mul_le_mul_of_nonneg_left hd4 (by positivity))
    _ = (24 ^ 2 + 24) * (23 : ℝ) ^ (4 + n) * (1 + ν⁻¹) ^ 2 *
          (ε ^ (3 + n) * ε ^ (-4 - (n : ℝ))) * ρ ^ (-4 - (n : ℝ)) := by ring
    _ = (24 ^ 2 + 24) * (23 : ℝ) ^ (4 + n) * (1 + ν⁻¹) ^ 2 * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) := by
        rw [hε_pow]

set_option maxHeartbeats 800000 in
private theorem validPsiFieldWith_diff_and_newton :
    ∃ C_D : ℝ, 0 ≤ C_D ∧
      ∀ (ν c ε μ : ℝ), 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 < μ → μ < 1 / 4 →
      ∀ (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ),
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        Integrable (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)) volume →
        let r₁ := (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν)
        let Nr := ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)
        let Z₁ := srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G))
        let Z₂ := newtonX0 ε μ G
        ValidPsiFieldWith r₁ (C_D * (1 + ν⁻¹ + c) ^ 2 * ε⁻¹ * Nr) (fun t y' => Z₁ t y' - Z₂ t y') ∧
        ∃ B₂ : ℝ, ValidPsiFieldWith r₁ B₂ Z₂ := by
  choose CD hCD0 hCD using mp_diff_iter_pointwise
  choose CV hCV0 hCV using iteratedFDeriv_sepVmu0_le
  set M_CD := max (max (CD 0) (CD 1)) (max (CD 2) (CD 3))
  set M_CV := max (max (CV 0) (CV 1)) (max (CV 2) (CV 3))
  have hMCD0 : 0 ≤ M_CD := le_trans (hCD0 0) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hMCV0 : 0 ≤ M_CV := le_trans (hCV0 0) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨4 * M_CD * (24 ^ 2 + 24) * (23 : ℝ) ^ 7, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint r₁ Nr Z₁ Z₂
  have hmeas : Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2) := by
    unfold IIIa.tensorNorm
    exact Measurable.sqrt (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => (hGm i j).pow_const 2)
  have hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume := by
    refine Integrable.mono' hwint hmeas.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_of_nonneg (tn_nonneg _)]
    exact le_mul_of_one_le_left (tn_nonneg _) (by linarith [abs_nonneg w.2])
  have hNr0 : 0 ≤ Nr := integral_nonneg fun w => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  set N0 : ℝ := ∫ w : (ℝ × ℝ) × ℝ, IIIa.tensorNorm (G w.1 w.2)
  have hN0_nn : 0 ≤ N0 := integral_nonneg fun _ => Real.sqrt_nonneg _
  set ρo := Real.sqrt (5 * ν / 6)
  have hρo : 0 ≤ ρo := Real.sqrt_nonneg _
  have hμ_re0 : -(1 / 4 : ℝ) < (μ : ℂ).re := by simp; linarith
  have hμ_re1 : -(1 / 4 : ℝ) < ((μ : ℂ) + 1).re := by simp; linarith
  -- τ-independence of `Z₁` and `Z₂`
  have hZ1_tau : ∀ t, Z₁ t = Z₁ 0 := fun _ => rfl
  have hZ2_tau : ∀ t, Z₂ t = Z₂ 0 := fun _ => rfl
  -- Smoothness and evaluations at any `y'` with `r₁ < ϱ y'`
  have h_at : ∀ y' : Space, r₁ < ϱ y' →
      ContDiffAt ℝ ∞ (fun y => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε (IIIa.meanLift G)) y 0) y' ∧
      ContDiffAt ℝ ∞ (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε (IIIa.meanLift G)) y 0) y' ∧
      ContDiffAt ℝ ∞ (IIIa.sepVmu0 (μ : ℂ) G) (ε • y') ∧
      ContDiffAt ℝ ∞ (IIIa.sepVmu0 ((μ : ℂ) + 1) G) (ε • y') := by
    intro y' hy'
    obtain ⟨hρ, _, _⟩ := gap_bounds_of_gt hν hε hy'
    have hρ0 : 0 ≤ ϱ y' := by unfold ϱ; exact Real.sqrt_nonneg _
    have hxo' : ε * ϱ y' ≤ Real.sqrt ((ε • y') 0 ^ 2 + (ε • y') 1 ^ 2) := by
      have : (ε • y') 0 ^ 2 + (ε • y') 1 ^ 2 = (ε * ϱ y') ^ 2 := by
        unfold ϱ
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        simp only [PiLp.smul_apply, smul_eq_mul]; ring
      rw [this, Real.sqrt_sq (mul_nonneg hε.le hρ0)]
    have hy'_eq : ε⁻¹ • (ε • y') = y' := inv_smul_smul₀ hε.ne' y'
    have hW0 := (mp_W_iter_eval 0 ν c ε ρo (ε * ϱ y') (μ : ℂ) hν hc hε hρo hρ hμ_re0
      G hGm hGs hint (ε • y') hxo' 0).1
    have hW1 := (mp_W_iter_eval 0 ν c ε ρo (ε * ϱ y') ((μ : ℂ) + 1) hν hc hε hρo hρ hμ_re1
      G hGm hGs hint (ε • y') hxo' 0).1
    rw [hy'_eq] at hW0 hW1
    have hV0 := (mp_V_iter_eval 0 (μ : ℂ) hμ_re0 ρo (ε * ϱ y') hρo hρ G hGm hGs hint (ε • y') hxo').1
    have hV1 := (mp_V_iter_eval 0 ((μ : ℂ) + 1) hμ_re1 ρo (ε * ϱ y') hρo hρ G hGm hGs hint (ε • y') hxo').1
    exact ⟨hW0, hW1, hV0, hV1⟩
  have hZ1_smooth : ∀ y', r₁ < ϱ y' → ContDiffAt ℝ ∞ (Z₁ 0) y' := by
    intro y' hy'
    obtain ⟨hW0, hW1, _, _⟩ := h_at y' hy'
    exact PhasePrim.reMap.contDiff.contDiffAt.comp y' (hW0.sub hW1)
  have hZ2_smooth : ∀ y', r₁ < ϱ y' → ContDiffAt ℝ ∞ (Z₂ 0) y' := by
    intro y' hy'
    obtain ⟨_, _, hV0, hV1⟩ := h_at y' hy'
    have hsmul : ContDiffAt ℝ ∞ (fun y : Space => ε • y) y' := (contDiff_const_smul ε).contDiffAt
    exact (PhasePrim.reMap.contDiff.contDiffAt.comp y'
      ((hV0.comp y' hsmul).sub (hV1.comp y' hsmul))).const_smul (ε ^ 2)
  have h1nuc : 0 < 1 + ν⁻¹ + c := by have := inv_pos.2 hν; positivity
  refine ⟨?_, ?_⟩
  · -- Part 1: `ValidPsiFieldWith` for `D = Z₁ - Z₂`
    refine ⟨by positivity, fun t => funext fun y' => by simp [hZ1_tau t, hZ2_tau t],
      fun y' hy' => (hZ1_smooth y' hy').sub (hZ2_smooth y' hy'), ?_⟩
    intro n hn y' hy'
    obtain ⟨hW0, hW1, hV0, hV1⟩ := h_at y' hy'
    obtain ⟨hρ, hd1, hd2⟩ := gap_bounds_of_gt hν hε hy'
    have hρ' : 0 < ϱ y' := lt_of_le_of_lt (by positivity) hy'
    have hρ'_nn : 0 ≤ ϱ y' := hρ'.le
    have hxo' : ε * ϱ y' ≤ Real.sqrt ((ε • y') 0 ^ 2 + (ε • y') 1 ^ 2) := by
      have : (ε • y') 0 ^ 2 + (ε • y') 1 ^ 2 = (ε * ϱ y') ^ 2 := by
        unfold ϱ
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        simp only [PiLp.smul_apply, smul_eq_mul]; ring
      rw [this, Real.sqrt_sq (mul_nonneg hε.le hρ'_nn)]
    have hy'_eq : ε⁻¹ • (ε • y') = y' := inv_smul_smul₀ hε.ne' y'
    have hZ1n : ContDiffAt ℝ n (Z₁ 0) y' := (hZ1_smooth y' hy').of_le (by exact_mod_cast le_top)
    have hZ2n : ContDiffAt ℝ n (Z₂ 0) y' := (hZ2_smooth y' hy').of_le (by exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ n (Z₁ 0 - Z₂ 0) y'‖ ≤ _
    rw [iteratedFDeriv_sub_apply hZ1n hZ2n]
    have hsrc_eq := iteratedFDeriv_srcX0 n ν μ (IIIa.thinSource ε (IIIa.meanLift G)) 0 y' hW0 hW1
    have hnew_eq := iteratedFDeriv_newtonX0 n hε G 0 hV0 hV1
    rw [hy'_eq] at hnew_eq
    unfold Z₁ Z₂
    rw [hsrc_eq, hnew_eq]
    set A0 := iteratedFDeriv ℝ n (fun y => IIIa.sepW ν (μ : ℂ)
      (IIIa.thinSource ε (IIIa.meanLift G)) y 0) y'
    set A1 := iteratedFDeriv ℝ n (fun y => IIIa.sepW ν ((μ : ℂ) + 1)
      (IIIa.thinSource ε (IIIa.meanLift G)) y 0) y'
    set B0 := (ε ^ (2 + n) : ℝ) • iteratedFDeriv ℝ n (IIIa.sepVmu0 (μ : ℂ) G) (ε • y')
    set B1 := (ε ^ (2 + n) : ℝ) • iteratedFDeriv ℝ n (IIIa.sepVmu0 ((μ : ℂ) + 1) G) (ε • y')
    have hsub : PhasePrim.reMap.compContinuousMultilinearMap (A0 - A1) -
        PhasePrim.reMap.compContinuousMultilinearMap (B0 - B1) =
        PhasePrim.reMap.compContinuousMultilinearMap ((A0 - B0) - (A1 - B1)) := by
      refine ContinuousMultilinearMap.ext fun m => ?_
      change PhasePrim.reMap (A0 m - A1 m) - PhasePrim.reMap (B0 m - B1 m) =
        PhasePrim.reMap ((A0 m - B0 m) - (A1 m - B1 m))
      rw [← map_sub]
      congr 1; abel
    have hnorm_re : ‖PhasePrim.reMap.compContinuousMultilinearMap (A0 - A1) -
        PhasePrim.reMap.compContinuousMultilinearMap (B0 - B1)‖ ≤
        2 * (‖A0 - B0‖ + ‖A1 - B1‖) := by
      rw [hsub]
      calc ‖PhasePrim.reMap.compContinuousMultilinearMap ((A0 - B0) - (A1 - B1))‖
          ≤ ‖PhasePrim.reMap‖ * ‖(A0 - B0) - (A1 - B1)‖ :=
            ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ ≤ 2 * (‖A0 - B0‖ + ‖A1 - B1‖) :=
            mul_le_mul PhasePrim.opNorm_reMap_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
    have hb0 := iteratedFDeriv_sepW_sub_sepVmu0_le n (CD n) (hCD0 n) (hCD n)
      ν c ε ρo (ε * ϱ y') (μ : ℂ) hν hν1 hc hε hε1 hρo hρ hμ_re0 G hGm hGs hwint hint
      (ε • y') hxo' 0
    have hb1 := iteratedFDeriv_sepW_sub_sepVmu0_le n (CD n) (hCD0 n) (hCD n)
      ν c ε ρo (ε * ϱ y') ((μ : ℂ) + 1) hν hν1 hc hε hε1 hρo hρ hμ_re1 G hGm hGs hwint hint
      (ε • y') hxo' 0
    rw [hy'_eq] at hb0 hb1
    have hCD_le : CD n ≤ M_CD := by
      interval_cases n
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    have h23_le : (23 : ℝ) ^ (4 + n) ≤ (23 : ℝ) ^ 7 :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hd_bd := d_rpow_bound n hν hν1 hε hρ' hd1 hd2
    have hnu_c : (1 + ν⁻¹) ^ 2 ≤ (1 + ν⁻¹ + c) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hcomb : 2 * (‖A0 - B0‖ + ‖A1 - B1‖) ≤
        4 * CD n * (ε ^ (3 + n) *
          ((ε * ϱ y' - ρo) ^ (-6 - (n : ℝ)) + (ε * ϱ y' - ρo) ^ (-5 - (n : ℝ)))) * Nr := by
      linarith [hb0, hb1]
    refine (hnorm_re.trans hcomb).trans ?_
    calc 4 * CD n * (ε ^ (3 + n) *
          ((ε * ϱ y' - ρo) ^ (-6 - (n : ℝ)) + (ε * ϱ y' - ρo) ^ (-5 - (n : ℝ)))) * Nr
        ≤ 4 * M_CD * ((24 ^ 2 + 24) * (23 : ℝ) ^ (4 + n) * (1 + ν⁻¹) ^ 2 * ε⁻¹ *
            (ϱ y') ^ (-4 - (n : ℝ))) * Nr := by gcongr
      _ ≤ 4 * M_CD * ((24 ^ 2 + 24) * (23 : ℝ) ^ 7 * (1 + ν⁻¹ + c) ^ 2 * ε⁻¹ *
            (ϱ y') ^ (-4 - (n : ℝ))) * Nr := by gcongr
      _ = (4 * M_CD * (24 ^ 2 + 24) * (23 : ℝ) ^ 7 * (1 + ν⁻¹ + c) ^ 2 * ε⁻¹ * Nr) *
            (ϱ y') ^ (-4 - (n : ℝ)) := by ring
  · -- Part 2: `ValidPsiFieldWith` for `Z₂ = newtonX0 ε μ G`
    refine ⟨4 * M_CV * (23 : ℝ) ^ 7 * ε ^ (-2 : ℝ) * N0, ?_⟩
    refine ⟨by positivity, hZ2_tau, hZ2_smooth, ?_⟩
    intro n hn y' hy'
    obtain ⟨_, _, hV0, hV1⟩ := h_at y' hy'
    obtain ⟨hρ, _, hd2⟩ := gap_bounds_of_gt hν hε hy'
    have hρ' : 0 < ϱ y' := lt_of_le_of_lt (by positivity) hy'
    have hρ'_nn : 0 ≤ ϱ y' := hρ'.le
    have hxo' : ε * ϱ y' ≤ Real.sqrt ((ε • y') 0 ^ 2 + (ε • y') 1 ^ 2) := by
      have : (ε • y') 0 ^ 2 + (ε • y') 1 ^ 2 = (ε * ϱ y') ^ 2 := by
        unfold ϱ
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        simp only [PiLp.smul_apply, smul_eq_mul]; ring
      rw [this, Real.sqrt_sq (mul_nonneg hε.le hρ'_nn)]
    have hy'_eq : ε⁻¹ • (ε • y') = y' := inv_smul_smul₀ hε.ne' y'
    have hnew_eq := iteratedFDeriv_newtonX0 n hε G 0 hV0 hV1
    rw [hy'_eq] at hnew_eq
    unfold Z₂
    rw [hnew_eq]
    set B0 := (ε ^ (2 + n) : ℝ) • iteratedFDeriv ℝ n (IIIa.sepVmu0 (μ : ℂ) G) (ε • y')
    set B1 := (ε ^ (2 + n) : ℝ) • iteratedFDeriv ℝ n (IIIa.sepVmu0 ((μ : ℂ) + 1) G) (ε • y')
    have hnorm_re : ‖PhasePrim.reMap.compContinuousMultilinearMap (B0 - B1)‖ ≤
        2 * (‖B0‖ + ‖B1‖) := by
      calc ‖PhasePrim.reMap.compContinuousMultilinearMap (B0 - B1)‖
          ≤ ‖PhasePrim.reMap‖ * ‖B0 - B1‖ :=
            ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ ≤ 2 * (‖B0‖ + ‖B1‖) :=
            mul_le_mul PhasePrim.opNorm_reMap_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
    have hv0 := hCV n (μ : ℂ) ρo (ε * ϱ y') hμ_re0 hρo hρ G hGm hGs hint (ε • y') hxo'
    have hv1 := hCV n ((μ : ℂ) + 1) ρo (ε * ϱ y') hμ_re1 hρo hρ G hGm hGs hint (ε • y') hxo'
    have hB0_le : ‖B0‖ ≤ ε ^ (2 + n) * (CV n * (ε * ϱ y' - ρo) ^ (-4 - (n : ℝ)) * N0) := by
      unfold B0
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hv0 (by positivity)
    have hB1_le : ‖B1‖ ≤ ε ^ (2 + n) * (CV n * (ε * ϱ y' - ρo) ^ (-4 - (n : ℝ)) * N0) := by
      unfold B1
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hv1 (by positivity)
    have hCV_le : CV n ≤ M_CV := by
      interval_cases n
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    have hd4 : (ε * ϱ y' - ρo) ^ (-4 - (n : ℝ)) ≤
        (23 : ℝ) ^ 7 * ε ^ (-4 - (n : ℝ)) * (ϱ y') ^ (-4 - (n : ℝ)) := by
      have h1 : (ε * ϱ y' - ρo) ^ (-4 - (n : ℝ)) ≤ ((ε * ϱ y') / 23) ^ (-4 - (n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hd2 (by have := n.cast_nonneg (α := ℝ); linarith)
      have h2 : ((ε * ϱ y') / 23) ^ (-4 - (n : ℝ)) =
          (23 : ℝ) ^ (4 + n) * ε ^ (-4 - (n : ℝ)) * (ϱ y') ^ (-4 - (n : ℝ)) := by
        rw [div_eq_mul_inv, Real.mul_rpow (mul_nonneg hε.le hρ'.le) (by norm_num),
          Real.mul_rpow hε.le hρ'.le, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
        have he : -(-4 - (n : ℝ)) = ((4 + n : ℕ) : ℝ) := by push_cast; ring
        rw [he, Real.rpow_natCast]
        ring
      have h23 : (23 : ℝ) ^ (4 + n) ≤ (23 : ℝ) ^ 7 :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      refine h1.trans (h2.trans_le ?_)
      gcongr
    have hε_pow : ε ^ (2 + n) * ε ^ (-4 - (n : ℝ)) = ε ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast ε (2 + n), ← Real.rpow_add hε]
      congr 1; push_cast; ring
    have hcomb : 2 * (‖B0‖ + ‖B1‖) ≤
        4 * CV n * (ε ^ (2 + n) * (ε * ϱ y' - ρo) ^ (-4 - (n : ℝ))) * N0 := by
      linarith [hB0_le, hB1_le]
    refine (hnorm_re.trans hcomb).trans ?_
    calc 4 * CV n * (ε ^ (2 + n) * (ε * ϱ y' - ρo) ^ (-4 - (n : ℝ))) * N0
        ≤ 4 * M_CV * (ε ^ (2 + n) *
            ((23 : ℝ) ^ 7 * ε ^ (-4 - (n : ℝ)) * (ϱ y') ^ (-4 - (n : ℝ)))) * N0 := by gcongr
      _ = 4 * M_CV * (23 : ℝ) ^ 7 * (ε ^ (2 + n) * ε ^ (-4 - (n : ℝ))) * N0 *
            (ϱ y') ^ (-4 - (n : ℝ)) := by ring
      _ = (4 * M_CV * (23 : ℝ) ^ 7 * ε ^ (-2 : ℝ) * N0) * (ϱ y') ^ (-4 - (n : ℝ)) := by
          rw [hε_pow]

/-! ## 5. Proof of `YBWidth.sepCommPsiDiff` -/

/-- **Outward stream-primitive commutator difference bound** (`PartIII-b:C/rep/8/1/1/2/5/2/1/4`). -/
theorem sepCommPsiDiff : SepCommPsiDiff := by
  intro χy hχ
  obtain ⟨C_phi, hC_phi0, h_phi⟩ := fderiv_phiScalar_bound hχ
  obtain ⟨C_D, hC_D0, h_valid⟩ := validPsiFieldWith_diff_and_newton
  refine ⟨32 * C_phi * C_D, 2, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint τ xo hxo1 hxo2
  set r₁ := (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν)
  set Nr := ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)
  have hNr0 : 0 ≤ Nr := integral_nonneg fun w => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  set Z₁ := srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G))
  set Z₂ := newtonX0 ε μ G
  set D : ℝ → Space → Space := fun t y' => Z₁ t y' - Z₂ t y'
  have h1nuc : 0 < 1 + ν⁻¹ + c := by have := inv_pos.2 hν; positivity
  set B_D := C_D * (1 + ν⁻¹ + c) ^ 2 * ε⁻¹ * Nr
  obtain ⟨hD_val, ⟨B₂, hZ₂_val⟩⟩ :=
    h_valid ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint
  have hZ₁_eq : Z₁ = fun t y' => D t y' + Z₂ t y' := by
    funext t y'; simp [D]
  have hZ₁_val : ValidPsiFieldWith r₁ (B_D + B₂) Z₁ := by
    rw [hZ₁_eq]
    exact hD_val.add hZ₂_val
  set y := ε⁻¹ • xo
  set r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hr_ge : Real.sqrt ν ≤ r := Real.sqrt_le_sqrt hxo1
  have hr_le : r ≤ Real.sqrt (5 * ν / 4) := Real.sqrt_le_sqrt hxo2
  have hr_pos : 0 < r := lt_of_lt_of_le hsν hr_ge
  have hR1 : 1 ≤ ε⁻¹ := one_le_inv_iff₀.2 ⟨hε, hε1⟩
  have hR_pos : 0 < ε⁻¹ := inv_pos.2 hε
  have hr₁_pos : 0 < r₁ := by positivity
  have hϱ_y : ϱ y = ε⁻¹ * r := by
    unfold ϱ y r
    have : (ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2 = (ε⁻¹) ^ 2 * (xo 0 ^ 2 + xo 1 ^ 2) := by
      simp only [PiLp.smul_apply, smul_eq_mul]; ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hR_pos.le]
  have hy_ann : y ∈ streamAnn ν ε⁻¹ := by
    refine ⟨?_, ?_⟩ <;> rw [hϱ_y] <;> gcongr
  have hy_r1 : r₁ < ϱ y := by
    rw [hϱ_y]
    dsimp [r₁]
    have : (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν) < 1 * (ε⁻¹ * Real.sqrt ν) := by
      have : 0 < ε⁻¹ * Real.sqrt ν := by positivity
      linarith
    linarith [mul_le_mul_of_nonneg_left hr_ge hR_pos.le]
  have hopen : IsOpen {y' : Space | r₁ < ϱ y'} := isOpen_lt continuous_const continuous_ϱ
  have hmem : {y' : Space | r₁ < ϱ y'} ∈ 𝓝 y := hopen.mem_nhds hy_r1
  let smulE2 : ℝ →L[ℝ] Space :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (coordinateVector 2)
  have hev1 : commPsi ν μ ε⁻¹ χy Z₁ τ =ᶠ[𝓝 y] fun y' => smulE2 (phiScalar ν ε⁻¹ χy Z₁ y') := by
    filter_upwards [hmem] with y' hy'
    simpa [smulE2] using commPsi_eq_phiScalar ν μ ε⁻¹ hχ hZ₁_val hr₁_pos τ hy'
  have hev2 : commPsi ν μ ε⁻¹ χy Z₂ τ =ᶠ[𝓝 y] fun y' => smulE2 (phiScalar ν ε⁻¹ χy Z₂ y') := by
    filter_upwards [hmem] with y' hy'
    simpa [smulE2] using commPsi_eq_phiScalar ν μ ε⁻¹ hχ hZ₂_val hr₁_pos τ hy'
  have hevD : phiScalar ν ε⁻¹ χy D =ᶠ[𝓝 y]
      fun y' => phiScalar ν ε⁻¹ χy Z₁ y' - phiScalar ν ε⁻¹ χy Z₂ y' := by
    filter_upwards [hmem] with y' hy'
    exact (phiScalar_sub ν ε⁻¹ χy hZ₁_val hZ₂_val hr₁_pos hy').symm
  obtain ⟨hdZ₁, _⟩ := h_phi ν ε⁻¹ (B_D + B₂) Z₁ hν hν1 hR1 hZ₁_val y hy_ann
  obtain ⟨hdZ₂, _⟩ := h_phi ν ε⁻¹ B₂ Z₂ hν hν1 hR1 hZ₂_val y hy_ann
  obtain ⟨_, hbdD⟩ := h_phi ν ε⁻¹ B_D D hν hν1 hR1 hD_val y hy_ann
  have hfd1 : fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y =
      smulE2.comp (fderiv ℝ (phiScalar ν ε⁻¹ χy Z₁) y) := by
    rw [hev1.fderiv_eq]
    exact (smulE2.hasFDerivAt.comp y hdZ₁.hasFDerivAt).fderiv
  have hfd2 : fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y =
      smulE2.comp (fderiv ℝ (phiScalar ν ε⁻¹ χy Z₂) y) := by
    rw [hev2.fderiv_eq]
    exact (smulE2.hasFDerivAt.comp y hdZ₂.hasFDerivAt).fderiv
  have hfdD : fderiv ℝ (phiScalar ν ε⁻¹ χy D) y =
      fderiv ℝ (phiScalar ν ε⁻¹ χy Z₁) y - fderiv ℝ (phiScalar ν ε⁻¹ χy Z₂) y := by
    rw [hevD.fderiv_eq]
    exact fderiv_sub hdZ₁ hdZ₂
  have hdiff_eq : fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y -
      fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y =
      smulE2.comp (fderiv ℝ (phiScalar ν ε⁻¹ χy D) y) := by
    rw [hfd1, hfd2, ← ContinuousLinearMap.comp_sub, hfdD]
  have hnorm_smulE2 : ‖smulE2.comp (fderiv ℝ (phiScalar ν ε⁻¹ χy D) y)‖ ≤
      ‖fderiv ℝ (phiScalar ν ε⁻¹ χy D) y‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    simp only [smulE2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, norm_smul, IIIa.mp_norm_e, mul_one]
    exact (fderiv ℝ (phiScalar ν ε⁻¹ χy D) y).le_opNorm v
  rw [hdiff_eq]
  have hr_2sν : r ≤ 2 * Real.sqrt ν := by
    have : Real.sqrt (5 * ν / 4) ≤ 2 * Real.sqrt ν := by
      rw [show (2 : ℝ) * Real.sqrt ν = Real.sqrt (2 ^ 2 * ν) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    exact hr_le.trans this
  have hs_le : (ε⁻¹ * Real.sqrt ν)⁻¹ ≤ 2 * ε * r⁻¹ := by
    rw [mul_inv, inv_inv]
    have h1 : (Real.sqrt ν)⁻¹ ≤ 2 * r⁻¹ := by
      have := inv_anti₀ hr_pos hr_2sν
      rw [mul_inv] at this
      linarith [inv_pos.2 hsν]
    calc ε * (Real.sqrt ν)⁻¹ ≤ ε * (2 * r⁻¹) := by gcongr
      _ = 2 * ε * r⁻¹ := by ring
  have hs5_le : ((ε⁻¹ * Real.sqrt ν)⁻¹) ^ 5 ≤ 32 * ε ^ 5 * r ^ (-5 : ℝ) := by
    have h1 : ((ε⁻¹ * Real.sqrt ν)⁻¹) ^ 5 ≤ (2 * ε * r⁻¹) ^ 5 :=
      pow_le_pow_left₀ (by positivity) hs_le 5
    have h2 : (r⁻¹) ^ 5 = r ^ (-5 : ℝ) := by
      rw [show (-5 : ℝ) = -(5 : ℕ) by norm_num, Real.rpow_neg hr_pos.le, Real.rpow_natCast, inv_pow]
    calc ((ε⁻¹ * Real.sqrt ν)⁻¹) ^ 5 ≤ (2 * ε * r⁻¹) ^ 5 := h1
      _ = 32 * ε ^ 5 * (r⁻¹) ^ 5 := by ring
      _ = 32 * ε ^ 5 * r ^ (-5 : ℝ) := by rw [h2]
  have hε_cancel : ε⁻¹ * ε ^ 5 = ε ^ 4 := by
    have : ε ^ 5 = ε * ε ^ 4 := by ring
    rw [this, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
  calc ‖smulE2.comp (fderiv ℝ (phiScalar ν ε⁻¹ χy D) y)‖
      ≤ ‖fderiv ℝ (phiScalar ν ε⁻¹ χy D) y‖ := hnorm_smulE2
    _ ≤ C_phi * B_D * ((ε⁻¹ * Real.sqrt ν)⁻¹) ^ 5 := hbdD
    _ ≤ C_phi * B_D * (32 * ε ^ 5 * r ^ (-5 : ℝ)) := by
        have : 0 ≤ C_phi * B_D := by unfold B_D; positivity
        gcongr
    _ = 32 * C_phi * C_D * (1 + ν⁻¹ + c) ^ 2 * (ε⁻¹ * ε ^ 5) * r ^ (-5 : ℝ) * Nr := by
        unfold B_D; ring
    _ = 32 * C_phi * C_D * (1 + ν⁻¹ + c) ^ 2 * ε ^ 4 * r ^ (-5 : ℝ) * Nr := by
        rw [hε_cancel]

end YBWidth

end UnforcedLeray.Short.PartIIIb.Concrete
