import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.CommDerivSplit.TimeReg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.ZPrimRegular.RayPrim
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Leibniz
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_2_11_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.Comm

/-!
# Pointwise transition-annulus derivative bound for `commPsi` (`SepPsiOscFar/PointwisePhi`)

Source `the November 2 reference manuscript`
lines 4178-4215, 5400-5432.

For `Z₁ = srcX0 ν μ (IIIa.thinSource ε F)` and
`Z₂ = srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F)))` with
`FarLeafOrg.ThinHyp c ρo F` and `IIIa.thinMoment c F ≠ ⊤`, at any phase `τ : ℝ`:
1. `thin_commPsi_eq_phiScalar`: on `{y' : Space | r₁ < ϱ y'}` (`r₁ = (23/24) * (ε⁻¹ * √ν)`),
   `commPsi ν μ ε⁻¹ χy Z_i τ y' = phiScalar ν ε⁻¹ χy (fun _ => Z_i τ) y' • coordinateVector 2`.
2. `fderiv_commPsi_sub_le`: at `y = ε⁻¹ • xo` on the transition annulus
   `ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4` (`r_y = ϱ y`, `z_y = y 2`, `s = (ε⁻¹ * √ν)⁻¹`),
   `‖fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y‖` is bounded by
   `C_χ` times the sum of pointwise norms `ptNorm (ΔZ τ) j r_y z_y` (`j ≤ 2`) and outward ray
   integrals `rayInt (ΔZ τ) j r_y z_y` (`j ≤ 3`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi ContinuousMultilinearMap
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

open UnforcedLeray.Short.IIIa
open YBComm PhasePrim FarLeafOrg GeomXAsm GeomXAsm.RayFTCAux GeomXAsm.RayPrimAux

namespace SepPsiOscFarAux

/-! ## 1. Partial-derivative bounds and `HasDecay45` -/

theorem contDiffAt_physPd {g : Space → Space} {y : Space} (hg : ContDiffAt ℝ ∞ g y)
    (j : Fin 3) : ContDiffAt ℝ ∞ (physPd g j) y := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ g) y :=
    hg.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤))
  exact (ContinuousLinearMap.apply ℝ Space (UnforcedLeray.coordinateVector j)).contDiff.contDiffAt.comp
    y hd

theorem norm_iteratedFDeriv_physPd_le_at (m : ℕ) {g : Space → Space} {y : Space}
    (hg : ContDiffAt ℝ ∞ g y) (j : Fin 3) :
    ‖iteratedFDeriv ℝ m (physPd g j) y‖ ≤ ‖iteratedFDeriv ℝ (m + 1) g y‖ := by
  let L : (Space →L[ℝ] Space) →L[ℝ] Space :=
    ContinuousLinearMap.apply ℝ Space (UnforcedLeray.coordinateVector j)
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
  change ‖M v (UnforcedLeray.coordinateVector j)‖ ≤ ‖M‖ * ∏ i : Fin m, ‖v i‖
  calc ‖M v (UnforcedLeray.coordinateVector j)‖
      ≤ ‖M v‖ * ‖(UnforcedLeray.coordinateVector j : Space)‖ := (M v).le_opNorm _
    _ = ‖M v‖ := by rw [norm_e j, mul_one]
    _ ≤ ‖M‖ * ∏ i : Fin m, ‖v i‖ := M.le_opNorm v

theorem norm_fderiv_le_iter1 {g : Space → Space} {y : Space} :
    ‖fderiv ℝ g y‖ ≤ ‖iteratedFDeriv ℝ 1 g y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  have h := (iteratedFDeriv ℝ 1 g y).le_opNorm ![v]
  simpa [iteratedFDeriv_one_apply] using h

theorem norm_self_le_iter0 {g : Space → Space} {y : Space} :
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

theorem ϱ_hpt_of_pos {ρ : ℝ} (hρ : 0 < ρ) (z : ℝ) : ϱ (hpt ρ z) = ρ := by
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
      fun y' : Space => ϱ y' • (UnforcedLeray.coordinateVector 0 : Space) +
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) y' •
          (UnforcedLeray.coordinateVector 2 : Space) :=
    funext fun y' => hpt_eq_lin (ϱ y') (y' 2)
  have hG : HasFDerivAt (fun y' : Space => hpt (ϱ y') (y' 2))
      ((ϱD y).smulRight (UnforcedLeray.coordinateVector 0) +
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight
          (UnforcedLeray.coordinateVector 2)) y := by
    rw [hhpt]
    exact ((hasFDerivAt_ϱ (tcle_notaxis hρ)).smul_const (UnforcedLeray.coordinateVector 0)).add
      ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.smul_const
        (UnforcedLeray.coordinateVector 2))
  have hdW : HasFDerivAt (W 0) (fderiv ℝ (W 0) (hpt (ϱ y) (y 2))) (hpt (ϱ y) (y 2)) :=
    (hW.diff (hpt (ϱ y) (y 2)) (by rw [ϱ_hpt_of_pos hρ]; exact hy)).hasFDerivAt
  have hcomp := (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp y
    (hdW.comp y hG)
  refine hcomp.congr_fderiv ?_
  ext v
  simp [physPd, map_smul]
  ring

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

theorem sub {B₁ B₂ : ℝ} {X Y : ℝ → Space → Space}
    (hX : ValidPsiFieldWith r₁ B₁ X) (hY : ValidPsiFieldWith r₁ B₂ Y) :
    ValidPsiFieldWith r₁ (B₁ + B₂) (fun t y' => X t y' - Y t y') where
  B_nonneg := add_nonneg hX.B_nonneg hY.B_nonneg
  tau_indep t := funext fun y' => by simp [hX.tau_indep t, hY.tau_indep t]
  smooth y' hy' := (hX.smooth y' hy').sub (hY.smooth y' hy')
  decay n hn y' hy' := by
    have hXn : ContDiffAt ℝ n (X 0) y' := (hX.smooth y' hy').of_le (by exact_mod_cast le_top)
    have hYn : ContDiffAt ℝ n (Y 0) y' := (hY.smooth y' hy').of_le (by exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ n (X 0 - Y 0) y'‖ ≤ (B₁ + B₂) * (ϱ y') ^ (-4 - (n : ℝ))
    rw [iteratedFDeriv_sub_apply hXn hYn]
    refine (norm_sub_le _ _).trans ?_
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
      norm_self_le_iter0.trans (norm_iteratedFDeriv_physPd_le_at 0 (hZ.smooth y' hy') j)
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
      norm_fderiv_le_iter1.trans (norm_iteratedFDeriv_physPd_le_at 1 (hZ.smooth y' hy') j)
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
      (norm_self_le_iter0.trans (norm_iteratedFDeriv_physPd_le_at 0 hcd1 j)).trans
        (norm_iteratedFDeriv_physPd_le_at 1 (hZ.smooth y' hy') l)
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
      (norm_fderiv_le_iter1.trans (norm_iteratedFDeriv_physPd_le_at 1 hcd1 j)).trans
        (norm_iteratedFDeriv_physPd_le_at 2 (hZ.smooth y' hy') l)
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

/-- The explicit scalar coefficient of `coordinateVector 2` in `commPsi`. -/
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
      have hp := PiLp.norm_apply_le (fderiv ℝ (Z 0) (hpt ρ z) (UnforcedLeray.coordinateVector 0)) 2
      rw [Real.norm_eq_abs] at hp
      refine hp.trans ?_
      calc ‖fderiv ℝ (Z 0) (hpt ρ z) (UnforcedLeray.coordinateVector 0)‖
          ≤ ‖fderiv ℝ (Z 0) (hpt ρ z)‖ * ‖(UnforcedLeray.coordinateVector 0 : Space)‖ :=
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
  have hpd2_def : (fun ρ : ℝ => ρ * fderiv ℝ (Z 0) (hpt ρ z) (UnforcedLeray.coordinateVector 2) 2) =
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
        (UnforcedLeray.coordinateVector 2 : Space) := by
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
  have hd_eq : ∀ (j : Fin 3), ∀ y' ∈ U,
      fderiv ℝ u y' (UnforcedLeray.coordinateVector j) = d j y' := by
    intro j y' hy'
    have hρ' : 0 < ϱ y' := lt_trans hr₁ hy'
    have hρ'ne : ϱ y' ≠ 0 := hρ'.ne'
    rw [(hu_fderiv y' hy').fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul,
      ϱD_apply, EuclideanSpace.coe_proj, primDz_eq_neg_outPrim_physPd]
    fin_cases j
    · simp [d, H, UnforcedLeray.coordinateVector]; field_simp
    · simp [d, H, UnforcedLeray.coordinateVector]; field_simp
    · simp [d, H, UnforcedLeray.coordinateVector]
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
  have hcut_eq : cutPsi ν R χy Z τ =
      fun y' => u y' • (UnforcedLeray.coordinateVector 2 : Space) := by
    funext y'
    unfold cutPsi psiFld u
    rw [outPrim_congr_tau hZ.tau_indep, mul_smul]
  rw [hcut_eq, tcl_physLap_smul u d (UnforcedLeray.coordinateVector 2 : Space)
    hU_nhds hu_diff hd_eq hdy]
  congr 1
  rw [Fin.sum_univ_three]
  have f0 := tcl_fd_mul 0 hH_fd.differentiableAt (UnforcedLeray.coordinateVector 0)
  have f1 := tcl_fd_mul 1 hH_fd.differentiableAt (UnforcedLeray.coordinateVector 1)
  change fderiv ℝ (fun y' : Space => y' 0 * H y') y (UnforcedLeray.coordinateVector 0) +
      fderiv ℝ (fun y' : Space => y' 1 * H y') y (UnforcedLeray.coordinateVector 1) +
      fderiv ℝ (d 2) y (UnforcedLeray.coordinateVector 2) = _
  rw [f0, f1, hH_fd.fderiv, hd2_fd.fderiv]
  have hsq := tcl_sqsum hρ
  have hp22 : -primDz (fun _ w => physPd (Z 0) 2 w) 0 (ϱ y) (y 2) =
      outPrim (fun _ w => physPd2 (Z 0) 2 2 w) 0 (ϱ y) (y 2) := rfl
  simp only [add_apply, smul_apply, smul_eq_mul,
    ϱD_apply, EuclideanSpace.coe_proj, UnforcedLeray.coordinateVector, PiLp.single_apply,
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
    change (fderiv ℝ (Z₁ 0 - Z₂ 0) (hpt r z) (UnforcedLeray.coordinateVector 0)) 2 = _
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
      change fderiv ℝ (Z₁ 0 - Z₂ 0) x (UnforcedLeray.coordinateVector 2) = _
      rw [fderiv_sub (hZ₁.hasDecay45_self.diff x hx) (hZ₂.hasDecay45_self.diff x hx)]
      rfl
    unfold physPd2
    change fderiv ℝ (physPd (fun x => Z₁ 0 x - Z₂ 0 x) 2) w (UnforcedLeray.coordinateVector 2) = _
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
      change fderiv ℝ (Z₁ 0 - Z₂ 0) x (UnforcedLeray.coordinateVector j) = _
      rw [fderiv_sub (hZ₁.hasDecay45_self.diff x hx) (hZ₂.hasDecay45_self.diff x hx)]
      rfl
    unfold physPd2
    change fderiv ℝ (physPd (fun x => Z₁ 0 x - Z₂ 0 x) j) w (UnforcedLeray.coordinateVector j) = _
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

/-! ## 3. `ValidPsiFieldWith` and `commPsi = phiScalar • e₂` for `srcX0 (thinSource ε F)` -/

theorem rOut_le_22_23_r1 {ν ε ρo : ℝ} (hν : 0 < ν) (hε : 0 < ε)
    (hρo : ρo ≤ Real.sqrt (5 * ν / 6)) :
    ρo / ε ≤ (22 / 23 : ℝ) * ((23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν)) := by
  have h1 : Real.sqrt (5 * ν / 6) ≤ (22 / 24 : ℝ) * Real.sqrt ν := by
    have h2 : (22 / 24 : ℝ) * Real.sqrt ν = Real.sqrt ((22 / 24 : ℝ) ^ 2 * ν) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [h2]
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : ρo / ε ≤ ((22 / 24 : ℝ) * Real.sqrt ν) / ε :=
    div_le_div_of_nonneg_right (hρo.trans h1) hε.le
  calc ρo / ε ≤ ((22 / 24 : ℝ) * Real.sqrt ν) / ε := h2
    _ = (22 / 23 : ℝ) * ((23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν)) := by ring

private theorem thin_sepW_r1_decay {ν ε c ρo : ℝ} {m : ℂ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hρo0 : 0 ≤ ρo)
    (hρo : ρo ≤ Real.sqrt (5 * ν / 6)) (hm : -(1 / 4) < m.re)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤) (τ : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space,
      (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν) < ϱ y' →
      ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν m (IIIa.thinSource ε F) z τ) y'‖ ≤
        C * (ϱ y') ^ (-4 - (j : ℝ)) := by
  obtain ⟨C0, hC0, hdom⟩ := IIIa.sepWDominated IIIa.sepKernelBounds j
  set M_enn : ℝ≥0∞ :=
    ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (2 * m.re + 2 + 1) * c)))) *
      ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * IIIa.thinMoment c F)
  have hM_lt : M_enn < ⊤ := by
    refine ENNReal.mul_lt_top ?_
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hN))
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  set M : ℝ := M_enn.toReal
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  have hM_eq : ENNReal.ofReal M = M_enn := ENNReal.ofReal_toReal hM_lt.ne
  refine ⟨C0 * M * (23 : ℝ) ^ (4 + (j : ℝ)), by positivity, fun y' hy' => ?_⟩
  have hr₁0 : 0 < (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν) := by positivity
  have hrOut : 0 ≤ ρo / ε := div_nonneg hρo0 hε.le
  have hy'_pos : 0 < ϱ y' := lt_trans hr₁0 hy'
  have hrOut_le : ρo / ε ≤ (22 / 23 : ℝ) * ϱ y' :=
    (rOut_le_22_23_r1 hν hε hρo).trans (mul_le_mul_of_nonneg_left hy'.le (by norm_num))
  have hrr : ρo / ε < ϱ y' := by linarith
  have hP : 0 < 2 * ε * c := by positivity
  have hS := thin_isSep hε hth
  set D : ℝ := ϱ y' - ρo / ε
  have hD_23 : ϱ y' / 23 ≤ D := by show ϱ y' / 23 ≤ ϱ y' - ρo / ε; linarith
  have hD_pos : 0 < D := by linarith
  have hfin0 : IIIa.sepDom (2 * m.re + 2) 0 D (IIIa.srcNorm (IIIa.thinSource ε F)) τ y' < ⊤ :=
    (sepDom_thin_le hε hc hD_pos hm hth 0 τ y').trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM_lt)
  have hw := hdom ν hν m hm (ρo / ε) (ϱ y') (2 * ε * c) hrOut hrr hP
    (IIIa.thinSource ε F) hS τ y' le_rfl hfin0
  have hw' : ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν m (IIIa.thinSource ε F) z τ) y'‖ₑ ≤
      ENNReal.ofReal (C0 * M * D ^ (-4 - (j : ℝ))) := by
    calc ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν m (IIIa.thinSource ε F) z τ) y'‖ₑ
        = IIIa.wDerivNorm ν m (IIIa.thinSource ε F) j τ y' := rfl
      _ ≤ ENNReal.ofReal C0 *
            IIIa.sepDom (2 * m.re + 2) j D (IIIa.srcNorm (IIIa.thinSource ε F)) τ y' := hw
      _ ≤ ENNReal.ofReal C0 * (ENNReal.ofReal (D ^ (-4 - (j : ℝ))) * M_enn) := by
          gcongr
          exact sepDom_thin_le hε hc hD_pos hm hth j τ y'
      _ = ENNReal.ofReal (C0 * M * D ^ (-4 - (j : ℝ))) := by
          rw [← hM_eq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
          congr 1; ring
  rw [← ofReal_norm] at hw'
  have hreal : ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν m (IIIa.thinSource ε F) z τ) y'‖ ≤
      C0 * M * D ^ (-4 - (j : ℝ)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hw'
  refine hreal.trans ?_
  have hpow : D ^ (-4 - (j : ℝ)) ≤ (23 : ℝ) ^ (4 + (j : ℝ)) * (ϱ y') ^ (-4 - (j : ℝ)) := by
    have h1 : D ^ (-4 - (j : ℝ)) ≤ (ϱ y' / 23) ^ (-4 - (j : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hD_23
        (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    rw [Real.div_rpow hy'_pos.le (by norm_num)] at h1
    have h2 : (23 : ℝ) ^ (-4 - (j : ℝ)) = ((23 : ℝ) ^ (4 + (j : ℝ)))⁻¹ := by
      rw [show -4 - (j : ℝ) = -(4 + (j : ℝ)) by ring, Real.rpow_neg (by norm_num)]
    rw [h2, div_inv_eq_mul, mul_comm] at h1
    exact h1
  calc C0 * M * D ^ (-4 - (j : ℝ))
      ≤ C0 * M * ((23 : ℝ) ^ (4 + (j : ℝ)) * (ϱ y') ^ (-4 - (j : ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = C0 * M * (23 : ℝ) ^ (4 + (j : ℝ)) * (ϱ y') ^ (-4 - (j : ℝ)) := by ring

private theorem thin_X0_r1_decay {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo0 : 0 ≤ ρo)
    (hρo : ρo ≤ Real.sqrt (5 * ν / 6))
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤) (τ : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space,
      (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν) < ϱ y' →
      ‖iteratedFDeriv ℝ j (srcX0 ν μ (IIIa.thinSource ε F) τ) y'‖ ≤
        C * (ϱ y') ^ (-4 - (j : ℝ)) := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  obtain ⟨C0, hC0, hb0⟩ := thin_sepW_r1_decay hν hε hc hρo0 hρo hm1 hth hN τ j
  obtain ⟨C1, hC1, hb1⟩ := thin_sepW_r1_decay hν hε hc hρo0 hρo hm2 hth hN τ j
  refine ⟨‖reL‖ * (C0 + C1), by positivity, fun y' hy' => ?_⟩
  have hrOut_le := rOut_le_22_23_r1 hν hε hρo
  have hr₁0 : 0 < (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν) := by positivity
  have hy'_mem : ρo / ε < ϱ y' := by linarith
  have hopen : IsOpen {y : Space | ρo / ε < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hWa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ) y' :=
    (contDiffOn_pi.2 fun i =>
      thin_sepW_contDiffOn_top hν hε hc hρo0 hm1 hth hN τ i).contDiffAt (hopen.mem_nhds hy'_mem)
  have hWb : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ) y' :=
    (contDiffOn_pi.2 fun i =>
      thin_sepW_contDiffOn_top hν hε hc hρo0 hm2 hth hN τ i).contDiffAt (hopen.mem_nhds hy'_mem)
  have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hW_sub : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ -
        IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ) y' := hWa.sub hWb
  have hcomp := reL.norm_iteratedFDeriv_comp_left hW_sub hj
  have hsub_eq : iteratedFDeriv ℝ j
      (fun z => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ -
        IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ) y' =
      iteratedFDeriv ℝ j (fun z => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ) y' -
        iteratedFDeriv ℝ j (fun z => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ) y' :=
    iteratedFDeriv_sub_apply (hWa.of_le hj) (hWb.of_le hj)
  calc ‖iteratedFDeriv ℝ j (srcX0 ν μ (IIIa.thinSource ε F) τ) y'‖
      ≤ ‖reL‖ * ‖iteratedFDeriv ℝ j
          (fun z => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ -
            IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ) y'‖ := hcomp
    _ ≤ ‖reL‖ * (‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ) y'‖ +
          ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ) y'‖) := by
        rw [hsub_eq]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ‖reL‖ * (C0 * (ϱ y') ^ (-4 - (j : ℝ)) + C1 * (ϱ y') ^ (-4 - (j : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add (hb0 y' hy') (hb1 y' hy')) (norm_nonneg _)
    _ = ‖reL‖ * (C0 + C1) * (ϱ y') ^ (-4 - (j : ℝ)) := by ring

theorem thin_validPsiFieldWith {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo0 : 0 ≤ ρo)
    (hρo : ρo ≤ Real.sqrt (5 * ν / 6))
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤) (τ : ℝ) :
    ∃ B : ℝ, ValidPsiFieldWith ((23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν)) B
      (fun _ => srcX0 ν μ (IIIa.thinSource ε F) τ) := by
  obtain ⟨B0, hB0, hb0⟩ := thin_X0_r1_decay hν hμ hε hc hρo0 hρo hth hN τ 0
  obtain ⟨B1, hB1, hb1⟩ := thin_X0_r1_decay hν hμ hε hc hρo0 hρo hth hN τ 1
  obtain ⟨B2, hB2, hb2⟩ := thin_X0_r1_decay hν hμ hε hc hρo0 hρo hth hN τ 2
  obtain ⟨B3, hB3, hb3⟩ := thin_X0_r1_decay hν hμ hε hc hρo0 hρo hth hN τ 3
  refine ⟨B0 + B1 + B2 + B3, ?_, fun _ => rfl, fun y' hy' => ?_, fun n hn y' hy' => ?_⟩
  · positivity
  · have hrOut_le := rOut_le_22_23_r1 hν hε hρo
    have hr₁0 : 0 < (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν) := by positivity
    have hy'_mem : ρo / ε < ϱ y' := by linarith
    have hopen : IsOpen {y : Space | ρo / ε < ϱ y} := isOpen_lt continuous_const continuous_ϱ
    exact (thin_X0_contDiffOn_top hν hμ hε hc hρo0 hth hN τ).contDiffAt (hopen.mem_nhds hy'_mem)
  · have hr₁0 : 0 < (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν) := by positivity
    have hρ0 : 0 ≤ (ϱ y') ^ (-4 - (n : ℝ)) := Real.rpow_nonneg (lt_trans hr₁0 hy').le _
    interval_cases n
    · exact (hb0 y' hy').trans (mul_le_mul_of_nonneg_right (by linarith) hρ0)
    · exact (hb1 y' hy').trans (mul_le_mul_of_nonneg_right (by linarith) hρ0)
    · exact (hb2 y' hy').trans (mul_le_mul_of_nonneg_right (by linarith) hρ0)
    · exact (hb3 y' hy').trans (mul_le_mul_of_nonneg_right (by linarith) hρ0)

/-- On `{y' | r₁ < ϱ y'}`, `commPsi ν μ R χy (srcX0 ν μ (thinSource ε F)) τ y'` equals
`phiScalar ν R χy (fun _ => srcX0 ν μ (thinSource ε F) τ) y' • coordinateVector 2`. -/
theorem thin_commPsi_eq_phiScalar {ν μ R ε c ρo : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo0 : 0 ≤ ρo)
    (hρo : ρo ≤ Real.sqrt (5 * ν / 6))
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    (τ : ℝ) {y : Space} (hy : (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν) < ϱ y) :
    commPsi ν μ R χy (srcX0 ν μ (IIIa.thinSource ε F)) τ y =
      phiScalar ν R χy (fun _ => srcX0 ν μ (IIIa.thinSource ε F) τ) y •
        (UnforcedLeray.coordinateVector 2 : Space) := by
  set Z : ℝ → Space → Space := srcX0 ν μ (IIIa.thinSource ε F)
  set Zc : ℝ → Space → Space := fun _ => Z τ
  set r₁ : ℝ := (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν)
  have hr₁ : 0 < r₁ := by dsimp [r₁]; positivity
  have hρ : 0 < ϱ y := lt_trans hr₁ hy
  have hy_out : ρo / ε < ϱ y :=
    ((rOut_le_22_23_r1 hν hε hρo).trans (mul_le_mul_of_nonneg_left hy.le (by norm_num))).trans_lt
      (by linarith)
  obtain ⟨B, hZc⟩ := thin_validPsiFieldWith hν hμ hε hc hρo0 hρo hth hN τ
  set F0 := tcF0 ν R χy
  set r := ϱ y
  set z := y 2
  have hF_c2 : ContDiffAt ℝ 2 F0 r := tcle_f0_smooth hχ ν R hρ.ne'
  have hF_diff : DifferentiableAt ℝ F0 r := hF_c2.differentiableAt (by norm_num)
  -- 1. Time derivative of `cutPsi`
  obtain ⟨hi2, hd_out⟩ := thin_outPrim_tau hν hμ hε hc hρo0 hth hN τ hy_out
  have ht_cut : deriv (fun t => cutPsi ν R χy Z t y) τ =
      (F0 r * outPrim (fun t y'' => deriv (fun s => Z s y'') t) τ r z) •
        (UnforcedLeray.coordinateVector 2 : Space) := by
    have hhd : HasDerivAt (fun t => cutPsi ν R χy Z t y)
        (F0 r • (outPrim (fun t y'' => deriv (fun s => Z s y'') t) τ r z •
          (UnforcedLeray.coordinateVector 2 : Space))) τ :=
      (hd_out.smul_const (UnforcedLeray.coordinateVector 2)).const_smul (F0 r)
    rw [hhd.deriv, smul_smul]
  -- 2. Dilation derivative `fderiv ℝ (cutPsi ν R χy Z τ) y y`
  have hcut_tau : cutPsi ν R χy Z τ =
      fun y' => (F0 (ϱ y') * outPrim Zc 0 (ϱ y') (y' 2)) •
        (UnforcedLeray.coordinateVector 2 : Space) := by
    funext y'; unfold cutPsi psiFld Zc; rw [mul_smul]; rfl
  have hF_comp : HasFDerivAt (fun y' : Space => F0 (ϱ y')) (deriv F0 r • ϱD y) y :=
    tcle_hasFDeriv_comp hρ hF_diff
  have hu0_fd := hZc.hasDecay45_self.hasFDerivAt_outPrim hr₁ hy
  have hcut_fd := (hF_comp.mul hu0_fd).smul_const (UnforcedLeray.coordinateVector 2 : Space)
  have hD_cut : fderiv ℝ (cutPsi ν R χy Z τ) y y =
      (r * deriv F0 r * outPrim Zc 0 r z +
        F0 r * (r ^ 2 * Zc 0 (hpt r z) 2 - z * primDz Zc 0 r z)) •
        (UnforcedLeray.coordinateVector 2 : Space) := by
    rw [hcut_tau]
    change fderiv ℝ (fun y' => ((fun y'' => F0 (ϱ y'')) * fun y'' => outPrim Zc 0 (ϱ y'') (y'' 2)) y' •
      (UnforcedLeray.coordinateVector 2 : Space)) y y = _
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
  have hcut_eq_Zc : cutPsi ν R χy Z τ = cutPsi ν R χy Zc 0 := rfl
  have hLap_cut : physLap (cutPsi ν R χy Z τ) y =
      ((deriv (deriv F0) r + deriv F0 r / r) * outPrim Zc 0 r z +
        (2 * r * deriv F0 r + 2 * F0 r) * Zc 0 (hpt r z) 2 +
        r * F0 r * physPd (Zc 0) 0 (hpt r z) 2 +
        F0 r * outPrim (fun _ w => physPd2 (Zc 0) 2 2 w) 0 r z) •
        (UnforcedLeray.coordinateVector 2 : Space) := by
    rw [hcut_eq_Zc]
    exact physLap_cutPsi_eq ν R hχ hZc hr₁ 0 hy
  -- 4. `outPrim (physDmu ν (μ + 1) Z) τ r z`
  have i1 : IntegrableOn (fun ρ : ℝ => ρ * Z τ !₂[ρ, 0, z] 2) (Ioi r) :=
    (hZc.hasDecay45_self.primData hr₁ hy z).1
  obtain ⟨i3, heuler⟩ := outPrim_euler_eq hZc hr₁ hy z
  have i4 : IntegrableOn (fun ρ : ℝ => ρ * (physLap (Z τ) !₂[ρ, 0, z]) 2) (Ioi r) :=
    ((hZc.hasDecay45_physLap hr₁).primData hr₁ hy z).1
  have hout_lin := tcle_outPrim_lin ν (μ + 1) Z τ r z i1 hi2 i3 i4
  have hout_D : outPrim (fun t y' => fderiv ℝ (Z t) y' y') τ r z =
      r ^ 2 * Zc 0 (hpt r z) 2 - 2 * outPrim Zc 0 r z - z * primDz Zc 0 r z := heuler
  have hout_L : outPrim (fun t y' => physLap (Z t) y') τ r z =
      outPrim (fun _ w => physLap (Zc 0) w) 0 r z := rfl
  have hout_Z : outPrim Z τ r z = outPrim Zc 0 r z := rfl
  -- 5. Combine into `commPsi`
  unfold commPsi
  have hDW : physDmu ν (μ + 1) (cutPsi ν R χy Z) τ y =
      deriv (fun t => cutPsi ν R χy Z t y) τ -
        (1 / 2 : ℝ) • fderiv ℝ (cutPsi ν R χy Z τ) y y -
          ν • physLap (cutPsi ν R χy Z τ) y +
            (μ + 1 - 1 / 2) • cutPsi ν R χy Z τ y := rfl
  have hcut_DZ : cutPsi ν R χy (physDmu ν (μ + 1) Z) τ y =
      (F0 r * outPrim (physDmu ν (μ + 1) Z) τ r z) •
        (UnforcedLeray.coordinateVector 2 : Space) := by
    unfold cutPsi psiFld; rw [mul_smul]
  have hcut_Z : cutPsi ν R χy Z τ y =
      (F0 r * outPrim Zc 0 r z) • (UnforcedLeray.coordinateVector 2 : Space) := by
    rw [hcut_tau]
  rw [hDW, hcut_DZ, ht_cut, hD_cut, hLap_cut, hcut_Z, hout_lin, hout_D, hout_L, hout_Z]
  simp only [← mul_smul, ← sub_smul, ← add_smul]
  congr 1
  unfold phiScalar tcB1 tcB2
  change _ = (-(1 / 2) * (r * deriv F0 r + 2 * F0 r) -
        ν * (deriv (deriv F0) r + deriv F0 r / r)) * outPrim Zc 0 r z +
      (-2 * ν * (r * deriv F0 r + F0 r)) * Zc 0 (hpt r z) 2 -
      ν * (F0 r * r) * physPd (Zc 0) 0 (hpt r z) 2 -
      ν * F0 r * outPrim (fun _ w => physPd2 (Zc 0) 2 2 w) 0 r z +
      ν * F0 r * outPrim (fun _ w => physLap (Zc 0) w) 0 r z
  ring

/-! ## 4. Quantitative derivative bound of `phiScalar` in terms of `ptNorm` and `rayInt` -/

/-- Pointwise norm of `iteratedFDeriv ℝ j g` at `hpt r z`. -/
def ptNorm (g : Space → Space) (j : ℕ) (r z : ℝ) : ℝ :=
  ‖iteratedFDeriv ℝ j g (hpt r z)‖

/-- Outward ray integral `∫ ρ in Ioi r, ρ * ‖iteratedFDeriv ℝ j g (hpt ρ z)‖`. -/
def rayInt (g : Space → Space) (j : ℕ) (r z : ℝ) : ℝ :=
  ∫ ρ in Ioi r, ρ * ‖iteratedFDeriv ℝ j g (hpt ρ z)‖

theorem integrableOn_ray_iteratedFDeriv {r₁ B : ℝ} {W : ℝ → Space → Space}
    (hW : ValidPsiFieldWith r₁ B W) (hr₁ : 0 < r₁) {r : ℝ} (hr : r₁ < r) (z : ℝ)
    {j : ℕ} (hj : j ≤ 3) :
    IntegrableOn (fun ρ : ℝ => ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) (Ioi r) := by
  have hr0 : 0 < r := lt_trans hr₁ hr
  have hdom : IntegrableOn (fun ρ : ℝ => B * ρ ^ (-3 - (j : ℝ))) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt
      (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) hr0).const_mul B
  have hopen : IsOpen {w : Space | r₁ < ϱ w} := isOpen_lt continuous_const continuous_ϱ
  have hcd_on : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W 0) {w : Space | r₁ < ϱ w} :=
    fun w hw => (hW.smooth w hw).contDiffWithinAt
  have hcont_iter : ContinuousOn (iteratedFDeriv ℝ j (W 0)) {w : Space | r₁ < ϱ w} :=
    ContinuousOn.continuousOn_iteratedFDeriv hcd_on hopen (by exact_mod_cast le_top)
  have hcont : ContinuousOn (fun ρ : ℝ => ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) (Ioi r) := by
    intro ρ hρ
    have hρ1 : r₁ < ρ := lt_trans hr hρ
    have hρ0 : 0 < ρ := lt_trans hr0 hρ
    have hmem : hpt ρ z ∈ {w : Space | r₁ < ϱ w} := by
      change r₁ < ϱ (hpt ρ z)
      rw [ϱ_hpt_of_pos hρ0]
      exact hρ1
    have hca_iter : ContinuousAt (iteratedFDeriv ℝ j (W 0)) (hpt ρ z) :=
      hcont_iter.continuousAt (hopen.mem_nhds hmem)
    have hca : ContinuousAt (fun s : ℝ => ‖iteratedFDeriv ℝ j (W 0) (hpt s z)‖) ρ :=
      ContinuousAt.comp (g := fun w => ‖iteratedFDeriv ℝ j (W 0) w‖) (f := fun s => hpt s z)
        (continuous_norm.continuousAt.comp hca_iter) (continuous_hpt' z).continuousAt
    exact (continuousAt_id.mul hca).continuousWithinAt
  refine Integrable.mono' hdom (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
  have hρ1 : r₁ < ρ := lt_trans hr hρ
  have hρ0 : 0 < ρ := lt_trans hr0 hρ
  have hb := hW.decay j hj (hpt ρ z) (by rw [ϱ_hpt_of_pos hρ0]; exact hρ1)
  rw [ϱ_hpt_of_pos hρ0] at hb
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ0, abs_norm]
  calc ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖
      ≤ ρ * (B * ρ ^ (-4 - (j : ℝ))) := mul_le_mul_of_nonneg_left hb hρ0.le
    _ = B * (ρ ^ (1 : ℝ) * ρ ^ (-4 - (j : ℝ))) := by rw [Real.rpow_one]; ring
    _ = B * ρ ^ (-3 - (j : ℝ)) := by
        rw [← Real.rpow_add hρ0]
        congr 2; ring

private theorem outPrim_le_rayInt {r₁ B : ℝ} {W U : ℝ → Space → Space}
    (hW : ValidPsiFieldWith r₁ B W) (hr₁ : 0 < r₁) {r : ℝ} (hr : r₁ < r) (z : ℝ)
    {j : ℕ} (hj : j ≤ 3) {c₀ : ℝ} (_hc₀ : 0 ≤ c₀)
    (hU : ∀ w, r₁ < ϱ w → ‖U 0 w‖ ≤ c₀ * ‖iteratedFDeriv ℝ j (W 0) w‖) :
    |outPrim U 0 r z| ≤ c₀ * rayInt (W 0) j r z := by
  have hr0 : 0 < r := lt_trans hr₁ hr
  have hint := (integrableOn_ray_iteratedFDeriv hW hr₁ hr z hj).const_mul c₀
  have hbd : ∀ᵐ ρ ∂(volume.restrict (Ioi r)),
      ‖ρ * U 0 (hpt ρ z) 2‖ ≤ c₀ * (ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    have hρ1 : r₁ < ρ := lt_trans hr hρ
    have hρ0 : 0 < ρ := lt_trans hr0 hρ
    have h1 := hU (hpt ρ z) (by rw [ϱ_hpt_of_pos hρ0]; exact hρ1)
    have h2 : |U 0 (hpt ρ z) 2| ≤ ‖U 0 (hpt ρ z)‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (U 0 (hpt ρ z)) 2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ0]
    calc ρ * |U 0 (hpt ρ z) 2| ≤ ρ * (c₀ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) :=
          mul_le_mul_of_nonneg_left (h2.trans h1) hρ0.le
      _ = c₀ * (ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) := by ring
  unfold outPrim rayInt
  rw [abs_neg, ← Real.norm_eq_abs]
  calc ‖∫ ρ in Ioi r, ρ * U 0 !₂[ρ, 0, z] 2‖
      ≤ ∫ ρ in Ioi r, c₀ * (ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) :=
        norm_integral_le_of_norm_le hint hbd
    _ = c₀ * ∫ ρ in Ioi r, ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖ := integral_const_mul _ _

private theorem primDz_le_rayInt {r₁ B : ℝ} {W U : ℝ → Space → Space}
    (hW : ValidPsiFieldWith r₁ B W) (hr₁ : 0 < r₁) {r : ℝ} (hr : r₁ < r) (z : ℝ)
    {j : ℕ} (hj : j ≤ 3) {c₁ : ℝ} (_hc₁ : 0 ≤ c₁)
    (hU : ∀ w, r₁ < ϱ w → ‖fderiv ℝ (U 0) w‖ ≤ c₁ * ‖iteratedFDeriv ℝ j (W 0) w‖) :
    |primDz U 0 r z| ≤ c₁ * rayInt (W 0) j r z := by
  have hr0 : 0 < r := lt_trans hr₁ hr
  have hint := (integrableOn_ray_iteratedFDeriv hW hr₁ hr z hj).const_mul c₁
  have hbd : ∀ᵐ ρ ∂(volume.restrict (Ioi r)),
      ‖ρ * fderiv ℝ (U 0) (hpt ρ z) (UnforcedLeray.coordinateVector 2) 2‖ ≤
        c₁ * (ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    have hρ1 : r₁ < ρ := lt_trans hr hρ
    have hρ0 : 0 < ρ := lt_trans hr0 hρ
    have h1 := hU (hpt ρ z) (by rw [ϱ_hpt_of_pos hρ0]; exact hρ1)
    have h2 : |fderiv ℝ (U 0) (hpt ρ z) (UnforcedLeray.coordinateVector 2) 2| ≤
        ‖fderiv ℝ (U 0) (hpt ρ z)‖ := by
      have hp := PiLp.norm_apply_le
        (fderiv ℝ (U 0) (hpt ρ z) (UnforcedLeray.coordinateVector 2)) 2
      rw [Real.norm_eq_abs] at hp
      refine hp.trans ?_
      calc ‖fderiv ℝ (U 0) (hpt ρ z) (UnforcedLeray.coordinateVector 2)‖
          ≤ ‖fderiv ℝ (U 0) (hpt ρ z)‖ * ‖(UnforcedLeray.coordinateVector 2 : Space)‖ :=
            (fderiv ℝ (U 0) (hpt ρ z)).le_opNorm _
        _ = ‖fderiv ℝ (U 0) (hpt ρ z)‖ := by rw [norm_e 2, mul_one]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ0]
    calc ρ * |fderiv ℝ (U 0) (hpt ρ z) (UnforcedLeray.coordinateVector 2) 2|
        ≤ ρ * (c₁ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) :=
          mul_le_mul_of_nonneg_left (h2.trans h1) hρ0.le
      _ = c₁ * (ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) := by ring
  unfold primDz rayInt
  rw [← Real.norm_eq_abs]
  calc ‖∫ ρ in Ioi r, ρ * fderiv ℝ (U 0) (hpt ρ z) (UnforcedLeray.coordinateVector 2) 2‖
      ≤ ∫ ρ in Ioi r, c₁ * (ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖) :=
        norm_integral_le_of_norm_le hint hbd
    _ = c₁ * ∫ ρ in Ioi r, ρ * ‖iteratedFDeriv ℝ j (W 0) (hpt ρ z)‖ := integral_const_mul _ _

private theorem hasFDerivAt_coeff_mul_outPrim_raw {r₁ B A₀ A₁ : ℝ} {W U : ℝ → Space → Space}
    (hW : ValidPsiFieldWith r₁ B W) (hU : HasDecay45 r₁ A₀ A₁ U) (hr₁ : 0 < r₁)
    {j : ℕ} (hj : j + 1 ≤ 3) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hb0 : ∀ w, r₁ < ϱ w → ‖U 0 w‖ ≤ c₀ * ‖iteratedFDeriv ℝ j (W 0) w‖)
    (hb1 : ∀ w, r₁ < ϱ w → ‖fderiv ℝ (U 0) w‖ ≤ c₀ * ‖iteratedFDeriv ℝ (j + 1) (W 0) w‖)
    {g : ℝ → ℝ} {g' : ℝ} {y : Space} (hy : r₁ < ϱ y) (hg : HasDerivAt g g' (ϱ y)) :
    ∃ L : Space →L[ℝ] ℝ,
      HasFDerivAt (fun y' : Space => g (ϱ y') * outPrim U 0 (ϱ y') (y' 2)) L y ∧
      ‖L‖ ≤ |g'| * c₀ * rayInt (W 0) j (ϱ y) (y 2) +
        |g (ϱ y)| * c₀ * (ϱ y * ptNorm (W 0) j (ϱ y) (y 2) + rayInt (W 0) (j + 1) (ϱ y) (y 2)) := by
  have hρy : 0 < ϱ y := lt_trans hr₁ hy
  have hgc : HasFDerivAt (fun y' : Space => g (ϱ y')) (g' • ϱD y) y :=
    hg.comp_hasFDerivAt y (hasFDerivAt_ϱ (tcle_notaxis hρy))
  have hu := hU.hasFDerivAt_outPrim hr₁ hy
  refine ⟨_, hgc.mul hu, ?_⟩
  have hϱn : ‖ϱD y‖ ≤ 1 := wgx_norm_ϱD_le hρy
  have hp2n : ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v 2
  have hpt_nn : ∀ k : ℕ, 0 ≤ ptNorm (W 0) k (ϱ y) (y 2) := fun _ => norm_nonneg _
  have hray_nn : ∀ k : ℕ, 0 ≤ rayInt (W 0) k (ϱ y) (y 2) := fun k =>
    setIntegral_nonneg measurableSet_Ioi fun ρ hρ =>
      mul_nonneg (lt_trans hρy hρ).le (norm_nonneg _)
  have hpt_j := hpt_nn j
  have hray_j := hray_nn j
  have hray_j1 := hray_nn (j + 1)
  have hu_val := outPrim_le_rayInt hW hr₁ hy (y 2) (by omega) hc₀ hb0
  have hdz_val := primDz_le_rayInt hW hr₁ hy (y 2) hj hc₀ hb1
  have hU_val : |U 0 (hpt (ϱ y) (y 2)) 2| ≤ c₀ * ptNorm (W 0) j (ϱ y) (y 2) := by
    have h1 := hb0 (hpt (ϱ y) (y 2)) (by rw [ϱ_hpt_of_pos hρy]; exact hy)
    have h2 : |U 0 (hpt (ϱ y) (y 2)) 2| ≤ ‖U 0 (hpt (ϱ y) (y 2))‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (U 0 (hpt (ϱ y) (y 2))) 2
    exact h2.trans h1
  have hrU : |ϱ y * U 0 (hpt (ϱ y) (y 2)) 2| ≤ c₀ * (ϱ y * ptNorm (W 0) j (ϱ y) (y 2)) := by
    rw [abs_mul, abs_of_pos hρy]
    calc ϱ y * |U 0 (hpt (ϱ y) (y 2)) 2| ≤ ϱ y * (c₀ * ptNorm (W 0) j (ϱ y) (y 2)) :=
          mul_le_mul_of_nonneg_left hU_val hρy.le
      _ = c₀ * (ϱ y * ptNorm (W 0) j (ϱ y) (y 2)) := by ring
  have hdu_norm : ‖(ϱ y * U 0 (hpt (ϱ y) (y 2)) 2) • ϱD y +
      (-primDz U 0 (ϱ y) (y 2)) • (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤
      c₀ * (ϱ y * ptNorm (W 0) j (ϱ y) (y 2) + rayInt (W 0) (j + 1) (ϱ y) (y 2)) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    calc |ϱ y * U 0 (hpt (ϱ y) (y 2)) 2| * ‖ϱD y‖ +
          |primDz U 0 (ϱ y) (y 2)| * ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖
        ≤ (c₀ * (ϱ y * ptNorm (W 0) j (ϱ y) (y 2))) * 1 +
          (c₀ * rayInt (W 0) (j + 1) (ϱ y) (y 2)) * 1 := by gcongr
      _ = c₀ * (ϱ y * ptNorm (W 0) j (ϱ y) (y 2) + rayInt (W 0) (j + 1) (ϱ y) (y 2)) := by ring
  have h1 : ‖g (ϱ y) • ((ϱ y * U 0 (hpt (ϱ y) (y 2)) 2) • ϱD y +
      (-primDz U 0 (ϱ y) (y 2)) • (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ))‖ ≤
      |g (ϱ y)| * c₀ * (ϱ y * ptNorm (W 0) j (ϱ y) (y 2) + rayInt (W 0) (j + 1) (ϱ y) (y 2)) := by
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left hdu_norm (abs_nonneg _)
  have h2 : ‖outPrim U 0 (ϱ y) (y 2) • (g' • ϱD y)‖ ≤
      |g'| * c₀ * rayInt (W 0) j (ϱ y) (y 2) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |outPrim U 0 (ϱ y) (y 2)| * (|g'| * ‖ϱD y‖)
        ≤ (c₀ * rayInt (W 0) j (ϱ y) (y 2)) * (|g'| * 1) := by gcongr
      _ = |g'| * c₀ * rayInt (W 0) j (ϱ y) (y 2) := by ring
  refine (norm_add_le _ _).trans ?_
  linarith [h1, h2]

private theorem hasFDerivAt_coeff_mul_hpt_raw {r₁ A₀ A₁ : ℝ} {W U : ℝ → Space → Space}
    (hU : HasDecay45 r₁ A₀ A₁ U) (hr₁ : 0 < r₁)
    {j : ℕ} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hb0 : ∀ w, r₁ < ϱ w → ‖U 0 w‖ ≤ c₀ * ‖iteratedFDeriv ℝ j (W 0) w‖)
    (hb1 : ∀ w, r₁ < ϱ w → ‖fderiv ℝ (U 0) w‖ ≤ c₀ * ‖iteratedFDeriv ℝ (j + 1) (W 0) w‖)
    {g : ℝ → ℝ} {g' : ℝ} {y : Space} (hy : r₁ < ϱ y) (hg : HasDerivAt g g' (ϱ y)) :
    ∃ L : Space →L[ℝ] ℝ,
      HasFDerivAt (fun y' : Space => g (ϱ y') * U 0 (hpt (ϱ y') (y' 2)) 2) L y ∧
      ‖L‖ ≤ |g'| * c₀ * ptNorm (W 0) j (ϱ y) (y 2) +
        2 * |g (ϱ y)| * c₀ * ptNorm (W 0) (j + 1) (ϱ y) (y 2) := by
  have hρy : 0 < ϱ y := lt_trans hr₁ hy
  have hgc : HasFDerivAt (fun y' : Space => g (ϱ y')) (g' • ϱD y) y :=
    hg.comp_hasFDerivAt y (hasFDerivAt_ϱ (tcle_notaxis hρy))
  have hz := hU.hasFDerivAt_hpt_eval2 hr₁ hy
  refine ⟨_, hgc.mul hz, ?_⟩
  have hϱn : ‖ϱD y‖ ≤ 1 := wgx_norm_ϱD_le hρy
  have hp2n : ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v 2
  have hpt_j : 0 ≤ ptNorm (W 0) j (ϱ y) (y 2) := norm_nonneg _
  have hpt_j1 : 0 ≤ ptNorm (W 0) (j + 1) (ϱ y) (y 2) := norm_nonneg _
  have hU_val : |U 0 (hpt (ϱ y) (y 2)) 2| ≤ c₀ * ptNorm (W 0) j (ϱ y) (y 2) := by
    have h1 := hb0 (hpt (ϱ y) (y 2)) (by rw [ϱ_hpt_of_pos hρy]; exact hy)
    have h2 : |U 0 (hpt (ϱ y) (y 2)) 2| ≤ ‖U 0 (hpt (ϱ y) (y 2))‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (U 0 (hpt (ϱ y) (y 2))) 2
    exact h2.trans h1
  have hpd_le : ∀ l : Fin 3,
      |physPd (U 0) l (hpt (ϱ y) (y 2)) 2| ≤ c₀ * ptNorm (W 0) (j + 1) (ϱ y) (y 2) := by
    intro l
    have h1 := hb1 (hpt (ϱ y) (y 2)) (by rw [ϱ_hpt_of_pos hρy]; exact hy)
    have h2 : |physPd (U 0) l (hpt (ϱ y) (y 2)) 2| ≤ ‖fderiv ℝ (U 0) (hpt (ϱ y) (y 2))‖ := by
      unfold physPd
      have hp := PiLp.norm_apply_le
        (fderiv ℝ (U 0) (hpt (ϱ y) (y 2)) (UnforcedLeray.coordinateVector l)) 2
      rw [Real.norm_eq_abs] at hp
      refine hp.trans ?_
      calc ‖fderiv ℝ (U 0) (hpt (ϱ y) (y 2)) (UnforcedLeray.coordinateVector l)‖
          ≤ ‖fderiv ℝ (U 0) (hpt (ϱ y) (y 2))‖ * ‖(UnforcedLeray.coordinateVector l : Space)‖ :=
            (fderiv ℝ (U 0) (hpt (ϱ y) (y 2))).le_opNorm _
        _ = ‖fderiv ℝ (U 0) (hpt (ϱ y) (y 2))‖ := by rw [norm_e l, mul_one]
    exact h2.trans h1
  have hdz_norm : ‖(physPd (U 0) 0 (hpt (ϱ y) (y 2)) 2) • ϱD y +
      (physPd (U 0) 2 (hpt (ϱ y) (y 2)) 2) •
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤
      2 * c₀ * ptNorm (W 0) (j + 1) (ϱ y) (y 2) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hp0 := hpd_le 0
    have hp2 := hpd_le 2
    calc |physPd (U 0) 0 (hpt (ϱ y) (y 2)) 2| * ‖ϱD y‖ +
          |physPd (U 0) 2 (hpt (ϱ y) (y 2)) 2| * ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖
        ≤ (c₀ * ptNorm (W 0) (j + 1) (ϱ y) (y 2)) * 1 +
          (c₀ * ptNorm (W 0) (j + 1) (ϱ y) (y 2)) * 1 := by gcongr
      _ = 2 * c₀ * ptNorm (W 0) (j + 1) (ϱ y) (y 2) := by ring
  have h1 : ‖g (ϱ y) • ((physPd (U 0) 0 (hpt (ϱ y) (y 2)) 2) • ϱD y +
      (physPd (U 0) 2 (hpt (ϱ y) (y 2)) 2) •
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ))‖ ≤
      2 * |g (ϱ y)| * c₀ * ptNorm (W 0) (j + 1) (ϱ y) (y 2) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |g (ϱ y)| * ‖(physPd (U 0) 0 (hpt (ϱ y) (y 2)) 2) • ϱD y +
            (physPd (U 0) 2 (hpt (ϱ y) (y 2)) 2) •
              (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖
        ≤ |g (ϱ y)| * (2 * c₀ * ptNorm (W 0) (j + 1) (ϱ y) (y 2)) :=
          mul_le_mul_of_nonneg_left hdz_norm (abs_nonneg _)
      _ = 2 * |g (ϱ y)| * c₀ * ptNorm (W 0) (j + 1) (ϱ y) (y 2) := by ring
  have h2 : ‖U 0 (hpt (ϱ y) (y 2)) 2 • (g' • ϱD y)‖ ≤
      |g'| * c₀ * ptNorm (W 0) j (ϱ y) (y 2) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |U 0 (hpt (ϱ y) (y 2)) 2| * (|g'| * ‖ϱD y‖)
        ≤ (c₀ * ptNorm (W 0) j (ϱ y) (y 2)) * (|g'| * 1) := by gcongr
      _ = |g'| * c₀ * ptNorm (W 0) j (ϱ y) (y 2) := by ring
  refine (norm_add_le _ _).trans ?_
  linarith [h1, h2]

set_option maxHeartbeats 800000 in
theorem fderiv_phiScalar_raw_bound {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν R B : ℝ) (W : ℝ → Space → Space),
      0 < ν → ν ≤ 1 → 1 ≤ R →
      ValidPsiFieldWith ((23 / 24 : ℝ) * (R * Real.sqrt ν)) B W →
      ∀ y : Space, y ∈ streamAnn ν R →
        DifferentiableAt ℝ (phiScalar ν R χy W) y ∧
        ‖fderiv ℝ (phiScalar ν R χy W) y‖ ≤ C * (
          (R * Real.sqrt ν)⁻¹ * ptNorm (W 0) 0 (ϱ y) (y 2) +
          ptNorm (W 0) 1 (ϱ y) (y 2) +
          (R * Real.sqrt ν)⁻¹ * ptNorm (W 0) 2 (ϱ y) (y 2) +
          ((R * Real.sqrt ν)⁻¹) ^ 3 * rayInt (W 0) 0 (ϱ y) (y 2) +
          ((R * Real.sqrt ν)⁻¹) ^ 2 * rayInt (W 0) 1 (ϱ y) (y 2) +
          (R * Real.sqrt ν)⁻¹ * rayInt (W 0) 2 (ϱ y) (y 2) +
          rayInt (W 0) 3 (ϱ y) (y 2)) := by
  obtain ⟨C0, hC0, hcoef⟩ := tcCoeff χy hχ
  obtain ⟨C1, hC1, hder⟩ := wgy_coeff_deriv hχ
  obtain ⟨M, hM0, hM⟩ := wgyc_profile χy hχ
  refine ⟨20 * (C0 + C1 + M), by positivity, ?_⟩
  intro ν R B W hν hν1 hR1 hW y hyann
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
  have hρy : 0 < ϱ y := lt_trans hr₁ hy
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
    ((tcle_f0_smooth hχ ν R hρy.ne').differentiableAt (by norm_num)).hasDerivAt
  -- Norm comparison lemmas for W, physPd, physPd2, physLap
  have hbW0 : ∀ w, r₁ < ϱ w → ‖W 0 w‖ ≤ 1 * ‖iteratedFDeriv ℝ 0 (W 0) w‖ := fun w _ => by
    rw [one_mul]; exact norm_self_le_iter0
  have hbW1 : ∀ w, r₁ < ϱ w → ‖fderiv ℝ (W 0) w‖ ≤ 1 * ‖iteratedFDeriv ℝ 1 (W 0) w‖ := fun w _ => by
    rw [one_mul]; exact norm_fderiv_le_iter1
  have hbPd0 : ∀ w, r₁ < ϱ w → ‖physPd (W 0) 0 w‖ ≤ 1 * ‖iteratedFDeriv ℝ 1 (W 0) w‖ :=
    fun w hw => by
      rw [one_mul]
      exact norm_self_le_iter0.trans (norm_iteratedFDeriv_physPd_le_at 0 (hW.smooth w hw) 0)
  have hbPd1 : ∀ w, r₁ < ϱ w →
      ‖fderiv ℝ (physPd (W 0) 0) w‖ ≤ 1 * ‖iteratedFDeriv ℝ 2 (W 0) w‖ :=
    fun w hw => by
      rw [one_mul]
      exact norm_fderiv_le_iter1.trans (norm_iteratedFDeriv_physPd_le_at 1 (hW.smooth w hw) 0)
  have hbPd22_0 : ∀ j l : Fin 3, ∀ w, r₁ < ϱ w →
      ‖physPd2 (W 0) j l w‖ ≤ 1 * ‖iteratedFDeriv ℝ 2 (W 0) w‖ :=
    fun j l w hw => by
      rw [one_mul]
      exact (norm_self_le_iter0.trans
        (norm_iteratedFDeriv_physPd_le_at 0 (contDiffAt_physPd (hW.smooth w hw) l) j)).trans
        (norm_iteratedFDeriv_physPd_le_at 1 (hW.smooth w hw) l)
  have hbPd22_1 : ∀ j l : Fin 3, ∀ w, r₁ < ϱ w →
      ‖fderiv ℝ (physPd2 (W 0) j l) w‖ ≤ 1 * ‖iteratedFDeriv ℝ 3 (W 0) w‖ :=
    fun j l w hw => by
      rw [one_mul]
      exact (norm_fderiv_le_iter1.trans
        (norm_iteratedFDeriv_physPd_le_at 1 (contDiffAt_physPd (hW.smooth w hw) l) j)).trans
        (norm_iteratedFDeriv_physPd_le_at 2 (hW.smooth w hw) l)
  have hbLap0 : ∀ w, r₁ < ϱ w → ‖physLap (W 0) w‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 (W 0) w‖ :=
    fun w hw => by
      unfold physLap
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j : Fin 3, ‖physPd2 (W 0) j j w‖
          ≤ ∑ _j : Fin 3, 1 * ‖iteratedFDeriv ℝ 2 (W 0) w‖ :=
            Finset.sum_le_sum fun j _ => hbPd22_0 j j w hw
        _ = 3 * ‖iteratedFDeriv ℝ 2 (W 0) w‖ := by simp [Finset.sum_const]
  have hbLap1 : ∀ w, r₁ < ϱ w →
      ‖fderiv ℝ (physLap (W 0)) w‖ ≤ 3 * ‖iteratedFDeriv ℝ 3 (W 0) w‖ :=
    fun w hw => by
      have hd : ∀ j : Fin 3, DifferentiableAt ℝ (physPd2 (W 0) j j) w :=
        fun j => (hW.hasDecay45_physPd2 hr₁ j j).diff w hw
      have heq : fderiv ℝ (physLap (W 0)) w = ∑ j : Fin 3, fderiv ℝ (physPd2 (W 0) j j) w := by
        unfold physLap
        exact fderiv_fun_sum fun j _ => hd j
      rw [heq]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j : Fin 3, ‖fderiv ℝ (physPd2 (W 0) j j) w‖
          ≤ ∑ _j : Fin 3, 1 * ‖iteratedFDeriv ℝ 3 (W 0) w‖ :=
            Finset.sum_le_sum fun j _ => hbPd22_1 j j w hw
        _ = 3 * ‖iteratedFDeriv ℝ 3 (W 0) w‖ := by simp [Finset.sum_const]
  -- Term 1: `tcB1 * outPrim W`
  obtain ⟨L1, hL1, hL1b⟩ :=
    hasFDerivAt_coeff_mul_outPrim_raw hW hW.hasDecay45_self hr₁ (j := 0) (by omega)
      zero_le_one hbW0 hbW1 hy hB1
  -- Term 2: `tcB2 * W 0 (hpt (ϱ y') (y' 2)) 2`
  obtain ⟨L2, hL2, hL2b⟩ :=
    hasFDerivAt_coeff_mul_hpt_raw (W := W) hW.hasDecay45_self hr₁ (j := 0)
      zero_le_one hbW0 hbW1 hy hB2
  -- Term 3: `(-ν * (tcF0 r * r)) * physPd (W 0) 0`
  have hg3_hd : HasDerivAt (fun r => -ν * (tcF0 ν R χy r * r))
      (-ν * (deriv (tcF0 ν R χy) (ϱ y) * ϱ y + tcF0 ν R χy (ϱ y) * 1)) (ϱ y) :=
    (hF_hd.mul (hasDerivAt_id (ϱ y))).const_mul (-ν)
  obtain ⟨L3, hL3, hL3b⟩ :=
    hasFDerivAt_coeff_mul_hpt_raw (W := W) (hW.hasDecay45_physPd hr₁ 0) hr₁ (j := 1)
      zero_le_one hbPd0 hbPd1 hy hg3_hd
  -- Term 4: `(-ν * tcF0 r) * outPrim (physPd2 (W 0) 2 2)`
  have hg4_hd : HasDerivAt (fun r => -ν * tcF0 ν R χy r)
      (-ν * deriv (tcF0 ν R χy) (ϱ y)) (ϱ y) :=
    hF_hd.const_mul (-ν)
  obtain ⟨L4, hL4, hL4b⟩ :=
    hasFDerivAt_coeff_mul_outPrim_raw hW (hW.hasDecay45_physPd2 hr₁ 2 2) hr₁ (j := 2) (by omega)
      zero_le_one (hbPd22_0 2 2) (hbPd22_1 2 2) hy hg4_hd
  -- Term 5: `(ν * tcF0 r) * outPrim (physLap (W 0))`
  have hg5_hd : HasDerivAt (fun r => ν * tcF0 ν R χy r)
      (ν * deriv (tcF0 ν R χy) (ϱ y)) (ϱ y) :=
    hF_hd.const_mul ν
  obtain ⟨L5, hL5, hL5b⟩ :=
    hasFDerivAt_coeff_mul_outPrim_raw hW (hW.hasDecay45_physLap hr₁) hr₁ (j := 2) (by omega)
      (by norm_num) hbLap0 hbLap1 hy hg5_hd
  have hphi_eq : phiScalar ν R χy W = fun y' =>
      (tcB1 ν R χy (ϱ y') * outPrim W 0 (ϱ y') (y' 2) +
        tcB2 ν R χy (ϱ y') * W 0 (hpt (ϱ y') (y' 2)) 2 +
        (-ν * (tcF0 ν R χy (ϱ y') * ϱ y')) * physPd (W 0) 0 (hpt (ϱ y') (y' 2)) 2 +
        (-ν * tcF0 ν R χy (ϱ y')) * outPrim (fun _ w => physPd2 (W 0) 2 2 w) 0 (ϱ y') (y' 2)) +
      (ν * tcF0 ν R χy (ϱ y')) * outPrim (fun _ w => physLap (W 0) w) 0 (ϱ y') (y' 2) := by
    funext y'; unfold phiScalar; ring
  have h_all : HasFDerivAt (phiScalar ν R χy W) ((((L1 + L2) + L3) + L4) + L5) y := by
    rw [hphi_eq]
    exact (((hL1.add hL2).add hL3).add hL4).add hL5
  refine ⟨h_all.differentiableAt, ?_⟩
  rw [h_all.fderiv]
  -- Nonnegativity of `ptNorm` and `rayInt`
  have hP_nn : ∀ j : ℕ, 0 ≤ ptNorm (W 0) j (ϱ y) (y 2) := fun _ => norm_nonneg _
  have hI_nn : ∀ j : ℕ, 0 ≤ rayInt (W 0) j (ϱ y) (y 2) := fun j =>
    setIntegral_nonneg measurableSet_Ioi fun ρ hρ =>
      mul_nonneg (lt_trans hρy hρ).le (norm_nonneg _)
  -- Bound each `‖L_i‖`
  have hB1_y : |tcB1 ν R χy (ϱ y)| * ϱ y ≤ 2 * C0 * s := by
    calc |tcB1 ν R χy (ϱ y)| * ϱ y ≤ (C0 * s ^ 2) * ϱ y := by gcongr
      _ = C0 * s * (s * ϱ y) := by ring
      _ ≤ C0 * s * 2 := by gcongr
      _ = 2 * C0 * s := by ring
  have t1 : ‖L1‖ ≤ C1 * s ^ 3 * rayInt (W 0) 0 (ϱ y) (y 2) +
      2 * C0 * s * ptNorm (W 0) 0 (ϱ y) (y 2) +
      C0 * s ^ 2 * rayInt (W 0) 1 (ϱ y) (y 2) := by
    have h1 := hL1b
    rw [mul_one, mul_one] at h1
    have h2 : |tcB1 ν R χy (ϱ y)| *
        (ϱ y * ptNorm (W 0) 0 (ϱ y) (y 2) + rayInt (W 0) 1 (ϱ y) (y 2)) =
        (|tcB1 ν R χy (ϱ y)| * ϱ y) * ptNorm (W 0) 0 (ϱ y) (y 2) +
          |tcB1 ν R χy (ϱ y)| * rayInt (W 0) 1 (ϱ y) (y 2) := by ring
    rw [h2] at h1
    have hI0 := hI_nn 0
    have hP0 := hP_nn 0
    have hI1 := hI_nn 1
    calc ‖L1‖
        ≤ |b1| * rayInt (W 0) 0 (ϱ y) (y 2) +
          ((|tcB1 ν R χy (ϱ y)| * ϱ y) * ptNorm (W 0) 0 (ϱ y) (y 2) +
            |tcB1 ν R χy (ϱ y)| * rayInt (W 0) 1 (ϱ y) (y 2)) := h1
      _ ≤ (C1 * s ^ 3) * rayInt (W 0) 0 (ϱ y) (y 2) +
          ((2 * C0 * s) * ptNorm (W 0) 0 (ϱ y) (y 2) +
            (C0 * s ^ 2) * rayInt (W 0) 1 (ϱ y) (y 2)) := by gcongr
      _ = _ := by ring
  have t2 : ‖L2‖ ≤ C1 * s * ptNorm (W 0) 0 (ϱ y) (y 2) +
      2 * C0 * ptNorm (W 0) 1 (ϱ y) (y 2) := by
    have h1 := hL2b
    rw [mul_one, mul_one] at h1
    have hP0 := hP_nn 0
    have hP1 := hP_nn 1
    calc ‖L2‖
        ≤ |b2| * ptNorm (W 0) 0 (ϱ y) (y 2) +
          2 * |tcB2 ν R χy (ϱ y)| * ptNorm (W 0) 1 (ϱ y) (y 2) := h1
      _ ≤ (C1 * s) * ptNorm (W 0) 0 (ϱ y) (y 2) +
          2 * C0 * ptNorm (W 0) 1 (ϱ y) (y 2) := by gcongr
  have bg3_val : |-ν * (tcF0 ν R χy (ϱ y) * ϱ y)| ≤ 2 * M * s := by
    rw [abs_mul, abs_neg, abs_of_pos hν, abs_mul, abs_of_pos hρy]
    calc ν * (|tcF0 ν R χy (ϱ y)| * ϱ y)
        ≤ 1 * (M * s ^ 2 * ϱ y) := by gcongr
      _ = M * s * (s * ϱ y) := by ring
      _ ≤ M * s * 2 := by gcongr
      _ = 2 * M * s := by ring
  have bg3_der : |-ν * (deriv (tcF0 ν R χy) (ϱ y) * ϱ y + tcF0 ν R χy (ϱ y) * 1)| ≤ 3 * M := by
    rw [abs_mul, abs_neg, abs_of_pos hν, mul_one]
    have hder_y : |deriv (tcF0 ν R χy) (ϱ y) * ϱ y| ≤ 2 * M * s ^ 2 := by
      rw [abs_mul, abs_of_pos hρy]
      calc |deriv (tcF0 ν R χy) (ϱ y)| * ϱ y ≤ (M * s ^ 3) * ϱ y := by gcongr
        _ = M * s ^ 2 * (s * ϱ y) := by ring
        _ ≤ M * s ^ 2 * 2 := by gcongr
        _ = 2 * M * s ^ 2 := by ring
    have htri : |deriv (tcF0 ν R χy) (ϱ y) * ϱ y + tcF0 ν R χy (ϱ y)| ≤
        2 * M * s ^ 2 + M * s ^ 2 :=
      (abs_add_le _ _).trans (add_le_add hder_y bF0)
    calc ν * |deriv (tcF0 ν R χy) (ϱ y) * ϱ y + tcF0 ν R χy (ϱ y)|
        ≤ ν * (2 * M * s ^ 2 + M * s ^ 2) := by gcongr
      _ = 3 * M * (ν * s ^ 2) := by ring
      _ ≤ 3 * M * 1 := by gcongr
      _ = 3 * M := mul_one _
  have t3 : ‖L3‖ ≤ 3 * M * ptNorm (W 0) 1 (ϱ y) (y 2) +
      4 * M * s * ptNorm (W 0) 2 (ϱ y) (y 2) := by
    have h1 := hL3b
    have hP1 := hP_nn 1
    have hP2 := hP_nn 2
    calc ‖L3‖
        ≤ |-ν * (deriv (tcF0 ν R χy) (ϱ y) * ϱ y + tcF0 ν R χy (ϱ y) * 1)| * 1 *
            ptNorm (W 0) 1 (ϱ y) (y 2) +
          2 * |-ν * (tcF0 ν R χy (ϱ y) * ϱ y)| * 1 * ptNorm (W 0) 2 (ϱ y) (y 2) := h1
      _ ≤ (3 * M) * 1 * ptNorm (W 0) 1 (ϱ y) (y 2) +
          2 * (2 * M * s) * 1 * ptNorm (W 0) 2 (ϱ y) (y 2) := by gcongr
      _ = _ := by ring
  have bg4_val : |ν * tcF0 ν R χy (ϱ y)| ≤ M := by
    rw [abs_mul, abs_of_pos hν]
    calc ν * |tcF0 ν R χy (ϱ y)| ≤ ν * (M * s ^ 2) := by gcongr
      _ = M * (ν * s ^ 2) := by ring
      _ ≤ M * 1 := by gcongr
      _ = M := mul_one _
  have bg4_val_y : |ν * tcF0 ν R χy (ϱ y)| * ϱ y ≤ 2 * M * s := by
    rw [abs_mul, abs_of_pos hν]
    calc ν * |tcF0 ν R χy (ϱ y)| * ϱ y ≤ 1 * (M * s ^ 2) * ϱ y := by gcongr
      _ = M * s * (s * ϱ y) := by ring
      _ ≤ M * s * 2 := by gcongr
      _ = 2 * M * s := by ring
  have bg4_der : |ν * deriv (tcF0 ν R χy) (ϱ y)| ≤ M * s := by
    rw [abs_mul, abs_of_pos hν]
    calc ν * |deriv (tcF0 ν R χy) (ϱ y)| ≤ ν * (M * s ^ 3) := by gcongr
      _ = M * s * (ν * s ^ 2) := by ring
      _ ≤ M * s * 1 := by gcongr
      _ = M * s := mul_one _
  have t4 : ‖L4‖ ≤ M * s * rayInt (W 0) 2 (ϱ y) (y 2) +
      2 * M * s * ptNorm (W 0) 2 (ϱ y) (y 2) +
      M * rayInt (W 0) 3 (ϱ y) (y 2) := by
    have h1 := hL4b
    have hneg1 : |-ν * deriv (tcF0 ν R χy) (ϱ y)| = |ν * deriv (tcF0 ν R χy) (ϱ y)| := by
      rw [neg_mul, abs_neg]
    have hneg2 : |-ν * tcF0 ν R χy (ϱ y)| = |ν * tcF0 ν R χy (ϱ y)| := by
      rw [neg_mul, abs_neg]
    rw [hneg1, hneg2, mul_one, mul_one] at h1
    have h2 : |ν * tcF0 ν R χy (ϱ y)| *
        (ϱ y * ptNorm (W 0) 2 (ϱ y) (y 2) + rayInt (W 0) 3 (ϱ y) (y 2)) =
        (|ν * tcF0 ν R χy (ϱ y)| * ϱ y) * ptNorm (W 0) 2 (ϱ y) (y 2) +
          |ν * tcF0 ν R χy (ϱ y)| * rayInt (W 0) 3 (ϱ y) (y 2) := by ring
    rw [h2] at h1
    have hI2 := hI_nn 2
    have hP2 := hP_nn 2
    have hI3 := hI_nn 3
    calc ‖L4‖
        ≤ |ν * deriv (tcF0 ν R χy) (ϱ y)| * rayInt (W 0) 2 (ϱ y) (y 2) +
          ((|ν * tcF0 ν R χy (ϱ y)| * ϱ y) * ptNorm (W 0) 2 (ϱ y) (y 2) +
            |ν * tcF0 ν R χy (ϱ y)| * rayInt (W 0) 3 (ϱ y) (y 2)) := h1
      _ ≤ (M * s) * rayInt (W 0) 2 (ϱ y) (y 2) +
          ((2 * M * s) * ptNorm (W 0) 2 (ϱ y) (y 2) +
            M * rayInt (W 0) 3 (ϱ y) (y 2)) := by gcongr
      _ = _ := by ring
  have t5 : ‖L5‖ ≤ 3 * M * s * rayInt (W 0) 2 (ϱ y) (y 2) +
      6 * M * s * ptNorm (W 0) 2 (ϱ y) (y 2) +
      3 * M * rayInt (W 0) 3 (ϱ y) (y 2) := by
    have h1 := hL5b
    have h2 : |ν * tcF0 ν R χy (ϱ y)| * 3 *
        (ϱ y * ptNorm (W 0) 2 (ϱ y) (y 2) + rayInt (W 0) 3 (ϱ y) (y 2)) =
        3 * ((|ν * tcF0 ν R χy (ϱ y)| * ϱ y) * ptNorm (W 0) 2 (ϱ y) (y 2)) +
          3 * (|ν * tcF0 ν R χy (ϱ y)| * rayInt (W 0) 3 (ϱ y) (y 2)) := by ring
    rw [h2] at h1
    have hI2 := hI_nn 2
    have hP2 := hP_nn 2
    have hI3 := hI_nn 3
    calc ‖L5‖
        ≤ |ν * deriv (tcF0 ν R χy) (ϱ y)| * 3 * rayInt (W 0) 2 (ϱ y) (y 2) +
          (3 * ((|ν * tcF0 ν R χy (ϱ y)| * ϱ y) * ptNorm (W 0) 2 (ϱ y) (y 2)) +
            3 * (|ν * tcF0 ν R χy (ϱ y)| * rayInt (W 0) 3 (ϱ y) (y 2))) := h1
      _ ≤ (M * s) * 3 * rayInt (W 0) 2 (ϱ y) (y 2) +
          (3 * ((2 * M * s) * ptNorm (W 0) 2 (ϱ y) (y 2)) +
            3 * (M * rayInt (W 0) 3 (ϱ y) (y 2))) := by gcongr
      _ = _ := by ring
  have hsum : ‖(((L1 + L2) + L3) + L4) + L5‖ ≤ ‖L1‖ + ‖L2‖ + ‖L3‖ + ‖L4‖ + ‖L5‖ := by
    have a1 := norm_add_le (((L1 + L2) + L3) + L4) L5
    have a2 := norm_add_le ((L1 + L2) + L3) L4
    have a3 := norm_add_le (L1 + L2) L3
    have a4 := norm_add_le L1 L2
    linarith
  have hP0 := mul_nonneg hs0.le (hP_nn 0)
  have hP1 := hP_nn 1
  have hP2 := mul_nonneg hs0.le (hP_nn 2)
  have hI0 := mul_nonneg (pow_pos hs0 3).le (hI_nn 0)
  have hI1 := mul_nonneg (pow_pos hs0 2).le (hI_nn 1)
  have hI2 := mul_nonneg hs0.le (hI_nn 2)
  have hI3 := hI_nn 3
  linarith [hsum, t1, t2, t3, t4, t5,
    mul_nonneg hC0 hP0, mul_nonneg hC1 hP0, mul_nonneg hM0 hP0,
    mul_nonneg hC0 hP1, mul_nonneg hC1 hP1, mul_nonneg hM0 hP1,
    mul_nonneg hC0 hP2, mul_nonneg hC1 hP2, mul_nonneg hM0 hP2,
    mul_nonneg hC0 hI0, mul_nonneg hC1 hI0, mul_nonneg hM0 hI0,
    mul_nonneg hC0 hI1, mul_nonneg hC1 hI1, mul_nonneg hM0 hI1,
    mul_nonneg hC0 hI2, mul_nonneg hC1 hI2, mul_nonneg hM0 hI2,
    mul_nonneg hC0 hI3, mul_nonneg hC1 hI3, mul_nonneg hM0 hI3]

/-- Pointwise bound on `‖fderiv ℝ (commPsi Z₁ τ) y - fderiv ℝ (commPsi Z₂ τ) y‖` on the transition
annulus in terms of `ptNorm` and `rayInt` of `Z₁ τ - Z₂ τ`. -/
theorem fderiv_commPsi_sub_le {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν μ ε c ρo : ℝ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ),
      0 < ν → ν ≤ 1 → -(1 / 4) < μ → 0 < ε → ε ≤ 1 →
      0 < c → 0 ≤ ρo → ρo ≤ Real.sqrt (5 * ν / 6) →
      ThinHyp c ρo F → IIIa.thinMoment c F ≠ ⊤ →
      ∀ (xo : Space), ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
      ∀ (τ : ℝ),
        let Z₁ := srcX0 ν μ (IIIa.thinSource ε F)
        let Z₂ := srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F)))
        let ΔZ : Space → Space := fun w => Z₁ τ w - Z₂ τ w
        let y : Space := ε⁻¹ • xo
        let s : ℝ := (ε⁻¹ * Real.sqrt ν)⁻¹
        ‖fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y‖ ≤
          C * (
            s * ptNorm ΔZ 0 (ϱ y) (y 2) +
            ptNorm ΔZ 1 (ϱ y) (y 2) +
            s * ptNorm ΔZ 2 (ϱ y) (y 2) +
            s ^ 3 * rayInt ΔZ 0 (ϱ y) (y 2) +
            s ^ 2 * rayInt ΔZ 1 (ϱ y) (y 2) +
            s * rayInt ΔZ 2 (ϱ y) (y 2) +
            rayInt ΔZ 3 (ϱ y) (y 2)) := by
  obtain ⟨C, hC0, hraw⟩ := fderiv_phiScalar_raw_bound hχ
  refine ⟨C, hC0, ?_⟩
  intro ν μ ε c ρo F hν hν1 hμ hε0 hε1 hc hρo0 hρo hth hN xo hxo1 hxo2 τ
  dsimp only
  set Z₁ := srcX0 ν μ (IIIa.thinSource ε F)
  set Z₂ := srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F)))
  set ΔZ : Space → Space := fun w => Z₁ τ w - Z₂ τ w
  set y : Space := ε⁻¹ • xo
  -- ThinHyp and finite thinMoment for meanLift (phaseMean c F)
  have hFm := hth.meas
  have hFs := hth.supp
  obtain ⟨hm1, _⟩ := IIIa.sepMomentSplit c hc F hFm
  have hN1 : IIIa.thinMoment c (IIIa.meanLift (IIIa.phaseMean c F)) ≠ ⊤ :=
    ne_top_of_le_ne_top hN hm1
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.phaseMean c F w.1 w.2 i j :=
    IIIa.phaseMean_measurable c F hFm
  have hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → IIIa.phaseMean c F x' Y = 0 := by
    intro x' Y h
    funext i j
    simp [IIIa.phaseMean, hFs x' Y _ h]
  have hth1 : ThinHyp c ρo (IIIa.meanLift (IIIa.phaseMean c F)) :=
    ⟨fun i j => (hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop),
     fun _ _ _ => rfl,
     fun x' Y _ h => hGs x' Y h⟩
  -- Geometry of y = ε⁻¹ • xo on streamAnn ν ε⁻¹
  have hR1 : 1 ≤ ε⁻¹ := one_le_inv₀ hε0 |>.2 hε1
  have hϱy : ϱ y = ε⁻¹ * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := by
    unfold ϱ y
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [show (ε⁻¹ * xo 0) ^ 2 + (ε⁻¹ * xo 1) ^ 2 = (ε⁻¹) ^ 2 * (xo 0 ^ 2 + xo 1 ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hε0.le)]
  have hyann : y ∈ streamAnn ν ε⁻¹ := by
    refine ⟨?_, ?_⟩ <;> rw [hϱy]
    · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxo1) (inv_nonneg.2 hε0.le)
    · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxo2) (inv_nonneg.2 hε0.le)
  set r₁ : ℝ := (23 / 24 : ℝ) * (ε⁻¹ * Real.sqrt ν)
  have hr₁ : 0 < r₁ := by dsimp [r₁]; positivity
  have hy_r1 : r₁ < ϱ y := by
    have : ε⁻¹ * Real.sqrt ν ≤ ϱ y := hyann.1
    have : 0 < ε⁻¹ * Real.sqrt ν := by positivity
    dsimp [r₁]; linarith
  have hy_out : ρo / ε < ϱ y :=
    ((rOut_le_22_23_r1 hν hε0 hρo).trans (mul_le_mul_of_nonneg_left hy_r1.le (by norm_num))).trans_lt
      (by linarith [lt_trans hr₁ hy_r1])
  -- ValidPsiFieldWith for Z₁ τ, Z₂ τ, and ΔZ
  obtain ⟨B₁, hZ₁v⟩ := thin_validPsiFieldWith hν hμ hε0 hc hρo0 hρo hth hN τ
  obtain ⟨B₂, hZ₂v⟩ := thin_validPsiFieldWith hν hμ hε0 hc hρo0 hρo hth1 hN1 τ
  have hΔZv : ValidPsiFieldWith r₁ (B₁ + B₂) (fun _ => ΔZ) := hZ₁v.sub hZ₂v
  -- Neighborhood equality commPsi Z₁ - commPsi Z₂ = phiScalar ΔZ • e₂
  have hopen : IsOpen {y' : Space | r₁ < ϱ y'} := isOpen_lt continuous_const continuous_ϱ
  have hev : (fun y' => commPsi ν μ ε⁻¹ χy Z₁ τ y' - commPsi ν μ ε⁻¹ χy Z₂ τ y') =ᶠ[𝓝 y]
      fun y' => phiScalar ν ε⁻¹ χy (fun _ => ΔZ) y' • (UnforcedLeray.coordinateVector 2 : Space) := by
    filter_upwards [hopen.mem_nhds hy_r1] with y' hy'
    rw [thin_commPsi_eq_phiScalar hχ hν hμ hε0 hc hρo0 hρo hth hN τ hy',
      thin_commPsi_eq_phiScalar hχ hν hμ hε0 hc hρo0 hρo hth1 hN1 τ hy',
      ← sub_smul, phiScalar_sub ν ε⁻¹ χy hZ₁v hZ₂v hr₁ hy']
  have hd1 := thin_commPsi_diffAt (R := ε⁻¹) hχ hν hμ hε0 hc hρo0 hth hN τ hy_out
  have hd2 := thin_commPsi_diffAt (R := ε⁻¹) hχ hν hμ hε0 hc hρo0 hth1 hN1 τ hy_out
  obtain ⟨hd_phi, hb_phi⟩ := hraw ν ε⁻¹ (B₁ + B₂) (fun _ => ΔZ) hν hν1 hR1 hΔZv y hyann
  have hfderiv_eq : fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y -
      fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y =
      (fderiv ℝ (phiScalar ν ε⁻¹ χy (fun _ => ΔZ)) y).smulRight
        (UnforcedLeray.coordinateVector 2 : Space) := by
    rw [← fderiv_sub hd1 hd2]
    change fderiv ℝ (fun y' => commPsi ν μ ε⁻¹ χy Z₁ τ y' - commPsi ν μ ε⁻¹ χy Z₂ τ y') y = _
    rw [hev.fderiv_eq, (hd_phi.hasFDerivAt.smul_const
      (UnforcedLeray.coordinateVector 2 : Space)).fderiv]
  have hnorm_le : ‖fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y -
      fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y‖ ≤
      ‖fderiv ℝ (phiScalar ν ε⁻¹ χy (fun _ => ΔZ)) y‖ := by
    rw [hfderiv_eq]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    simp only [ContinuousLinearMap.smulRight_apply, norm_smul, norm_e 2, mul_one,
      Real.norm_eq_abs]
    exact (fderiv ℝ (phiScalar ν ε⁻¹ χy (fun _ => ΔZ)) y).le_opNorm v
  exact hnorm_le.trans hb_phi

end SepPsiOscFarAux

end UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

end
