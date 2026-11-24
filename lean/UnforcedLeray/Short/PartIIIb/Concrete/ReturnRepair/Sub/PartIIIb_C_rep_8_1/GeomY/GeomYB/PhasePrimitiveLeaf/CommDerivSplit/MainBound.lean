import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.MainLeibniz.CoeffDeriv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Leibniz

/-!
# Pointwise commutator decomposition and `commMain` derivative bound (`CommDerivSplit/MainBound`)

Proves:
1. `comm_eq_commMain_add_commPsi_of_reg`: at any off-axis point `y` where `Z τ` and `psiFld Z τ`
   are `C²` in space and differentiable in time, `comm ν μ R χy Z τ y = commMain ν R χy Z τ y +
   commPsi ν μ R χy Z τ y`.
2. `fderiv_commMain_sub_le`: transition-annulus derivative difference bound for `commMain` keeping
   `‖fderiv ℝ (fderiv ℝ (Z₁ τ)) y - fderiv ℝ (fderiv ℝ (Z₂ τ)) y‖`.
3. `fderiv_comm_sub_enorm_le_of_reg`: combines the local `comm = commMain + commPsi` identity with
   the `commMain` derivative bound and triangle inequality in `ℝ≥0∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

open YBComm

/-- At any off-axis point `y` where `Z τ` and `psiFld Z τ` are `C²` in space and differentiable
in time at `τ`, the commutator splits into `commMain + commPsi`. -/
theorem comm_eq_commMain_add_commPsi_of_reg {ν μ R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (hρ : 0 < ϱ y)
    (hZc : ContDiffAt ℝ 2 (Z τ) y)
    (hZt : DifferentiableAt ℝ (fun t => Z t y) τ)
    (hψc : ContDiffAt ℝ 2 (psiFld Z τ) y)
    (hψt : DifferentiableAt ℝ (fun t => psiFld Z t y) τ) :
    comm ν μ R χy Z τ y = commMain ν R χy Z τ y + commPsi ν μ R χy Z τ y := by
  have hya : y ∉ axis := tcle_notaxis hρ
  have hcc : ContDiffAt ℝ 2 (tcC0 ν R χy) (ϱ y) := tcle_c0_smooth hχ ν R hρ.ne'
  have hff : ContDiffAt ℝ 2 (tcF0 ν R χy) (ϱ y) := tcle_f0_smooth hχ ν R hρ.ne'
  have hϱc : ContDiffAt ℝ 2 ϱ y := contDiffOn_ϱ.contDiffAt (isOpen_compl_axis.mem_nhds hya)
  have hC : ContDiffAt ℝ 2 (fun y' => tcC0 ν R χy (ϱ y')) y := hcc.comp y hϱc
  have hF : ContDiffAt ℝ 2 (fun y' => tcF0 ν R χy (ϱ y')) y := hff.comp y hϱc
  have hZd : DifferentiableAt ℝ (Z τ) y := hZc.differentiableAt (by norm_num)
  have hψd : DifferentiableAt ℝ (psiFld Z τ) y := hψc.differentiableAt (by norm_num)
  have hCd : DifferentiableAt ℝ (fun y' => tcC0 ν R χy (ϱ y')) y := hC.differentiableAt (by norm_num)
  have hFd : DifferentiableAt ℝ (fun y' => tcF0 ν R χy (ϱ y')) y := hF.differentiableAt (by norm_num)
  have hccd : DifferentiableAt ℝ (tcC0 ν R χy) (ϱ y) := hcc.differentiableAt (by norm_num)
  have hffd : DifferentiableAt ℝ (tcF0 ν R χy) (ϱ y) := hff.differentiableAt (by norm_num)
  have hWf : wardStreamCut ν R χy Z τ = fun y' =>
      tcC0 ν R χy (ϱ y') • Z τ y' + tcF0 ν R χy (ϱ y') • psiFld Z τ y' :=
    funext fun y' => tcle_wsc_eq ν R χy Z τ y'
  have ht : deriv (fun t => wardStreamCut ν R χy Z t y) τ =
      tcC0 ν R χy (ϱ y) • deriv (fun t => Z t y) τ +
        tcF0 ν R χy (ϱ y) • deriv (fun t => psiFld Z t y) τ := by
    have : (fun t => wardStreamCut ν R χy Z t y) = fun t =>
        tcC0 ν R χy (ϱ y) • Z t y + tcF0 ν R χy (ϱ y) • psiFld Z t y :=
      funext fun t => tcle_wsc_eq ν R χy Z t y
    rw [this]
    exact ((hZt.hasDerivAt.const_smul (tcC0 ν R χy (ϱ y))).add
      (hψt.hasDerivAt.const_smul (tcF0 ν R χy (ϱ y)))).deriv
  have ht_psi : deriv (fun t => cutPsi ν R χy Z t y) τ =
      tcF0 ν R χy (ϱ y) • deriv (fun t => psiFld Z t y) τ := by
    change deriv (fun t => tcF0 ν R χy (ϱ y) • psiFld Z t y) τ = _
    exact (hψt.hasDerivAt.const_smul (tcF0 ν R χy (ϱ y))).deriv
  have hD : fderiv ℝ (wardStreamCut ν R χy Z τ) y y =
      tcC0 ν R χy (ϱ y) • fderiv ℝ (Z τ) y y +
        (ϱ y * deriv (tcC0 ν R χy) (ϱ y)) • Z τ y +
        (tcF0 ν R χy (ϱ y) • fderiv ℝ (psiFld Z τ) y y +
          (ϱ y * deriv (tcF0 ν R χy) (ϱ y)) • psiFld Z τ y) := by
    rw [hWf]
    have h1 : HasFDerivAt (fun y' => tcC0 ν R χy (ϱ y') • Z τ y') _ y :=
      hCd.hasFDerivAt.smul hZd.hasFDerivAt
    have h2 : HasFDerivAt (fun y' => tcF0 ν R χy (ϱ y') • psiFld Z τ y') _ y :=
      hFd.hasFDerivAt.smul hψd.hasFDerivAt
    rw [(h1.fun_add h2).fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [tcle_dy_comp hρ hccd, tcle_dy_comp hρ hffd]
  have hD_psi : fderiv ℝ (cutPsi ν R χy Z τ) y y =
      tcF0 ν R χy (ϱ y) • fderiv ℝ (psiFld Z τ) y y +
        (ϱ y * deriv (tcF0 ν R χy) (ϱ y)) • psiFld Z τ y := by
    change fderiv ℝ (fun y' => tcF0 ν R χy (ϱ y') • psiFld Z τ y') y y = _
    have h2 : HasFDerivAt (fun y' => tcF0 ν R χy (ϱ y') • psiFld Z τ y') _ y :=
      hFd.hasFDerivAt.smul hψd.hasFDerivAt
    rw [h2.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [tcle_dy_comp hρ hffd]
  have hLap : physLap (wardStreamCut ν R χy Z τ) y =
      (deriv (deriv (tcC0 ν R χy)) (ϱ y) + deriv (tcC0 ν R χy) (ϱ y) / ϱ y) • Z τ y +
        ((2 : ℝ) • (deriv (tcC0 ν R χy) (ϱ y) • fderiv ℝ (Z τ) y (radialUnit y)) +
          tcC0 ν R χy (ϱ y) • physLap (Z τ) y) +
      ((deriv (deriv (tcF0 ν R χy)) (ϱ y) + deriv (tcF0 ν R χy) (ϱ y) / ϱ y) • psiFld Z τ y +
        ((2 : ℝ) • (deriv (tcF0 ν R χy) (ϱ y) • fderiv ℝ (psiFld Z τ) y (radialUnit y)) +
          tcF0 ν R χy (ϱ y) • physLap (psiFld Z τ) y)) := by
    have hCZ : ContDiffAt ℝ 2 (fun y' => tcC0 ν R χy (ϱ y') • Z τ y') y := hC.smul hZc
    have hFψ : ContDiffAt ℝ 2 (fun y' => tcF0 ν R χy (ϱ y') • psiFld Z τ y') y := hF.smul hψc
    rw [hWf, tcle_physLap_add hCZ hFψ, tcle_lap_smul hC hZc,
      tcle_lap_smul hF hψc, tcle_lapS_comp hρ hcc, tcle_lapS_comp hρ hff,
      tcle_grad_sum _ hρ hccd (fderiv ℝ (Z τ) y), tcle_grad_sum _ hρ hffd (fderiv ℝ (psiFld Z τ) y)]
    abel
  have hLap_psi : physLap (cutPsi ν R χy Z τ) y =
      (deriv (deriv (tcF0 ν R χy)) (ϱ y) + deriv (tcF0 ν R χy) (ϱ y) / ϱ y) • psiFld Z τ y +
        ((2 : ℝ) • (deriv (tcF0 ν R χy) (ϱ y) • fderiv ℝ (psiFld Z τ) y (radialUnit y)) +
          tcF0 ν R χy (ϱ y) • physLap (psiFld Z τ) y) := by
    change physLap (fun y' => tcF0 ν R χy (ϱ y') • psiFld Z τ y') y = _
    rw [tcle_lap_smul hF hψc, tcle_lapS_comp hρ hff,
      tcle_grad_sum _ hρ hffd (fderiv ℝ (psiFld Z τ) y)]
    abel
  have hrhs : wardStreamCut ν R χy (physDmu ν (μ + 1) Z) τ y =
      tcC0 ν R χy (ϱ y) • physDmu ν (μ + 1) Z τ y +
        cutPsi ν R χy (physDmu ν (μ + 1) Z) τ y := by
    rw [wardStreamCut_eq_cutMain_add_cutPsi]; rfl
  have hW0 : wardStreamCut ν R χy Z τ y = tcC0 ν R χy (ϱ y) • Z τ y +
      tcF0 ν R χy (ϱ y) • psiFld Z τ y := tcle_wsc_eq ν R χy Z τ y
  have hDW : physDmu ν (μ + 1) (wardStreamCut ν R χy Z) τ y =
      deriv (fun t => wardStreamCut ν R χy Z t y) τ -
        (1 / 2 : ℝ) • fderiv ℝ (wardStreamCut ν R χy Z τ) y y -
          ν • physLap (wardStreamCut ν R χy Z τ) y +
            (μ + 1 - 1 / 2) • wardStreamCut ν R χy Z τ y := rfl
  have hDpsi : physDmu ν (μ + 1) (cutPsi ν R χy Z) τ y =
      deriv (fun t => cutPsi ν R χy Z t y) τ -
        (1 / 2 : ℝ) • fderiv ℝ (cutPsi ν R χy Z τ) y y -
          ν • physLap (cutPsi ν R χy Z τ) y +
            (μ + 1 - 1 / 2) • cutPsi ν R χy Z τ y := rfl
  have hDZ : physDmu ν (μ + 1) Z τ y =
      deriv (fun t => Z t y) τ - (1 / 2 : ℝ) • fderiv ℝ (Z τ) y y -
        ν • physLap (Z τ) y + (μ + 1 - 1 / 2) • Z τ y := rfl
  change physDmu ν (μ + 1) (wardStreamCut ν R χy Z) τ y -
      wardStreamCut ν R χy (physDmu ν (μ + 1) Z) τ y =
    commMain ν R χy Z τ y +
      (physDmu ν (μ + 1) (cutPsi ν R χy Z) τ y - cutPsi ν R χy (physDmu ν (μ + 1) Z) τ y)
  rw [hDW, hrhs, hDpsi, ht, hD, hLap, hW0, hDZ, ht_psi, hD_psi, hLap_psi]
  unfold commMain cutPsi tcA1 tcA2
  module

/-- Transition-annulus derivative difference bound for `commMain`, expressed with
`fderiv ℝ (fderiv ℝ (Zᵢ τ)) y`. -/
theorem fderiv_commMain_sub_le {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ ν ε : ℝ, 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 →
        ∀ (Z₁ Z₂ : ℝ → Space → Space) (τ : ℝ) (xo : Space),
          ν ≤ xo 0 ^ 2 + xo 1 ^ 2 → xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4 →
          ContDiffAt ℝ 2 (Z₁ τ) (ε⁻¹ • xo) →
          ContDiffAt ℝ 2 (Z₂ τ) (ε⁻¹ • xo) →
          let y := ε⁻¹ • xo
          let r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
          DifferentiableAt ℝ (commMain ν ε⁻¹ χy Z₁ τ) y ∧
          DifferentiableAt ℝ (commMain ν ε⁻¹ χy Z₂ τ) y ∧
          ‖fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y‖ ≤
            C₀ * (ε * r⁻¹ * ‖Z₁ τ y - Z₂ τ y‖ +
              ‖fderiv ℝ (Z₁ τ) y - fderiv ℝ (Z₂ τ) y‖ +
              ν * ε * r⁻¹ *
                ‖fderiv ℝ (fderiv ℝ (Z₁ τ)) y - fderiv ℝ (fderiv ℝ (Z₂ τ)) y‖) := by
  obtain ⟨C, hC0, hC⟩ := YBWidth.coeff_annulus_bounds hχ
  obtain ⟨C₀, hC₀0, hsub⟩ := YBWidth.fderiv_commMain_sub_le hχ
  refine ⟨C₀, hC₀0, ?_⟩
  intro ν ε hν hν1 hε hε1 Z₁ Z₂ τ xo hxo1 hxo2 hZ₁ hZ₂ y r
  have hr_pos : 0 < r := Real.sqrt_pos.2 (lt_of_lt_of_le hν hxo1)
  have hr1 : Real.sqrt ν ≤ r := Real.sqrt_le_sqrt hxo1
  have hr2 : r ≤ Real.sqrt (5 * ν / 4) := Real.sqrt_le_sqrt hxo2
  have hR1 : 1 ≤ ε⁻¹ := one_le_inv_iff₀.2 ⟨hε, hε1⟩
  have hR_pos : 0 < ε⁻¹ := inv_pos.2 hε
  have hy_rho : ϱ y = ε⁻¹ * r := by
    change ϱ (ε⁻¹ • xo) = ε⁻¹ * r
    rw [ϱ_smul, abs_of_pos hR_pos]
    rfl
  have hs1 : ε⁻¹ * Real.sqrt ν ≤ ϱ y := by rw [hy_rho]; gcongr
  have hs2 : ϱ y ≤ ε⁻¹ * Real.sqrt (5 * ν / 4) := by rw [hy_rho]; gcongr
  have hy_pos : 0 < ϱ y := by rw [hy_rho]; positivity
  obtain ⟨a1, a2, hA1, hA2, -⟩ := hC ν ε⁻¹ hν hν1 hR1 (ϱ y) hs1 hs2
  obtain ⟨hZ1_diff, -⟩ := YBWidth.fderiv_commMain_bound hχ Z₁ τ hy_pos hZ₁ hA1 hA2
  obtain ⟨hZ2_diff, -⟩ := YBWidth.fderiv_commMain_bound hχ Z₂ τ hy_pos hZ₂ hA1 hA2
  have hbnd := hsub ν ε hν hν1 hε hε1 Z₁ Z₂ τ xo hxo1 hxo2 hZ₁ hZ₂
  have hiter : ‖iteratedFDeriv ℝ 2 (Z₁ τ) y - iteratedFDeriv ℝ 2 (Z₂ τ) y‖ =
      ‖fderiv ℝ (fderiv ℝ (Z₁ τ)) y - fderiv ℝ (fderiv ℝ (Z₂ τ)) y‖ := by
    set W : Space → Space := fun y' => Z₁ τ y' - Z₂ τ y'
    have hW2 : iteratedFDeriv ℝ 2 W y =
        iteratedFDeriv ℝ 2 (Z₁ τ) y - iteratedFDeriv ℝ 2 (Z₂ τ) y :=
      iteratedFDeriv_sub_apply hZ₁ hZ₂
    have hWd : fderiv ℝ W =ᶠ[𝓝 y] fun y' => fderiv ℝ (Z₁ τ) y' - fderiv ℝ (Z₂ τ) y' := by
      filter_upwards [hZ₁.eventually (by simp), hZ₂.eventually (by simp)] with y' h1 h2
      exact fderiv_sub (h1.differentiableAt (by norm_num)) (h2.differentiableAt (by norm_num))
    have hZ1d : DifferentiableAt ℝ (fderiv ℝ (Z₁ τ)) y :=
      (hZ₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hZ2d : DifferentiableAt ℝ (fderiv ℝ (Z₂ τ)) y :=
      (hZ₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hWdd : fderiv ℝ (fderiv ℝ W) y =
        fderiv ℝ (fderiv ℝ (Z₁ τ)) y - fderiv ℝ (fderiv ℝ (Z₂ τ)) y := by
      rw [hWd.fderiv_eq]
      exact fderiv_sub hZ1d hZ2d
    rw [← hW2, ← hWdd, ← norm_iteratedFDeriv_one, ← norm_iteratedFDeriv_fderiv]
  refine ⟨hZ1_diff, hZ2_diff, ?_⟩
  change ‖fderiv ℝ (YBWidth.commMain ν ε⁻¹ χy Z₁ τ) y -
      fderiv ℝ (YBWidth.commMain ν ε⁻¹ χy Z₂ τ) y‖ ≤ _
  refine hbnd.trans (le_of_eq ?_)
  unfold YBWidth.commMainMaj
  rw [hiter]

/-- Enorm triangle inequality combining the local `comm = commMain + commPsi` identity with
`fderiv_commMain_sub_le`. -/
theorem fderiv_comm_sub_enorm_le_of_reg {ν μ ε : ℝ} {χy : ℝ → ℝ}
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hν : 0 < ν) (hε : 0 < ε)
    {Z₁ Z₂ : ℝ → Space → Space} {τ : ℝ} {xo : Space}
    (hxo1 : ν ≤ xo 0 ^ 2 + xo 1 ^ 2)
    (hM1 : DifferentiableAt ℝ (commMain ν ε⁻¹ χy Z₁ τ) (ε⁻¹ • xo))
    (hM2 : DifferentiableAt ℝ (commMain ν ε⁻¹ χy Z₂ τ) (ε⁻¹ • xo))
    (hP1 : DifferentiableAt ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) (ε⁻¹ • xo))
    (hP2 : DifferentiableAt ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) (ε⁻¹ • xo))
    (heq1 : comm ν μ ε⁻¹ χy Z₁ τ =ᶠ[𝓝 (ε⁻¹ • xo)]
      fun y' => commMain ν ε⁻¹ χy Z₁ τ y' + commPsi ν μ ε⁻¹ χy Z₁ τ y')
    (heq2 : comm ν μ ε⁻¹ χy Z₂ τ =ᶠ[𝓝 (ε⁻¹ • xo)]
      fun y' => commMain ν ε⁻¹ χy Z₂ τ y' + commPsi ν μ ε⁻¹ χy Z₂ τ y')
    (hMain :
      let y := ε⁻¹ • xo
      let r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
      ‖fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y‖ ≤
        C₀ * (ε * r⁻¹ * ‖Z₁ τ y - Z₂ τ y‖ +
          ‖fderiv ℝ (Z₁ τ) y - fderiv ℝ (Z₂ τ) y‖ +
          ν * ε * r⁻¹ *
            ‖fderiv ℝ (fderiv ℝ (Z₁ τ)) y - fderiv ℝ (fderiv ℝ (Z₂ τ)) y‖)) :
    let y := ε⁻¹ • xo
    let r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
    ‖fderiv ℝ (comm ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (comm ν μ ε⁻¹ χy Z₂ τ) y‖ₑ ≤
      ENNReal.ofReal (max C₀ 1) *
        (ENNReal.ofReal (ε * r⁻¹) * ‖Z₁ τ y - Z₂ τ y‖ₑ +
          ‖fderiv ℝ (Z₁ τ) y - fderiv ℝ (Z₂ τ) y‖ₑ +
          ENNReal.ofReal (ν * ε * r⁻¹) *
            ‖fderiv ℝ (fderiv ℝ (Z₁ τ)) y - fderiv ℝ (fderiv ℝ (Z₂ τ)) y‖ₑ +
          ‖fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y -
            fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y‖ₑ) := by
  intro y r
  have hr_pos : 0 < r := Real.sqrt_pos.2 (lt_of_lt_of_le hν hxo1)
  have hf1 : fderiv ℝ (comm ν μ ε⁻¹ χy Z₁ τ) y =
      fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y + fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y := by
    rw [heq1.fderiv_eq]
    exact fderiv_add hM1 hP1
  have hf2 : fderiv ℝ (comm ν μ ε⁻¹ χy Z₂ τ) y =
      fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y + fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y := by
    rw [heq2.fderiv_eq]
    exact fderiv_add hM2 hP2
  have hsub_eq :
      fderiv ℝ (comm ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (comm ν μ ε⁻¹ χy Z₂ τ) y =
        (fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y) +
          (fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y) := by
    rw [hf1, hf2]; abel
  rw [hsub_eq]
  set C₁ : ℝ := max C₀ 1
  have hC₁0 : 0 ≤ C₁ := le_trans hC₀ (le_max_left C₀ 1)
  have hC₀_le : C₀ ≤ C₁ := le_max_left C₀ 1
  have h1_le : 1 ≤ C₁ := le_max_right C₀ 1
  set N0 := ‖Z₁ τ y - Z₂ τ y‖
  set N1 := ‖fderiv ℝ (Z₁ τ) y - fderiv ℝ (Z₂ τ) y‖
  set N2 := ‖fderiv ℝ (fderiv ℝ (Z₁ τ)) y - fderiv ℝ (fderiv ℝ (Z₂ τ)) y‖
  set NP := ‖fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y‖
  have hN_nonneg : 0 ≤ ε * r⁻¹ * N0 + N1 + ν * ε * r⁻¹ * N2 := by positivity
  have hreal :
      ‖(fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y) +
          (fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y)‖ ≤
        C₁ * (ε * r⁻¹ * N0 + N1 + ν * ε * r⁻¹ * N2 + NP) := by
    calc ‖(fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y) +
            (fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y)‖
        ≤ ‖fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y‖ + NP :=
          norm_add_le _ _
      _ ≤ C₀ * (ε * r⁻¹ * N0 + N1 + ν * ε * r⁻¹ * N2) + 1 * NP := by
          linarith [hMain]
      _ ≤ C₁ * (ε * r⁻¹ * N0 + N1 + ν * ε * r⁻¹ * N2) + C₁ * NP :=
          add_le_add (mul_le_mul_of_nonneg_right hC₀_le hN_nonneg)
            (mul_le_mul_of_nonneg_right h1_le (norm_nonneg _))
      _ = C₁ * (ε * r⁻¹ * N0 + N1 + ν * ε * r⁻¹ * N2 + NP) := by ring
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
  have hw1 : 0 ≤ ε * r⁻¹ := by positivity
  have hw2 : 0 ≤ ν * ε * r⁻¹ := by positivity
  have hN1 : 0 ≤ N1 := norm_nonneg _
  have hNP : 0 ≤ NP := norm_nonneg _
  rw [ENNReal.ofReal_mul hC₁0,
    ENNReal.ofReal_add (by positivity) hNP,
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) hN1,
    ENNReal.ofReal_mul hw1, ENNReal.ofReal_mul hw2]
  simp only [← ofReal_norm, N0, N1, N2, NP]

end UnforcedLeray.Short.PartIIIb.Concrete.YBPhase
