import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.MainLeibniz.CoeffDeriv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Leibniz
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B4a
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B4b
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.ZPrimRegular.Kernel

/-!
# Pointwise Leibniz splitting `comm = commMain + commPsi` for phase-free fields

Helper for `PartIII-b:C/rep/8/1/1/2/5/2/1/1` (`YBWidth.sepCommMainLeibniz`).
Source `the November 2 reference manuscript`
lines 3700-3712, 4195-4215, 5427-5432.

For any phase-independent field `Z = fun _ => W` whose spatial profile `W : Space → Space` is
`C^∞` on `{y' | r₀ < ϱ y'}` (`r₀ > 0`) with all derivatives decaying as `O(ϱ^{-4})` for
`ϱ ≥ 2 r₀ + 2`:
1. `commMain_eq_of_timeIndep`: `[D_{μ+1}, cutMain] Z = commMain Z` at every off-axis `C²` point;
2. `comm_eq_commMain_add_commPsi`: `comm Z = commMain Z + commPsi Z` on `{y' | r₀ < ϱ y'}`;
3. `psiFld_contDiffOn_of_decay`: `psiFld Z τ` is `C^∞` on `{y' | r₀ < ϱ y'}`;
4. `differentiableAt_psiFld_physDmu_of_decay`: `psiFld (physDmu ν (μ + 1) Z) τ` is differentiable
   at every `y` with `r₀ < ϱ y`;
5. `fderiv_comm_eq_add_of_decay`: `fderiv (comm Z) = fderiv (commMain Z) + fderiv (commPsi Z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace YBWidth

open YBComm PhasePrim GeomXAsm RayFTCAux RayPrimAux RayPrimW ZPrimKernel

/-! ## 1. Pointwise Leibniz expansion of `[D_{μ+1}, cutMain]` -/

/-- For a phase-independent field `Z` (`∀ t, Z t = Z τ`), `[D_{μ+1}, cutMain] Z = commMain Z`
at any off-axis point `y` where `Z τ` is `C²`. -/
theorem commMain_eq_of_timeIndep {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (ν μ R : ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (hZ : ∀ t, Z t = Z τ)
    {y : Space} (hρ : 0 < ϱ y) (hZc : ContDiffAt ℝ 2 (Z τ) y) :
    physDmu ν (μ + 1) (cutMain ν R χy Z) τ y -
      cutMain ν R χy (physDmu ν (μ + 1) Z) τ y =
        commMain ν R χy Z τ y := by
  have hya : y ∉ axis := tcle_notaxis hρ
  have hcc : ContDiffAt ℝ 2 (tcC0 ν R χy) (ϱ y) := tcle_c0_smooth hχ ν R hρ.ne'
  have hϱc : ContDiffAt ℝ 2 ϱ y := contDiffOn_ϱ.contDiffAt (isOpen_compl_axis.mem_nhds hya)
  have hC : ContDiffAt ℝ 2 (fun y' => tcC0 ν R χy (ϱ y')) y := hcc.comp y hϱc
  have hZd : DifferentiableAt ℝ (Z τ) y := hZc.differentiableAt (by norm_num)
  have hCd : DifferentiableAt ℝ (fun y' => tcC0 ν R χy (ϱ y')) y := hC.differentiableAt (by norm_num)
  have hccd : DifferentiableAt ℝ (tcC0 ν R χy) (ϱ y) := hcc.differentiableAt (by norm_num)
  have ht_cut : deriv (fun t => cutMain ν R χy Z t y) τ = 0 := by
    have : (fun t => cutMain ν R χy Z t y) = fun _ => cutMain ν R χy Z τ y := by
      funext t; simp [cutMain, hZ t]
    rw [this, deriv_const]
  have ht_Z : deriv (fun t => Z t y) τ = 0 := by
    have : (fun t => Z t y) = fun _ => Z τ y := by funext t; rw [hZ t]
    rw [this, deriv_const]
  have hD : fderiv ℝ (cutMain ν R χy Z τ) y y =
      tcC0 ν R χy (ϱ y) • fderiv ℝ (Z τ) y y +
        (ϱ y * deriv (tcC0 ν R χy) (ϱ y)) • Z τ y := by
    have h1 : HasFDerivAt (cutMain ν R χy Z τ) _ y :=
      hCd.hasFDerivAt.smul hZd.hasFDerivAt
    rw [h1.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [tcle_dy_comp hρ hccd]
  have hLap : physLap (cutMain ν R χy Z τ) y =
      (deriv (deriv (tcC0 ν R χy)) (ϱ y) + deriv (tcC0 ν R χy) (ϱ y) / ϱ y) • Z τ y +
        ((2 : ℝ) • (deriv (tcC0 ν R χy) (ϱ y) • fderiv ℝ (Z τ) y (radialUnit y)) +
          tcC0 ν R χy (ϱ y) • physLap (Z τ) y) := by
    unfold cutMain
    rw [tcle_lap_smul hC hZc, tcle_lapS_comp hρ hcc, tcle_grad_sum _ hρ hccd (fderiv ℝ (Z τ) y)]
    abel
  have hDW : physDmu ν (μ + 1) (cutMain ν R χy Z) τ y =
      deriv (fun t => cutMain ν R χy Z t y) τ -
        (1 / 2 : ℝ) • fderiv ℝ (cutMain ν R χy Z τ) y y -
          ν • physLap (cutMain ν R χy Z τ) y + (μ + 1 - 1 / 2) • cutMain ν R χy Z τ y := rfl
  have hDZ : cutMain ν R χy (physDmu ν (μ + 1) Z) τ y =
      tcC0 ν R χy (ϱ y) • (deriv (fun t => Z t y) τ - (1 / 2 : ℝ) • fderiv ℝ (Z τ) y y -
        ν • physLap (Z τ) y + (μ + 1 - 1 / 2) • Z τ y) := rfl
  have hCM : cutMain ν R χy Z τ y = tcC0 ν R χy (ϱ y) • Z τ y := rfl
  rw [hDW, hDZ, ht_cut, ht_Z, hD, hLap, hCM]
  unfold commMain tcA1 tcA2
  module

/-- Pointwise decomposition `comm = commMain + commPsi` for a phase-independent field `Z` at any
off-axis point `y` where `Z τ` and `psiFld Z τ` are `C²`. -/
theorem comm_eq_commMain_add_commPsi {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (ν μ R : ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (hZ : ∀ t, Z t = Z τ)
    {y : Space} (hρ : 0 < ϱ y) (hZc : ContDiffAt ℝ 2 (Z τ) y)
    (hψc : ContDiffAt ℝ 2 (psiFld Z τ) y) :
    comm ν μ R χy Z τ y = commMain ν R χy Z τ y + commPsi ν μ R χy Z τ y := by
  have hya : y ∉ axis := tcle_notaxis hρ
  have hcc : ContDiffAt ℝ 2 (tcC0 ν R χy) (ϱ y) := tcle_c0_smooth hχ ν R hρ.ne'
  have hff : ContDiffAt ℝ 2 (tcF0 ν R χy) (ϱ y) := tcle_f0_smooth hχ ν R hρ.ne'
  have hϱc : ContDiffAt ℝ 2 ϱ y := contDiffOn_ϱ.contDiffAt (isOpen_compl_axis.mem_nhds hya)
  have hC : ContDiffAt ℝ 2 (fun y' => tcC0 ν R χy (ϱ y')) y := hcc.comp y hϱc
  have hF : ContDiffAt ℝ 2 (fun y' => tcF0 ν R χy (ϱ y')) y := hff.comp y hϱc
  have hCMc : ContDiffAt ℝ 2 (cutMain ν R χy Z τ) y := hC.smul hZc
  have hCPc : ContDiffAt ℝ 2 (cutPsi ν R χy Z τ) y := hF.smul hψc
  have hCMd : DifferentiableAt ℝ (cutMain ν R χy Z τ) y := hCMc.differentiableAt (by norm_num)
  have hCPd : DifferentiableAt ℝ (cutPsi ν R χy Z τ) y := hCPc.differentiableAt (by norm_num)
  have hW_eq : wardStreamCut ν R χy Z τ =
      fun y' => cutMain ν R χy Z τ y' + cutPsi ν R χy Z τ y' :=
    funext fun y' => wardStreamCut_eq_cutMain_add_cutPsi ν R χy Z τ y'
  have ht_W : deriv (fun t => wardStreamCut ν R χy Z t y) τ = 0 := by
    have : (fun t => wardStreamCut ν R χy Z t y) = fun _ => wardStreamCut ν R χy Z τ y := by
      funext t; simp [wardStreamCut, outPrim, hZ t]
    rw [this, deriv_const]
  have ht_M : deriv (fun t => cutMain ν R χy Z t y) τ = 0 := by
    have : (fun t => cutMain ν R χy Z t y) = fun _ => cutMain ν R χy Z τ y := by
      funext t; simp [cutMain, hZ t]
    rw [this, deriv_const]
  have ht_P : deriv (fun t => cutPsi ν R χy Z t y) τ = 0 := by
    have : (fun t => cutPsi ν R χy Z t y) = fun _ => cutPsi ν R χy Z τ y := by
      funext t; simp [cutPsi, psiFld, outPrim, hZ t]
    rw [this, deriv_const]
  have hD_add : fderiv ℝ (wardStreamCut ν R χy Z τ) y y =
      fderiv ℝ (cutMain ν R χy Z τ) y y + fderiv ℝ (cutPsi ν R χy Z τ) y y := by
    rw [hW_eq, (hCMd.hasFDerivAt.fun_add hCPd.hasFDerivAt).fderiv]
    rfl
  have hLap_add : physLap (wardStreamCut ν R χy Z τ) y =
      physLap (cutMain ν R χy Z τ) y + physLap (cutPsi ν R χy Z τ) y := by
    rw [hW_eq]
    exact tcle_physLap_add hCMc hCPc
  have hphys_add : physDmu ν (μ + 1) (wardStreamCut ν R χy Z) τ y =
      physDmu ν (μ + 1) (cutMain ν R χy Z) τ y +
        physDmu ν (μ + 1) (cutPsi ν R χy Z) τ y := by
    unfold physDmu
    rw [ht_W, ht_M, ht_P, hD_add, hLap_add, wardStreamCut_eq_cutMain_add_cutPsi]
    module
  have hcut_add := wardStreamCut_eq_cutMain_add_cutPsi ν R χy (physDmu ν (μ + 1) Z) τ y
  have hMain := commMain_eq_of_timeIndep hχ ν μ R Z τ hZ hρ hZc
  unfold YBComm.comm commPsi
  rw [hphys_add, hcut_add, ← hMain]
  abel

/-! ## 2. Smoothness of `psiFld` from `C^∞` and `O(ϱ^{-4})` decay -/

/-- If `W : Space → Space` is `C^∞` on `{y' | r₀ < ϱ y'}` (`0 ≤ r₀`) and all its derivatives are
`O(ϱ^{-4})` for `ϱ ≥ 2 * r₀ + 2`, then `outPrim (fun _ => W)` is jointly `C^∞` on `{x | r₀ < x.2.1}`. -/
theorem outPrim_contDiffOn_of_decay {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (W : Space → Space)
    (hW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W {y' : Space | r₀ < ϱ y'})
    (hdec : ∀ n : ℕ, ∃ C : ℝ, ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ n W y'‖ ≤ C * (ϱ y' ^ 4)⁻¹) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ × ℝ => outPrim (fun _ => W) x.1 x.2.1 x.2.2) {x | r₀ < x.2.1} := by
  set S : Set (ℝ × Space) := {q | r₀ < ϱ q.2} with hSdef
  have hSo : IsOpen S := isOpen_lt continuous_const (continuous_ϱ.comp continuous_snd)
  have hUo : IsOpen {y' : Space | r₀ < ϱ y'} := isOpen_lt continuous_const continuous_ϱ
  set W₂ : ℝ × Space → ℝ := fun q => W q.2 2 with hW₂def
  have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : Space => v 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff
  have hW₂s : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W₂ S :=
    hp.comp_contDiffOn (hW.comp contDiff_snd.contDiffOn (fun q hq => hq))
  choose C hC using hdec
  have hW₂_iter : ∀ (j : ℕ) (q : ℝ × Space), 2 * r₀ + 2 ≤ ϱ q.2 →
      ‖iteratedFDeriv ℝ j W₂ q‖ ≤ |C j| * (ϱ q.2 ^ 4)⁻¹ := by
    intro j q hq
    have hqS : q ∈ S := by show r₀ < ϱ q.2; linarith
    have hqU : q.2 ∈ {y' : Space | r₀ < ϱ y'} := hqS
    let Lproj : Space →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)
    let Lsnd : ℝ × Space →L[ℝ] Space := ContinuousLinearMap.snd ℝ ℝ Space
    have hLproj_norm : ‖Lproj‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      simpa [Lproj, one_mul] using PiLp.norm_apply_le v 2
    have hLsnd_norm : ‖Lsnd‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ Space
    have hW_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W q.2 :=
      hW.contDiffAt (hUo.mem_nhds hqU)
    have hcomp1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Lproj ∘ W) {y' : Space | r₀ < ϱ y'} :=
      Lproj.contDiff.comp_contDiffOn hW
    have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
    have h1 := ContinuousLinearMap.iteratedFDerivWithin_comp_right Lsnd hcomp1 hUo.uniqueDiffOn
      hSo.uniqueDiffOn hqS hj
    rw [show Lsnd ⁻¹' {y' : Space | r₀ < ϱ y'} = S from rfl,
      show Lsnd q = q.2 from rfl,
      iteratedFDerivWithin_of_isOpen j hSo hqS,
      iteratedFDerivWithin_of_isOpen j hUo hqU] at h1
    have hW₂_eq : W₂ = (Lproj ∘ W) ∘ Lsnd := rfl
    rw [hW₂_eq, h1]
    have h2 : ‖(iteratedFDeriv ℝ j (Lproj ∘ W) q.2).compContinuousLinearMap fun _ => Lsnd‖ ≤
        ‖iteratedFDeriv ℝ j (Lproj ∘ W) q.2‖ * 1 := by
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hLsnd_norm) (norm_nonneg _)
    have h3 : ‖iteratedFDeriv ℝ j (Lproj ∘ W) q.2‖ ≤ ‖iteratedFDeriv ℝ j W q.2‖ := by
      have := Lproj.norm_iteratedFDeriv_comp_left hW_at (n := j) hj
      exact this.trans (mul_le_of_le_one_left (norm_nonneg _) hLproj_norm)
    have h4 := hC j q.2 hq
    have h5 : C j * (ϱ q.2 ^ 4)⁻¹ ≤ |C j| * (ϱ q.2 ^ 4)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    linarith
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ × ℝ => x.2.1 * W !₂[x.2.1, 0, x.2.2] 2) {x | r₀ < x.2.1} := by
    have he : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W₂ ∘ b4bE) {x : ℝ × ℝ × ℝ | r₀ < x.2.1} := by
      refine hW₂s.comp b4bE.contDiff.contDiffOn (fun x hx => ?_)
      have hx' : r₀ < x.2.1 := hx
      rw [b4bE_apply]
      show r₀ < ϱ (!₂[x.2.1, 0, x.2.2] : Space)
      rw [b4b_rho x.2.1 x.2.2 (hr₀.trans hx'.le)]
      exact hx'
    exact ((contDiff_fst.comp contDiff_snd).contDiffOn.mul he).congr fun x _ => by
      simp [W₂, b4bE_apply]
  have hdecay : ∀ (n : ℕ) (K : Set (ℝ × ℝ)), IsCompact K →
      ∃ ρ₀ C' : ℝ, 1 ≤ ρ₀ ∧ r₀ < ρ₀ ∧
        ∀ τ z : ℝ, (τ, z) ∈ K → ∀ ρ : ℝ, ρ₀ ≤ ρ →
          ‖iteratedFDeriv ℝ n (fun x : ℝ × ℝ × ℝ => x.2.1 * W !₂[x.2.1, 0, x.2.2] 2) (τ, ρ, z)‖ ≤
            C' / ρ ^ 2 := by
    intro n K _hK
    set En : ℝ := ‖b4bE‖
    refine ⟨2 * r₀ + 2, ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (2 * (|C (n - i)| * En ^ (n - i))),
      by linarith, by linarith, fun τ z _ ρ hρ => ?_⟩
    have hρ2 : 2 ≤ ρ := by linarith
    have hρ0 : 0 ≤ ρ := by linarith
    set x : ℝ × ℝ × ℝ := (τ, ρ, z)
    have hex : b4bE x = (τ, !₂[ρ, 0, z]) := b4bE_apply x
    have hexS : b4bE x ∈ S := by
      rw [hex]
      show r₀ < ϱ (!₂[ρ, 0, z] : Space)
      rw [b4b_rho ρ z hρ0]; linarith
    have hϱ : ϱ (b4bE x).2 = ρ := by rw [hex]; exact b4b_rho ρ z hρ0
    have hWe : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W₂ ∘ b4bE) (b4bE ⁻¹' S) :=
      hW₂s.comp b4bE.contDiff.contDiffOn (fun y hy => hy)
    have hbnd : ∀ j : ℕ, ‖iteratedFDeriv ℝ j (W₂ ∘ b4bE) x‖ ≤ |C j| * En ^ j * (ρ ^ 4)⁻¹ := by
      intro j
      refine (b4b_comp_norm W₂ S hSo hW₂s j x hexS).trans ?_
      have h1 := hW₂_iter j (b4bE x) (by rw [hϱ]; linarith)
      rw [hϱ] at h1
      calc ‖iteratedFDeriv ℝ j W₂ (b4bE x)‖ * ‖b4bE‖ ^ j ≤ (|C j| * (ρ ^ 4)⁻¹) * En ^ j :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = |C j| * En ^ j * (ρ ^ 4)⁻¹ := by ring
    have hft : IsOpen (b4bE ⁻¹' S) := hSo.preimage b4bE.continuous
    have hxt : x ∈ b4bE ⁻¹' S := hexS
    have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ × ℝ × ℝ => y.2.1) :=
      contDiff_fst.comp contDiff_snd
    have hn : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
    have hL := norm_iteratedFDerivWithin_mul_le hfs.contDiffOn hWe hft.uniqueDiffOn hxt hn
    have hFeq : (fun y : ℝ × ℝ × ℝ => y.2.1 * W !₂[y.2.1, 0, y.2.2] 2) =
        fun y => (fun y : ℝ × ℝ × ℝ => y.2.1) y * (W₂ ∘ b4bE) y := by
      funext y; simp [W₂, b4bE_apply]
    rw [hFeq]
    have hkey : (ρ + 1) * (ρ ^ 4)⁻¹ ≤ 2 / ρ ^ 2 := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : ρ + 1 ≤ 2 * ρ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ρ)]
    rw [iteratedFDerivWithin_of_isOpen n hft hxt] at hL
    refine hL.trans ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    have hi := b4b_lin_iter i x
    rw [iteratedFDerivWithin_of_isOpen i hft hxt, iteratedFDerivWithin_of_isOpen (n - i) hft hxt]
    have hj := hbnd (n - i)
    have hxρ : |x.2.1| = ρ := abs_of_nonneg hρ0
    rw [hxρ] at hi
    have hC0 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : ℝ × ℝ × ℝ => y.2.1) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (W₂ ∘ b4bE) x‖
        ≤ (n.choose i : ℝ) * (ρ + 1) * (|C (n - i)| * En ^ (n - i) * (ρ ^ 4)⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hi hC0) hj (norm_nonneg _)
            (mul_nonneg hC0 (by positivity))
      _ = (n.choose i : ℝ) * (|C (n - i)| * En ^ (n - i)) * ((ρ + 1) * (ρ ^ 4)⁻¹) := by ring
      _ ≤ (n.choose i : ℝ) * (|C (n - i)| * En ^ (n - i)) * (2 / ρ ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg hC0 (by positivity))
      _ = ((n.choose i : ℝ) * (2 * (|C (n - i)| * En ^ (n - i)))) / ρ ^ 2 := by ring
  simpa [outPrim] using paramIntSmooth_proved _ r₀ hG hdecay

/-- Under the same hypotheses as `outPrim_contDiffOn_of_decay`, `psiFld (fun _ => W) τ` is `C^∞`
on `{y' : Space | r₀ < ϱ y'}`. -/
theorem psiFld_contDiffOn_of_decay {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (W : Space → Space)
    (hW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W {y' : Space | r₀ < ϱ y'})
    (hdec : ∀ n : ℕ, ∃ C : ℝ, ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ n W y'‖ ≤ C * (ϱ y' ^ 4)⁻¹) (τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiFld (fun _ => W) τ) {y' : Space | r₀ < ϱ y'} := by
  have hop := outPrim_contDiffOn_of_decay hr₀ W hW hdec
  have hWax : ∀ y' ∈ {y' : Space | r₀ < ϱ y'}, y' ∉ axis := by
    intro y' hy' h
    have h0 : ϱ y' = 0 := (mem_axis_iff y').1 h
    have hy'' : r₀ < ϱ y' := hy'
    linarith
  have hϱ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϱ {y' : Space | r₀ < ϱ y'} :=
    contDiffOn_ϱ.mono hWax
  have hz : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => y' 2)
      {y' : Space | r₀ < ϱ y'} :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.contDiffOn
  have hmap : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : Space => ((τ, ϱ y', y' 2) : ℝ × ℝ × ℝ)) {y' : Space | r₀ < ϱ y'} :=
    contDiffOn_const.prodMk (hϱ.prodMk hz)
  exact (hop.comp hmap (fun y' hy' => hy')).smul contDiffOn_const

/-! ## 3. Differentiability of `psiFld (physDmu ν (μ + 1) (fun _ => W))` -/

private theorem norm_iteratedFDeriv_physPd_le {f : Space → Space} {p : Space}
    (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f p) (i : Fin 3) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (physPd f i) p‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f p‖ := by
  let L : (Space →L[ℝ] Space) →L[ℝ] Space :=
    ContinuousLinearMap.apply ℝ Space (coordinateVector i)
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ => ?_
    simpa [L, one_mul, tcd_norm_cv] using φ.le_opNorm (coordinateVector i)
  have hf' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) p :=
    hf.fderiv_right (by simp)
  have hj : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have h1 := L.norm_iteratedFDeriv_comp_left hf' (n := n) hj
  rw [norm_iteratedFDeriv_fderiv] at h1
  exact h1.trans (mul_le_of_le_one_left (norm_nonneg _) hLn)

private theorem contDiffOn_physPd {f : Space → Space} {U : Set Space} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) (i : Fin 3) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physPd f i) U := by
  let L : (Space →L[ℝ] Space) →L[ℝ] Space :=
    ContinuousLinearMap.apply ℝ Space (coordinateVector i)
  exact L.contDiff.comp_contDiffOn (hf.fderiv_of_isOpen hU (by simp))

private theorem contDiffOn_physLap {f : Space → Space} {U : Set Space} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physLap f) U :=
  ContDiffOn.sum fun i _ => contDiffOn_physPd hU (contDiffOn_physPd hU hf i) i

private theorem norm_fderiv_physLap_le {f : Space → Space} {p : Space}
    (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f p) :
    ‖fderiv ℝ (physLap f) p‖ ≤ 3 * ‖iteratedFDeriv ℝ 3 f p‖ := by
  let L : Fin 3 → (Space →L[ℝ] Space) →L[ℝ] Space :=
    fun i => ContinuousLinearMap.apply ℝ Space (coordinateVector i)
  have hcd2 : ∀ i : Fin 3, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physPd2 f i i) p := by
    intro i
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physPd f i) p :=
      (L i).contDiff.contDiffAt.comp p (hf.fderiv_right (by simp))
    exact (L i).contDiff.contDiffAt.comp p (h1.fderiv_right (by simp))
  have hd : ∀ i : Fin 3, DifferentiableAt ℝ (physPd2 f i i) p :=
    fun i => (hcd2 i).differentiableAt (by simp)
  have hsum : HasFDerivAt (physLap f) (∑ i : Fin 3, fderiv ℝ (physPd2 f i i) p) p := by
    unfold physLap
    exact HasFDerivAt.fun_sum fun i _ => (hd i).hasFDerivAt
  rw [hsum.fderiv]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ i : Fin 3, ‖fderiv ℝ (physPd2 f i i) p‖ ≤ ‖iteratedFDeriv ℝ 3 f p‖ := by
    intro i
    rw [← norm_iteratedFDeriv_one]
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physPd f i) p :=
      (L i).contDiff.contDiffAt.comp p (hf.fderiv_right (by simp))
    exact (norm_iteratedFDeriv_physPd_le h1 i 1).trans (norm_iteratedFDeriv_physPd_le hf i 2)
  calc ∑ i : Fin 3, ‖fderiv ℝ (physPd2 f i i) p‖
      ≤ ∑ _i : Fin 3, ‖iteratedFDeriv ℝ 3 f p‖ := Finset.sum_le_sum fun i _ => hb i
    _ = 3 * ‖iteratedFDeriv ℝ 3 f p‖ := by simp

private theorem rayDecayW_of_strip {Z : ℝ → Space → Space} {τ : ℝ} {U : Set Space} (hU : IsOpen U)
    (hZ : ContDiffOn ℝ 1 (Z τ) U) {r₁ R₁ C z : ℝ} (hr₁ : 0 < r₁)
    (hmem : ∀ ρ : ℝ, r₁ ≤ ρ → ∀ z' : ℝ, hpt ρ z' ∈ U)
    (hfar : ∀ ρ : ℝ, R₁ ≤ ρ → r₁ ≤ ρ → ∀ z' : ℝ, |z' - z| < 1 →
      ‖Z τ (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ) ∧ ‖fderiv ℝ (Z τ) (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ)) :
    ∃ K : ℝ, RayDecayW Z τ r₁ z 1 K := by
  set R₂ := max R₁ r₁
  set S : Set Space := (fun p : ℝ × ℝ => hpt p.1 p.2) '' (Icc r₁ R₂ ×ˢ Icc (z - 1) (z + 1))
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image continuous_hpt_pair
  have hSU : S ⊆ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact hmem p.1 hp.1.1 p.2
  obtain ⟨M₁, hM₁⟩ := hS.exists_bound_of_continuousOn (hZ.continuousOn.mono hSU)
  obtain ⟨M₂, hM₂⟩ := hS.exists_bound_of_continuousOn
    ((hZ.continuousOn_fderiv_of_isOpen hU le_rfl).mono hSU)
  set M := max (max M₁ M₂) 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hinS : ∀ ρ : ℝ, r₁ ≤ ρ → ρ ≤ R₂ → ∀ z' : ℝ, |z' - z| < 1 → hpt ρ z' ∈ S := by
    intro ρ h1 h2 z' hz'
    have := abs_lt.1 hz'
    exact ⟨(ρ, z'), ⟨⟨h1, h2⟩, ⟨by linarith, by linarith⟩⟩, rfl⟩
  refine ⟨max C (M * R₂ ^ 3), ?_, ?_, ?_⟩
  · intro ρ hρ z' _
    exact (hZ.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hmem ρ hρ z'))
  · intro ρ hρ z' hz'
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr₁ hρ
    refine le_of_split hρ0 hM0 (fun h => ?_) (fun h => ?_)
    · exact (hM₁ _ (hinS ρ hρ h z' hz')).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hfar ρ ((le_max_left _ _).trans h.le) hρ z' hz').1
  · intro ρ hρ z' hz'
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr₁ hρ
    refine le_of_split hρ0 hM0 (fun h => ?_) (fun h => ?_)
    · exact (hM₂ _ (hinS ρ hρ h z' hz')).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hfar ρ ((le_max_left _ _).trans h.le) hρ z' hz').2

/-- Under the same hypotheses as `outPrim_contDiffOn_of_decay`, `psiFld (physDmu ν (μ + 1) (fun _ => W)) τ`
is differentiable at every `y` with `r₀ < ϱ y`. -/
theorem differentiableAt_psiFld_physDmu_of_decay {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (ν μ : ℝ)
    (W : Space → Space)
    (hW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W {y' : Space | r₀ < ϱ y'})
    (hdec : ∀ n : ℕ, ∃ C : ℝ, ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ n W y'‖ ≤ C * (ϱ y' ^ 4)⁻¹)
    (τ : ℝ) {y : Space} (hy : r₀ < ϱ y) :
    DifferentiableAt ℝ (psiFld (physDmu ν (μ + 1) (fun _ => W)) τ) y := by
  set U : Set Space := {y' : Space | r₀ < ϱ y'}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  set Z' := physDmu ν (μ + 1) (fun _ => W)
  have hZ'_eq : Z' τ = fun y' =>
      -(1 / 2 : ℝ) • fderiv ℝ W y' y' - ν • physLap W y' + (μ + 1 - 1 / 2) • W y' := by
    funext y'
    unfold Z' physDmu
    rw [deriv_const, zero_sub, neg_smul]
  have hZ'_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Z' τ) U := by
    rw [hZ'_eq]
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => fderiv ℝ W y' y') U :=
      (hW.fderiv_of_isOpen hUo (by simp)).clm_apply contDiffOn_id
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physLap W) U := contDiffOn_physLap hUo hW
    exact ((h1.const_smul (-(1 / 2 : ℝ))).sub (h2.const_smul ν)).add
      (hW.const_smul (μ + 1 - 1 / 2))
  set r₁ : ℝ := (r₀ + ϱ y) / 2 with hr₁_def
  have hr₁_pos : 0 < r₁ := by rw [hr₁_def]; linarith
  have hr₀_r₁ : r₀ < r₁ := by rw [hr₁_def]; linarith
  have hr₁_y : r₁ < ϱ y := by rw [hr₁_def]; linarith
  have hmem : ∀ ρ : ℝ, r₁ ≤ ρ → ∀ z' : ℝ, hpt ρ z' ∈ U := by
    intro ρ hρ z'
    show r₀ < ϱ (hpt ρ z')
    rw [ϱ_hpt (lt_of_lt_of_le hr₁_pos hρ)]
    exact lt_of_lt_of_le hr₀_r₁ hρ
  choose C hC using hdec
  set C0 := max (C 0) 0
  set C1 := max (C 1) 0
  set C2 := max (C 2) 0
  set C3 := max (C 3) 0
  set z := y 2
  set K_far : ℝ := (1 / 2) * (C2 * (2 + |z|) + C1) + |ν| * (3 * C3) + |μ + 1 - 1 / 2| * C0 +
    (1 / 2) * (C1 * (2 + |z|)) + |ν| * (3 * C2) + |μ + 1 - 1 / 2| * C1
  obtain ⟨K, hK⟩ := rayDecayW_of_strip hUo (hZ'_cd.of_le (by simp)) hr₁_pos hmem
    (R₁ := 2 * r₀ + 2) (C := K_far) (z := z) (fun ρ hρ _ z' hz' => by
      have hρ2 : 2 ≤ ρ := by linarith
      have hρ1 : 1 ≤ ρ := by linarith
      have hρ0 : 0 < ρ := by linarith
      set p := hpt ρ z'
      have hϱp : ϱ p = ρ := ϱ_hpt hρ0 z'
      have hpU : p ∈ U := by show r₀ < ϱ p; rw [hϱp]; linarith
      have hW_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W p := hW.contDiffAt (hUo.mem_nhds hpU)
      have hW_c2 : ContDiffAt ℝ 2 W p := hW_at.of_le (by simp)
      have hp_norm : ‖p‖ ≤ (2 + |z|) * ρ := by
        have h1 : ‖p‖ ≤ ρ + |z'| := tcd_norm_pt ρ z' hρ0.le
        have h2 : |z'| ≤ |z| + 1 := by
          have := abs_lt.1 hz'
          have := abs_sub_abs_le_abs_sub z' z
          linarith
        nlinarith [abs_nonneg z]
      have hpow4_le_3 : (ρ ^ 4)⁻¹ ≤ ρ ^ (-3 : ℝ) := by
        rw [Real.rpow_neg hρ0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hρ1 (by norm_num : 3 ≤ 4))
      have hpow4_mul_ρ : (ρ ^ 4)⁻¹ * ρ = ρ ^ (-3 : ℝ) := by
        rw [Real.rpow_neg hρ0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp
      have hb0 : ‖W p‖ ≤ C0 * (ρ ^ 4)⁻¹ := by
        rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
        have := hC 0 p (by rw [hϱp]; exact hρ)
        rw [hϱp] at this
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      have hb1 : ‖fderiv ℝ W p‖ ≤ C1 * (ρ ^ 4)⁻¹ := by
        rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
        have := hC 1 p (by rw [hϱp]; exact hρ)
        rw [hϱp] at this
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      have hb2 : ‖iteratedFDeriv ℝ 2 W p‖ ≤ C2 * (ρ ^ 4)⁻¹ := by
        have := hC 2 p (by rw [hϱp]; exact hρ)
        rw [hϱp] at this
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      have hb3 : ‖iteratedFDeriv ℝ 3 W p‖ ≤ C3 * (ρ ^ 4)⁻¹ := by
        have := hC 3 p (by rw [hϱp]; exact hρ)
        rw [hϱp] at this
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      have hC0_pos : 0 ≤ C0 := le_max_right _ _
      have hC1_pos : 0 ≤ C1 := le_max_right _ _
      have hC2_pos : 0 ≤ C2 := le_max_right _ _
      have hC3_pos : 0 ≤ C3 := le_max_right _ _
      have hdil_val : ‖fderiv ℝ W p p‖ ≤ C1 * (2 + |z|) * ρ ^ (-3 : ℝ) := by
        calc ‖fderiv ℝ W p p‖ ≤ ‖fderiv ℝ W p‖ * ‖p‖ := (fderiv ℝ W p).le_opNorm p
          _ ≤ (C1 * (ρ ^ 4)⁻¹) * ((2 + |z|) * ρ) :=
              mul_le_mul hb1 hp_norm (norm_nonneg _) (by positivity)
          _ = C1 * (2 + |z|) * ((ρ ^ 4)⁻¹ * ρ) := by ring
          _ = C1 * (2 + |z|) * ρ ^ (-3 : ℝ) := by rw [hpow4_mul_ρ]
      have hlap_val : ‖physLap W p‖ ≤ 3 * C2 * ρ ^ (-3 : ℝ) := by
        calc ‖physLap W p‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 W p‖ := tcd_physLap_norm hW_c2
          _ ≤ 3 * (C2 * (ρ ^ 4)⁻¹) := mul_le_mul_of_nonneg_left hb2 (by norm_num)
          _ ≤ 3 * (C2 * ρ ^ (-3 : ℝ)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hpow4_le_3 hC2_pos) (by norm_num)
          _ = 3 * C2 * ρ ^ (-3 : ℝ) := by ring
      have hW_val : ‖W p‖ ≤ C0 * ρ ^ (-3 : ℝ) :=
        hb0.trans (mul_le_mul_of_nonneg_left hpow4_le_3 hC0_pos)
      constructor
      · -- bound on `‖Z' τ p‖`
        have hZp : Z' τ p = -(1 / 2 : ℝ) • fderiv ℝ W p p - ν • physLap W p +
            (μ + 1 - 1 / 2) • W p := by rw [hZ'_eq]
        rw [hZp]
        have h1 := norm_add_le (-(1 / 2 : ℝ) • fderiv ℝ W p p - ν • physLap W p)
          ((μ + 1 - 1 / 2) • W p)
        have h2 := norm_sub_le (-(1 / 2 : ℝ) • fderiv ℝ W p p) (ν • physLap W p)
        have hsm1 : ‖-(1 / 2 : ℝ) • fderiv ℝ W p p‖ = (1 / 2) * ‖fderiv ℝ W p p‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num)]
        have hsm2 : ‖ν • physLap W p‖ = |ν| * ‖physLap W p‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        have hsm3 : ‖(μ + 1 - 1 / 2) • W p‖ = |μ + 1 - 1 / 2| * ‖W p‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        have h3 : (1 / 2) * ‖fderiv ℝ W p p‖ ≤ (1 / 2) * (C1 * (2 + |z|) * ρ ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hdil_val (by norm_num)
        have h4 : |ν| * ‖physLap W p‖ ≤ |ν| * (3 * C2 * ρ ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlap_val (abs_nonneg ν)
        have h5 : |μ + 1 - 1 / 2| * ‖W p‖ ≤ |μ + 1 - 1 / 2| * (C0 * ρ ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hW_val (abs_nonneg _)
        have h6 : 0 ≤ ((1 / 2) * (C2 * (2 + |z|) + C1) + |ν| * (3 * C3) +
            |μ + 1 - 1 / 2| * C1) * ρ ^ (-3 : ℝ) := by positivity
        unfold K_far
        linarith
      · -- bound on `‖fderiv ℝ (Z' τ) p‖`
        have hd1 : HasFDerivAt (fun y' : Space => fderiv ℝ W y' y')
            ((fderiv ℝ W p).comp (ContinuousLinearMap.id ℝ Space) +
              (fderiv ℝ (fderiv ℝ W) p).flip p) p := by
          have hA : HasFDerivAt (fderiv ℝ W) (fderiv ℝ (fderiv ℝ W) p) p :=
            ((hW_c2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
          exact hA.clm_apply (hasFDerivAt_id p)
        have hd1_norm : ‖fderiv ℝ (fun y' : Space => fderiv ℝ W y' y') p‖ ≤
            (C2 * (2 + |z|) + C1) * ρ ^ (-3 : ℝ) := by
          rw [hd1.fderiv]
          refine (norm_add_le _ _).trans ?_
          have hflip : ‖(fderiv ℝ (fderiv ℝ W) p).flip p‖ ≤
              C2 * (2 + |z|) * ρ ^ (-3 : ℝ) := by
            have hf1 : ‖(fderiv ℝ (fderiv ℝ W) p).flip p‖ ≤
                ‖fderiv ℝ (fderiv ℝ W) p‖ * ‖p‖ := by
              refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
              simp only [ContinuousLinearMap.flip_apply]
              calc ‖fderiv ℝ (fderiv ℝ W) p v p‖ ≤ ‖fderiv ℝ (fderiv ℝ W) p v‖ * ‖p‖ :=
                    (fderiv ℝ (fderiv ℝ W) p v).le_opNorm p
                _ ≤ (‖fderiv ℝ (fderiv ℝ W) p‖ * ‖v‖) * ‖p‖ :=
                    mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ W) p).le_opNorm v)
                      (norm_nonneg p)
                _ = ‖fderiv ℝ (fderiv ℝ W) p‖ * ‖p‖ * ‖v‖ := by ring
            rw [tcd_norm_hess hW_c2] at hf1
            calc ‖(fderiv ℝ (fderiv ℝ W) p).flip p‖ ≤ ‖iteratedFDeriv ℝ 2 W p‖ * ‖p‖ := hf1
              _ ≤ (C2 * (ρ ^ 4)⁻¹) * ((2 + |z|) * ρ) :=
                  mul_le_mul hb2 hp_norm (norm_nonneg _) (by positivity)
              _ = C2 * (2 + |z|) * ((ρ ^ 4)⁻¹ * ρ) := by ring
              _ = C2 * (2 + |z|) * ρ ^ (-3 : ℝ) := by rw [hpow4_mul_ρ]
          have hid : ‖(fderiv ℝ W p).comp (ContinuousLinearMap.id ℝ Space)‖ ≤
              C1 * ρ ^ (-3 : ℝ) := by
            rw [ContinuousLinearMap.comp_id]
            exact hb1.trans (mul_le_mul_of_nonneg_left hpow4_le_3 hC1_pos)
          linarith
        have hlap_fd : ‖fderiv ℝ (physLap W) p‖ ≤ 3 * C3 * ρ ^ (-3 : ℝ) := by
          calc ‖fderiv ℝ (physLap W) p‖ ≤ 3 * ‖iteratedFDeriv ℝ 3 W p‖ :=
                norm_fderiv_physLap_le hW_at
            _ ≤ 3 * (C3 * (ρ ^ 4)⁻¹) := mul_le_mul_of_nonneg_left hb3 (by norm_num)
            _ ≤ 3 * (C3 * ρ ^ (-3 : ℝ)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hpow4_le_3 hC3_pos) (by norm_num)
            _ = 3 * C3 * ρ ^ (-3 : ℝ) := by ring
        have hW_fd : ‖fderiv ℝ W p‖ ≤ C1 * ρ ^ (-3 : ℝ) :=
          hb1.trans (mul_le_mul_of_nonneg_left hpow4_le_3 hC1_pos)
        have hd_all : HasFDerivAt (Z' τ)
            (-(1 / 2 : ℝ) • fderiv ℝ (fun y' : Space => fderiv ℝ W y' y') p -
              ν • fderiv ℝ (physLap W) p + (μ + 1 - 1 / 2) • fderiv ℝ W p) p := by
          rw [hZ'_eq]
          have hL_d : DifferentiableAt ℝ (physLap W) p :=
            ((contDiffOn_physLap hUo hW).contDiffAt (hUo.mem_nhds hpU)).differentiableAt (by simp)
          have hW_d : DifferentiableAt ℝ W p := hW_c2.differentiableAt (by norm_num)
          exact ((hd1.differentiableAt.hasFDerivAt.const_smul (-(1 / 2 : ℝ))).sub
            (hL_d.hasFDerivAt.const_smul ν)).add
            (hW_d.hasFDerivAt.const_smul (μ + 1 - 1 / 2))
        rw [hd_all.fderiv]
        have h1 := norm_add_le
          (-(1 / 2 : ℝ) • fderiv ℝ (fun y' : Space => fderiv ℝ W y' y') p -
            ν • fderiv ℝ (physLap W) p)
          ((μ + 1 - 1 / 2) • fderiv ℝ W p)
        have h2 := norm_sub_le
          (-(1 / 2 : ℝ) • fderiv ℝ (fun y' : Space => fderiv ℝ W y' y') p)
          (ν • fderiv ℝ (physLap W) p)
        have hsm1 : ‖-(1 / 2 : ℝ) • fderiv ℝ (fun y' : Space => fderiv ℝ W y' y') p‖ =
            (1 / 2) * ‖fderiv ℝ (fun y' : Space => fderiv ℝ W y' y') p‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num)]
        have hsm2 : ‖ν • fderiv ℝ (physLap W) p‖ = |ν| * ‖fderiv ℝ (physLap W) p‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        have hsm3 : ‖(μ + 1 - 1 / 2) • fderiv ℝ W p‖ = |μ + 1 - 1 / 2| * ‖fderiv ℝ W p‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        have h3 : (1 / 2) * ‖fderiv ℝ (fun y' : Space => fderiv ℝ W y' y') p‖ ≤
            (1 / 2) * ((C2 * (2 + |z|) + C1) * ρ ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hd1_norm (by norm_num)
        have h4 : |ν| * ‖fderiv ℝ (physLap W) p‖ ≤ |ν| * (3 * C3 * ρ ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlap_fd (abs_nonneg ν)
        have h5 : |μ + 1 - 1 / 2| * ‖fderiv ℝ W p‖ ≤ |μ + 1 - 1 / 2| * (C1 * ρ ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hW_fd (abs_nonneg _)
        have h6 : 0 ≤ ((1 / 2) * (C1 * (2 + |z|)) + |ν| * (3 * C2) +
            |μ + 1 - 1 / 2| * C0) * ρ ^ (-3 : ℝ) := by positivity
        unfold K_far
        linarith)
  have hprim := primData_of_decayW hK hr₁_pos one_pos hr₁_y
  have hρ_pos : 0 < ϱ y := lt_of_le_of_lt hr₀ hy
  have hya : y ∉ axis := tcle_notaxis hρ_pos
  have hϱ_d : DifferentiableAt ℝ ϱ y :=
    (contDiffOn_ϱ.contDiffAt (isOpen_compl_axis.mem_nhds hya) : ContDiffAt ℝ 2 ϱ y).differentiableAt
      (by norm_num)
  have hz_d : DifferentiableAt ℝ (fun y' : Space => y' 2) y :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt
  have hop_d : DifferentiableAt ℝ (fun y' : Space => outPrim Z' τ (ϱ y') (y' 2)) y := by
    change DifferentiableAt ℝ ((fun p : ℝ × ℝ => outPrim Z' τ p.1 p.2) ∘
      (fun y' : Space => (ϱ y', y' 2))) y
    exact hprim.2.2.differentiableAt.comp y (hϱ_d.prodMk hz_d)
  exact hop_d.smul_const (coordinateVector 2)

/-! ## 4. Derivative splitting `fderiv comm = fderiv commMain + fderiv commPsi` -/

/-- For a phase-independent field `Z = fun _ => W` satisfying `hW` and `hdec` on `{y' | r₀ < ϱ y'}`
(`0 ≤ r₀`), at every point `y` with `r₀ < ϱ y`:
`fderiv ℝ (comm ν μ R χy Z τ) y = fderiv ℝ (commMain ν R χy Z τ) y + fderiv ℝ (commPsi ν μ R χy Z τ) y`. -/
theorem fderiv_comm_eq_add_of_decay {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (ν μ R : ℝ) (W : Space → Space)
    (hW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W {y' : Space | r₀ < ϱ y'})
    (hdec : ∀ n : ℕ, ∃ C : ℝ, ∀ y' : Space, 2 * r₀ + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ n W y'‖ ≤ C * (ϱ y' ^ 4)⁻¹)
    (τ : ℝ) {y : Space} (hy : r₀ < ϱ y) :
    let Z : ℝ → Space → Space := fun _ => W
    fderiv ℝ (comm ν μ R χy Z τ) y =
      fderiv ℝ (commMain ν R χy Z τ) y + fderiv ℝ (commPsi ν μ R χy Z τ) y := by
  intro Z
  set U : Set Space := {y' : Space | r₀ < ϱ y'}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hψ_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiFld Z τ) U :=
    psiFld_contDiffOn_of_decay hr₀ W hW hdec τ
  have hev : comm ν μ R χy Z τ =ᶠ[𝓝 y]
      fun y' => commMain ν R χy Z τ y' + commPsi ν μ R χy Z τ y' := by
    filter_upwards [hUo.mem_nhds hy] with y' hy'
    have hρ' : 0 < ϱ y' := lt_of_le_of_lt hr₀ hy'
    have hZc' : ContDiffAt ℝ 2 (Z τ) y' :=
      (hW.contDiffAt (hUo.mem_nhds hy')).of_le (by simp)
    have hψc' : ContDiffAt ℝ 2 (psiFld Z τ) y' :=
      (hψ_cd.contDiffAt (hUo.mem_nhds hy')).of_le (by simp)
    exact comm_eq_commMain_add_commPsi hχ ν μ R Z τ (fun _ => rfl) hρ' hZc' hψc'
  have hρ : 0 < ϱ y := lt_of_le_of_lt hr₀ hy
  have hZc : ContDiffAt ℝ 2 (Z τ) y :=
    (hW.contDiffAt (hUo.mem_nhds hy)).of_le (by simp)
  have hdA1 : HasDerivAt (tcA1 ν R χy) (deriv (tcA1 ν R χy) (ϱ y)) (ϱ y) :=
    (Sub8_1_1_2_3.tcCoeff_diffAt (ν := ν) (R := R) hχ hρ).1.hasDerivAt
  have hdA2 : HasDerivAt (tcA2 ν R χy) (deriv (tcA2 ν R χy) (ϱ y)) (ϱ y) :=
    (Sub8_1_1_2_3.tcCoeff_diffAt (ν := ν) (R := R) hχ hρ).2.1.hasDerivAt
  have hd_main : DifferentiableAt ℝ (commMain ν R χy Z τ) y :=
    (fderiv_commMain_bound (ν := ν) (R := R) hχ Z τ hρ hZc hdA1 hdA2).1
  have hd_psi : DifferentiableAt ℝ (commPsi ν μ R χy Z τ) y := by
    have hWax : ∀ y' ∈ U, y' ∉ axis := by
      intro y' hy' h
      have h0 : ϱ y' = 0 := (mem_axis_iff y').1 h
      have hy'' : r₀ < ϱ y' := hy'
      linarith
    have hϱ_U : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϱ U := contDiffOn_ϱ.mono hWax
    have hne : ∀ y' ∈ U, ϱ y' ≠ 0 := fun y' hy' => ϱ_ne_zero (hWax y' hy')
    have hdχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv χy) :=
      (show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) χy from hχ.smooth).deriv'
    have hage : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => ν * (R ^ 2 / ϱ y' ^ 2)) U :=
      contDiffOn_const.mul (ContDiffOn.div contDiffOn_const (hϱ_U.pow 2)
        (fun y' hy' => pow_ne_zero 2 (hne y' hy')))
    have hF_U : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => tcF0 ν R χy (ϱ y')) U := by
      unfold tcF0
      exact ((hdχ.comp_contDiffOn hage).mul
        (ContDiffOn.div contDiffOn_const (hϱ_U.pow 3)
          (fun y' hy' => pow_ne_zero 3 (hne y' hy')))).div hϱ_U hne
    have hCP_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutPsi ν R χy Z τ) U :=
      hF_U.smul hψ_cd
    have h1_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (physDmu ν (μ + 1) (cutPsi ν R χy Z) τ) U := by
      have heq : physDmu ν (μ + 1) (cutPsi ν R χy Z) τ = fun y' =>
          -(1 / 2 : ℝ) • fderiv ℝ (cutPsi ν R χy Z τ) y' y' -
            ν • physLap (cutPsi ν R χy Z τ) y' + (μ + 1 - 1 / 2) • cutPsi ν R χy Z τ y' := by
        funext y'
        unfold physDmu
        have ht : (fun s => cutPsi ν R χy Z s y') = fun _ => cutPsi ν R χy Z τ y' := by
          funext s; simp [cutPsi, psiFld, outPrim, Z]
        rw [ht, deriv_const, zero_sub, neg_smul]
      rw [heq]
      have hdil : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y' : Space => fderiv ℝ (cutPsi ν R χy Z τ) y' y') U :=
        (hCP_cd.fderiv_of_isOpen hUo (by simp)).clm_apply contDiffOn_id
      have hlap : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physLap (cutPsi ν R χy Z τ)) U :=
        contDiffOn_physLap hUo hCP_cd
      exact ((hdil.const_smul (-(1 / 2 : ℝ))).sub (hlap.const_smul ν)).add
        (hCP_cd.const_smul (μ + 1 - 1 / 2))
    have hd1 : DifferentiableAt ℝ (physDmu ν (μ + 1) (cutPsi ν R χy Z) τ) y :=
      (h1_cd.contDiffAt (hUo.mem_nhds hy)).differentiableAt (by simp)
    have hd_F : DifferentiableAt ℝ (fun y' : Space => tcF0 ν R χy (ϱ y')) y :=
      (hF_U.contDiffAt (hUo.mem_nhds hy)).differentiableAt (by simp)
    have hd_ψ2 : DifferentiableAt ℝ (psiFld (physDmu ν (μ + 1) Z) τ) y :=
      differentiableAt_psiFld_physDmu_of_decay hr₀ ν μ W hW hdec τ hy
    have hd2 : DifferentiableAt ℝ (cutPsi ν R χy (physDmu ν (μ + 1) Z) τ) y :=
      hd_F.smul hd_ψ2
    exact hd1.sub hd2
  rw [hev.fderiv_eq, (hd_main.hasFDerivAt.fun_add hd_psi.hasFDerivAt).fderiv]

end YBWidth

end UnforcedLeray.Short.PartIIIb.Concrete

end
