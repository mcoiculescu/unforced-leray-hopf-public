import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen1Bound.MomentNorms
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_5.IbpQ.Common

/-!
# Gaussian Integration by Parts for Bounded Smooth Profiles (`GaussIBP`)

Adapts `ibp_core` (`PartIII-b_C_flatset_col_7_3_2_1_2_5/IbpQ/Common.lean`) from compactly supported
`IsMeridTest` profiles to arbitrary smooth profiles with globally bounded derivatives:
1. `etaMul_planeHeat_of_bdd`: `x.2 • planeHeat θ (ζ(s', ·)) x = planeHeat θ (etaMul ζ (s', ·)) x -
   (2 * θ) • planeHeat θ (pdEta ζ (s', ·)) x`.
2. `gaussDt_lap_of_bdd`: `∫ y, gaussDt 2 θ y • ζ(s', x - planeι y) =
   planeHeat θ (laplaceQEta ζ (s', ·)) x`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0225
  UnforcedLeray.B0226
open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.Heat (gaussDt)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

namespace FlatAdjointElemAux

/-! ### 1. Integrability of `ibpDfun` and `ibpA0` -/

theorem integrable_ibpDfun {θ : ℝ} (hθ : 0 < θ) {v : Euc 2} (hv : ‖v‖ = 1) :
    Integrable (ibpDfun θ v) := by
  have hcontD : Continuous (fun y : Euc 2 => -(inner ℝ y v / (2 * θ))) := by fun_prop
  refine ibp_integrable_weight hθ (w := fun y : Euc 2 => -(inner ℝ y v / (2 * θ)))
    (C := 1 / (2 * θ)) hcontD ?_
  intro y
  show |-(inner ℝ y v / (2 * θ))| ≤ 1 / (2 * θ) * (1 + ‖y‖ ^ 2)
  have hi : |inner ℝ y v| ≤ 1 + ‖y‖ ^ 2 := by
    have h1 := abs_real_inner_le_norm y v
    rw [hv, mul_one] at h1
    nlinarith [sq_nonneg (‖y‖ - 1), norm_nonneg y]
  have h2θ : 0 < 2 * θ := by linarith
  rw [abs_neg, abs_div, abs_of_pos h2θ]
  calc |inner ℝ y v| / (2 * θ) ≤ (1 + ‖y‖ ^ 2) / (2 * θ) := by gcongr
    _ = 1 / (2 * θ) * (1 + ‖y‖ ^ 2) := by ring

theorem integrable_ibpA0 {θ : ℝ} (hθ : 0 < θ) {v : Euc 2} (hv : ‖v‖ = 1) :
    Integrable (ibpA0 θ v) := by
  have hcontA : Continuous (fun y : Euc 2 => (inner ℝ y v) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) := by
    fun_prop
  refine ibp_integrable_weight hθ
    (w := fun y : Euc 2 => (inner ℝ y v) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ))
    (C := 1 / (4 * θ ^ 2) + 1 / (2 * θ)) hcontA ?_
  intro y
  show |(inner ℝ y v) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)| ≤
    (1 / (4 * θ ^ 2) + 1 / (2 * θ)) * (1 + ‖y‖ ^ 2)
  have h1 := abs_real_inner_le_norm y v
  rw [hv, mul_one] at h1
  have hi2 : (inner ℝ y v) ^ 2 ≤ 1 + ‖y‖ ^ 2 := by
    nlinarith [abs_nonneg (inner ℝ y v), sq_abs (inner ℝ y v), norm_nonneg y,
      mul_nonneg (sub_nonneg.2 h1) (add_nonneg (norm_nonneg y) (abs_nonneg (inner ℝ y v)))]
  have hq1 : (inner ℝ y v) ^ 2 / (4 * θ ^ 2) ≤ (1 + ‖y‖ ^ 2) / (4 * θ ^ 2) := by gcongr
  have hq2 : (1 + ‖y‖ ^ 2) / (4 * θ ^ 2) = 1 / (4 * θ ^ 2) * (1 + ‖y‖ ^ 2) := by ring
  have hb1 : 1 / (2 * θ) ≤ 1 / (2 * θ) * (1 + ‖y‖ ^ 2) := by
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * θ)) (sq_nonneg ‖y‖)
    nlinarith
  have hp1 : 0 ≤ 1 / (4 * θ ^ 2) * (1 + ‖y‖ ^ 2) := by positivity
  have hp2 : 0 ≤ 1 / (2 * θ) * (1 + ‖y‖ ^ 2) := by positivity
  have hq0 : 0 ≤ (inner ℝ y v) ^ 2 / (4 * θ ^ 2) := by positivity
  have hpos2 : 0 < 1 / (2 * θ) := by positivity
  have hexp : (1 / (4 * θ ^ 2) + 1 / (2 * θ)) * (1 + ‖y‖ ^ 2) =
      1 / (4 * θ ^ 2) * (1 + ‖y‖ ^ 2) + 1 / (2 * θ) * (1 + ‖y‖ ^ 2) := by ring
  rw [abs_le, hexp]
  constructor <;> linarith

/-! ### 2. First and second Gaussian integration by parts for bounded smooth profiles -/

/-- One integration by parts along a unit vector `v : Euc 2` with `w = (0, planeι v)`. -/
theorem ibp_one_of_bdd {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) {ζ : Profile → MeridC} (hζs : ContDiff ℝ ∞ ζ)
    {v : Euc 2} (hv : ‖v‖ = 1) {M0 M1 : ℝ}
    (hM0 : ∀ p, ‖ζ p‖ ≤ M0) (hM1 : ∀ p, ‖ibpPdW ζ (0, planeι v) p‖ ≤ M1)
    (x : ℝ × ℝ) :
    Integrable (fun y : Euc 2 => ibpDfun θ v y • ζ (σ, x - planeι y)) ∧
    Integrable (fun y : Euc 2 => gaussKernel 2 θ y • ibpPdW ζ (0, planeι v) (σ, x - planeι y)) ∧
    ∫ y : Euc 2, ibpDfun θ v y • ζ (σ, x - planeι y) =
      ∫ y : Euc 2, gaussKernel 2 θ y • ibpPdW ζ (0, planeι v) (σ, x - planeι y) := by
  set w : Profile := (0, planeι v)
  have hζd : Differentiable ℝ ζ := hζs.differentiable (by simp)
  have hζc : Continuous ζ := hζs.continuous
  have hW1s : ContDiff ℝ ∞ (ibpPdW ζ w) :=
    ((contDiff_infty_iff_fderiv.1 hζs).2).clm_apply contDiff_const
  have hW1c : Continuous (ibpPdW ζ w) := hW1s.continuous
  have hpc : Continuous (fun y : Euc 2 => ((σ, x - planeι y) : Profile)) :=
    continuous_const.prodMk (continuous_const.sub B0224.continuous_planeι)
  have hgc : Continuous (fun y : Euc 2 => ζ (σ, x - planeι y)) := hζc.comp hpc
  have hW1gc : Continuous (fun y : Euc 2 => ibpPdW ζ w (σ, x - planeι y)) := hW1c.comp hpc
  have hgd : Differentiable ℝ (fun y : Euc 2 => ζ (σ, x - planeι y)) :=
    ibp_differentiable_shift hζd σ x
  have hGint : Integrable (gaussKernel 2 θ) :=
    UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ
  have hGd : Differentiable ℝ (gaussKernel 2 θ) :=
    (UnforcedLeray.Gaussian.contDiff_gaussKernel (d := 2) (n := 1) θ).differentiable (by norm_num)
  have hDint : Integrable (ibpDfun θ v) := integrable_ibpDfun hθ hv
  have hMb0 : ∀ y : Euc 2, ‖ζ (σ, x - planeι y)‖ ≤ M0 := fun y => hM0 _
  have hMb1 : ∀ y : Euc 2, ‖ibpPdW ζ w (σ, x - planeι y)‖ ≤ M1 := fun y => hM1 _
  have I1 : Integrable (fun y : Euc 2 => ibpDfun θ v y • ζ (σ, x - planeι y)) :=
    ibp_integrable_smul_bdd hDint hgc hMb0
  have I2 : Integrable (fun y : Euc 2 => gaussKernel 2 θ y • ibpPdW ζ w (σ, x - planeι y)) :=
    ibp_integrable_smul_bdd hGint hW1gc hMb1
  have K1 : Integrable (fun y : Euc 2 =>
      fderiv ℝ (gaussKernel 2 θ) y v • ζ (σ, x - planeι y)) := by
    have e : (fun y : Euc 2 => fderiv ℝ (gaussKernel 2 θ) y v • ζ (σ, x - planeι y)) =
        fun y => ibpDfun θ v y • ζ (σ, x - planeι y) := by
      funext y
      rw [ibp_gauss_fderiv]
      rfl
    rw [e]
    exact I1
  have K2 : Integrable (fun y : Euc 2 =>
      gaussKernel 2 θ y • fderiv ℝ (fun z : Euc 2 => ζ (σ, x - planeι z)) y v) := by
    have e : (fun y : Euc 2 =>
        gaussKernel 2 θ y • fderiv ℝ (fun z : Euc 2 => ζ (σ, x - planeι z)) y v) =
        fun y => gaussKernel 2 θ y • -(ibpPdW ζ w (σ, x - planeι y)) := by
      funext y
      rw [ibp_shift_fderiv hζd σ x y v]
      rfl
    rw [e]
    exact ibp_integrable_smul_bdd hGint hW1gc.neg (M := M1) (fun y => by
      rw [norm_neg]
      exact hMb1 y)
  have K3 : Integrable (fun y : Euc 2 => gaussKernel 2 θ y • ζ (σ, x - planeι y)) :=
    ibp_integrable_smul_bdd hGint hgc hMb0
  have S2 := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := gaussKernel 2 θ) (g := fun y : Euc 2 => ζ (σ, x - planeι y)) (v := v)
    K1 K2 K3 (fun z _ => hGd.differentiableAt) (fun z _ => hgd z)
  have E3 : ∫ y : Euc 2, gaussKernel 2 θ y •
      fderiv ℝ (fun z : Euc 2 => ζ (σ, x - planeι z)) y v =
      -∫ y : Euc 2, gaussKernel 2 θ y • ibpPdW ζ w (σ, x - planeι y) := by
    rw [← integral_neg]
    congr 1
    funext y
    rw [ibp_shift_fderiv hζd σ x y v, smul_neg]
    rfl
  have E4 : ∫ y : Euc 2, fderiv ℝ (gaussKernel 2 θ) y v • ζ (σ, x - planeι y) =
      ∫ y : Euc 2, ibpDfun θ v y • ζ (σ, x - planeι y) := by
    congr 1
    funext y
    rw [ibp_gauss_fderiv]
    rfl
  rw [E3, E4] at S2
  exact ⟨I1, I2, (neg_inj.mp S2).symm⟩

/-- Two integrations by parts along a unit vector `v : Euc 2` with `w = (0, planeι v)`. -/
theorem ibp_two_of_bdd {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) {ζ : Profile → MeridC} (hζs : ContDiff ℝ ∞ ζ)
    {v : Euc 2} (hv : ‖v‖ = 1) {M0 M1 M2 : ℝ}
    (hM0 : ∀ p, ‖ζ p‖ ≤ M0)
    (hM1 : ∀ p, ‖ibpPdW ζ (0, planeι v) p‖ ≤ M1)
    (hM2 : ∀ p, ‖ibpPdW (ibpPdW ζ (0, planeι v)) (0, planeι v) p‖ ≤ M2)
    (x : ℝ × ℝ) :
    Integrable (fun y : Euc 2 => ibpA0 θ v y • ζ (σ, x - planeι y)) ∧
    Integrable (fun y : Euc 2 => gaussKernel 2 θ y •
      ibpPdW (ibpPdW ζ (0, planeι v)) (0, planeι v) (σ, x - planeι y)) ∧
    ∫ y : Euc 2, ibpA0 θ v y • ζ (σ, x - planeι y) =
      ∫ y : Euc 2, gaussKernel 2 θ y •
        ibpPdW (ibpPdW ζ (0, planeι v)) (0, planeι v) (σ, x - planeι y) := by
  set w : Profile := (0, planeι v)
  have hζd : Differentiable ℝ ζ := hζs.differentiable (by simp)
  have hζc : Continuous ζ := hζs.continuous
  have hW1s : ContDiff ℝ ∞ (ibpPdW ζ w) :=
    ((contDiff_infty_iff_fderiv.1 hζs).2).clm_apply contDiff_const
  have hW1c : Continuous (ibpPdW ζ w) := hW1s.continuous
  have hpc : Continuous (fun y : Euc 2 => ((σ, x - planeι y) : Profile)) :=
    continuous_const.prodMk (continuous_const.sub B0224.continuous_planeι)
  have hgc : Continuous (fun y : Euc 2 => ζ (σ, x - planeι y)) := hζc.comp hpc
  have hW1gc : Continuous (fun y : Euc 2 => ibpPdW ζ w (σ, x - planeι y)) := hW1c.comp hpc
  have hgd : Differentiable ℝ (fun y : Euc 2 => ζ (σ, x - planeι y)) :=
    ibp_differentiable_shift hζd σ x
  have hDint : Integrable (ibpDfun θ v) := integrable_ibpDfun hθ hv
  have hA0int : Integrable (ibpA0 θ v) := integrable_ibpA0 hθ hv
  have hMb0 : ∀ y : Euc 2, ‖ζ (σ, x - planeι y)‖ ≤ M0 := fun y => hM0 _
  have hMb1 : ∀ y : Euc 2, ‖ibpPdW ζ w (σ, x - planeι y)‖ ≤ M1 := fun y => hM1 _
  have I1 : Integrable (fun y : Euc 2 => ibpA0 θ v y • ζ (σ, x - planeι y)) :=
    ibp_integrable_smul_bdd hA0int hgc hMb0
  obtain ⟨_, I2, hstep2⟩ := ibp_one_of_bdd hθ σ hW1s hv hM1 hM2 x
  have J1 : Integrable (fun y : Euc 2 => fderiv ℝ (ibpDfun θ v) y v • ζ (σ, x - planeι y)) := by
    have e : (fun y : Euc 2 => fderiv ℝ (ibpDfun θ v) y v • ζ (σ, x - planeι y)) =
        fun y => ibpA0 θ v y • ζ (σ, x - planeι y) := by
      funext y
      rw [ibp_fderiv_Dfun hθ y v hv]
    rw [e]
    exact I1
  have J2 : Integrable (fun y : Euc 2 =>
      ibpDfun θ v y • fderiv ℝ (fun z : Euc 2 => ζ (σ, x - planeι z)) y v) := by
    have e : (fun y : Euc 2 =>
        ibpDfun θ v y • fderiv ℝ (fun z : Euc 2 => ζ (σ, x - planeι z)) y v) =
        fun y => ibpDfun θ v y • -(ibpPdW ζ w (σ, x - planeι y)) := by
      funext y
      rw [ibp_shift_fderiv hζd σ x y v]
      rfl
    rw [e]
    exact ibp_integrable_smul_bdd hDint hW1gc.neg (M := M1) (fun y => by
      rw [norm_neg]
      exact hMb1 y)
  have J3 : Integrable (fun y : Euc 2 => ibpDfun θ v y • ζ (σ, x - planeι y)) :=
    ibp_integrable_smul_bdd hDint hgc hMb0
  have S1 := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := ibpDfun θ v) (g := fun y : Euc 2 => ζ (σ, x - planeι y)) (v := v) J1 J2 J3
    (fun z _ => ibp_differentiableAt_Dfun θ v z) (fun z _ => hgd z)
  have E1 : ∫ y : Euc 2, ibpDfun θ v y • fderiv ℝ (fun z : Euc 2 => ζ (σ, x - planeι z)) y v =
      -∫ y : Euc 2, ibpDfun θ v y • ibpPdW ζ w (σ, x - planeι y) := by
    rw [← integral_neg]
    congr 1
    funext y
    rw [ibp_shift_fderiv hζd σ x y v, smul_neg]
    rfl
  have E2 : ∫ y : Euc 2, fderiv ℝ (ibpDfun θ v) y v • ζ (σ, x - planeι y) =
      ∫ y : Euc 2, ibpA0 θ v y • ζ (σ, x - planeι y) := by
    congr 1
    funext y
    rw [ibp_fderiv_Dfun hθ y v hv]
  rw [E1, E2] at S1
  exact ⟨I1, I2, (neg_inj.mp S1).symm.trans hstep2⟩

/-! ### 3. Commutation of `η = x.2` with `planeHeat θ` and heat-kernel Laplacian identity -/

/-- Commutation of `x.2` (`η`) with `B0224.planeHeat θ` for `0 < θ` and any smooth profile `ζ`
with bounded `ζ`, `pdEta ζ`, and `etaMul ζ`:
`x.2 • planeHeat θ (fun z => ζ (σ, z)) x =
  planeHeat θ (fun z => etaMul ζ (σ, z)) x - (2 * θ) • planeHeat θ (fun z => pdEta ζ (σ, z)) x`. -/
theorem etaMul_planeHeat_of_bdd {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) {ζ : Profile → MeridC}
    (hζs : ContDiff ℝ ∞ ζ)
    (hB0 : ∃ M0 : ℝ, ∀ p, ‖ζ p‖ ≤ M0)
    (hB1 : ∃ M1 : ℝ, ∀ p, ‖pdEta ζ p‖ ≤ M1)
    (hB2 : ∃ M2 : ℝ, ∀ p, ‖etaMul ζ p‖ ≤ M2)
    (x : ℝ × ℝ) :
    (x.2 : ℝ) • B0224.planeHeat θ (fun z => ζ (σ, z)) x =
      B0224.planeHeat θ (fun z => etaMul ζ (σ, z)) x -
        (2 * θ : ℝ) • B0224.planeHeat θ (fun z => pdEta ζ (σ, z)) x := by
  obtain ⟨M0, hM0⟩ := hB0
  obtain ⟨M1, hM1⟩ := hB1
  obtain ⟨M2, hM2⟩ := hB2
  set v : Euc 2 := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have hv : ‖v‖ = 1 := ibp_norm_single (1 : Fin 2)
  have hpl : planeι v = ((0 : ℝ), (1 : ℝ)) := by
    rw [UnforcedLeray.B0224.planeι_apply]
    simp [v]
  have hw_eq : ((0 : ℝ), planeι v) = ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    rw [hpl]
  have hpd_eq : ibpPdW ζ (0, planeι v) = pdEta ζ := by
    funext p
    simp only [ibpPdW, pdEta, hw_eq]
  have hM1' : ∀ p, ‖ibpPdW ζ (0, planeι v) p‖ ≤ M1 := by
    rw [hpd_eq]
    exact hM1
  obtain ⟨I1, I2, hibp⟩ := ibp_one_of_bdd hθ σ hζs hv hM0 hM1' x
  rw [hpd_eq] at I2 hibp
  have hpc : Continuous (fun y : Euc 2 => ((σ, x - planeι y) : Profile)) :=
    continuous_const.prodMk (continuous_const.sub B0224.continuous_planeι)
  have hGint : Integrable (gaussKernel 2 θ) :=
    UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ
  have I_eta : Integrable (fun y : Euc 2 =>
      gaussKernel 2 θ y • etaMul ζ (σ, x - planeι y)) :=
    ibp_integrable_smul_bdd hGint ((contDiff_etaMul hζs).continuous.comp hpc) (fun y => hM2 _)
  have I1_smul : Integrable (fun y : Euc 2 =>
      (2 * θ : ℝ) • (ibpDfun θ v y • ζ (σ, x - planeι y))) := I1.smul (2 * θ : ℝ)
  rw [B0224.planeHeat_of_pos hθ, B0224.planeHeat_of_pos hθ, B0224.planeHeat_of_pos hθ]
  rw [← hibp, ← integral_smul (x.2 : ℝ), ← integral_smul (2 * θ : ℝ),
    ← integral_sub I_eta I1_smul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  have hy1 : inner ℝ y v = y 1 := ibp_inner_single y 1
  have hθ_ne : 2 * θ ≠ 0 := by positivity
  have hscalar : (2 * θ) * ibpDfun θ v y = -(y 1 * gaussKernel 2 θ y) := by
    unfold ibpDfun
    rw [hy1]
    field_simp
  have hx2 : (x - planeι y).2 = x.2 - y 1 := rfl
  rw [etaMul, hx2, smul_comm (x.2 : ℝ) (gaussKernel 2 θ y),
    smul_smul (2 * θ : ℝ) (ibpDfun θ v y), hscalar,
    sub_smul (x.2 : ℝ) (y 1 : ℝ), smul_sub, neg_smul, sub_neg_eq_add,
    mul_smul (y 1) (gaussKernel 2 θ y), smul_comm (y 1) (gaussKernel 2 θ y)]
  abel

/-- Planar Gaussian heat equation `∫ y, gaussDt 2 θ y • ζ(σ, x - planeι y) =
planeHeat θ (laplaceQEta ζ (σ, ·)) x` for any smooth profile `ζ` with bounded derivatives up to
order 2 in `(q, η)`. -/
theorem gaussDt_lap_of_bdd {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) {ζ : Profile → MeridC}
    (hζs : ContDiff ℝ ∞ ζ)
    (hB0 : ∃ M0 : ℝ, ∀ p, ‖ζ p‖ ≤ M0)
    (hBQ1 : ∃ MQ1 : ℝ, ∀ p, ‖pdQ ζ p‖ ≤ MQ1)
    (hBQ2 : ∃ MQ2 : ℝ, ∀ p, ‖pdQ (pdQ ζ) p‖ ≤ MQ2)
    (hBE1 : ∃ ME1 : ℝ, ∀ p, ‖pdEta ζ p‖ ≤ ME1)
    (hBE2 : ∃ ME2 : ℝ, ∀ p, ‖pdEta (pdEta ζ) p‖ ≤ ME2)
    (x : ℝ × ℝ) :
    ∫ y : Euc 2, gaussDt 2 θ y • ζ (σ, x - planeι y) =
      B0224.planeHeat θ (fun z => laplaceQEta ζ (σ, z)) x := by
  obtain ⟨M0, hM0⟩ := hB0
  obtain ⟨MQ1, hMQ1⟩ := hBQ1
  obtain ⟨MQ2, hMQ2⟩ := hBQ2
  obtain ⟨ME1, hME1⟩ := hBE1
  obtain ⟨ME2, hME2⟩ := hBE2
  set v0 : Euc 2 := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  set v1 : Euc 2 := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have hv0 : ‖v0‖ = 1 := ibp_norm_single (0 : Fin 2)
  have hv1 : ‖v1‖ = 1 := ibp_norm_single (1 : Fin 2)
  have hpl0 : planeι v0 = ((1 : ℝ), (0 : ℝ)) := by
    rw [UnforcedLeray.B0224.planeι_apply]
    simp [v0]
  have hpl1 : planeι v1 = ((0 : ℝ), (1 : ℝ)) := by
    rw [UnforcedLeray.B0224.planeι_apply]
    simp [v1]
  have hw0 : ((0 : ℝ), planeι v0) = ((0 : ℝ), (1 : ℝ), (0 : ℝ)) := by
    rw [hpl0]
  have hw1 : ((0 : ℝ), planeι v1) = ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    rw [hpl1]
  have hpd0 : ibpPdW ζ (0, planeι v0) = pdQ ζ := by
    funext p; simp only [ibpPdW, pdQ, hw0]
  have hpd00 : ibpPdW (ibpPdW ζ (0, planeι v0)) (0, planeι v0) = pdQ (pdQ ζ) := by
    rw [hpd0]; funext p; simp only [ibpPdW, pdQ, hw0]
  have hpd1 : ibpPdW ζ (0, planeι v1) = pdEta ζ := by
    funext p; simp only [ibpPdW, pdEta, hw1]
  have hpd11 : ibpPdW (ibpPdW ζ (0, planeι v1)) (0, planeι v1) = pdEta (pdEta ζ) := by
    rw [hpd1]; funext p; simp only [ibpPdW, pdEta, hw1]
  obtain ⟨i0, j0, e0⟩ := ibp_two_of_bdd hθ σ hζs hv0 hM0
    (by rw [hpd0]; exact hMQ1) (by rw [hpd00]; exact hMQ2) x
  obtain ⟨i1, j1, e1⟩ := ibp_two_of_bdd hθ σ hζs hv1 hM0
    (by rw [hpd1]; exact hME1) (by rw [hpd11]; exact hME2) x
  rw [hpd00] at j0 e0
  rw [hpd11] at j1 e1
  have hA0_0 : ∀ y : Euc 2, ibpA0 θ v0 y =
      ((y 0) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * gaussKernel 2 θ y := by
    intro y
    unfold ibpA0
    rw [ibp_inner_single y 0]
  have hA0_1 : ∀ y : Euc 2, ibpA0 θ v1 y =
      ((y 1) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * gaussKernel 2 θ y := by
    intro y
    unfold ibpA0
    rw [ibp_inner_single y 1]
  have hL : (fun y : Euc 2 => gaussDt 2 θ y • ζ (σ, x - planeι y)) =
      fun y => ibpA0 θ v0 y • ζ (σ, x - planeι y) + ibpA0 θ v1 y • ζ (σ, x - planeι y) := by
    funext y
    rw [gaussDt_two_eq_sum θ y, ← hA0_0 y, ← hA0_1 y, add_smul]
  have hR : B0224.planeHeat θ (fun z => laplaceQEta ζ (σ, z)) x =
      ∫ y : Euc 2, (gaussKernel 2 θ y • pdQ (pdQ ζ) (σ, x - planeι y) +
        gaussKernel 2 θ y • pdEta (pdEta ζ) (σ, x - planeι y)) := by
    rw [B0224.planeHeat_of_pos hθ]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [laplaceQEta, smul_add]
  rw [hL, hR, integral_add i0 i1, integral_add j0 j1, e0, e1]

/-! ### 4. Commutation of `etaMul` with `flatAdjointSlice` and `causalAdjointRep` -/

theorem thetaWeight_mul (k l : ℕ) (t : ℝ) :
    thetaWeight k t * thetaWeight l t = thetaWeight (k + l) t := by
  simp only [thetaWeight, pow_add, Complex.ofReal_mul]

theorem stronglyMeasurable_flatAdjointSlice (ν : ℝ) (μ : ℂ) {w : Profile → MeridC}
    (hw : StronglyMeasurable w) (p : Profile) :
    StronglyMeasurable (fun t : ℝ => flatAdjointSlice ν μ w t p) := by
  refine (Continuous.stronglyMeasurable (by fun_prop :
    Continuous fun t : ℝ => Complex.exp (-((starRingEnd ℂ μ + (1 / 2 : ℂ)) * (t : ℂ))))).smul ?_
  have hite : (fun t : ℝ => B0224.planeHeat (ν * p.1 * (Real.exp t - 1))
      (fun y => w (Real.exp t * p.1, y)) p.2) =
      fun t : ℝ => if 0 < ν * p.1 * (Real.exp t - 1) then
        ∫ y : Euc 2, gaussKernel 2 (ν * p.1 * (Real.exp t - 1)) y •
          w (Real.exp t * p.1, p.2 - planeι y)
      else w (Real.exp t * p.1, p.2) := by
    funext t
    by_cases h : 0 < ν * p.1 * (Real.exp t - 1)
    · simp only [B0224.planeHeat_of_pos h, h, ↓reduceIte]
    · simp only [B0224.planeHeat_of_nonpos (not_lt.1 h), h, ↓reduceIte]
  rw [hite]
  have hθ : Measurable (fun t : ℝ => ν * p.1 * (Real.exp t - 1)) := by fun_prop
  have ha : Measurable (fun t : ℝ => Real.exp t * p.1) := by fun_prop
  refine StronglyMeasurable.ite (measurableSet_lt measurable_const hθ) ?_ ?_
  · refine StronglyMeasurable.integral_prod_right' (f := fun q : ℝ × Euc 2 =>
      gaussKernel 2 (ν * p.1 * (Real.exp q.1 - 1)) q.2 •
        w (Real.exp q.1 * p.1, p.2 - planeι q.2)) ?_
    refine (B0224.measurable_gaussKernel_two.comp ((hθ.comp measurable_fst).prodMk
      measurable_snd)).stronglyMeasurable.smul ?_
    exact hw.comp_measurable
      ((ha.comp measurable_fst).prodMk
        (measurable_const.sub (B0224.measurable_planeι.comp measurable_snd)))
  · exact hw.comp_measurable (ha.prodMk measurable_const)

theorem norm_planeHeat_le (θ : ℝ) {u : ℝ × ℝ → MeridC} {M : ℝ} (hu : ∀ z, ‖u z‖ ≤ M)
    (x : ℝ × ℝ) :
    ‖B0224.planeHeat θ u x‖ ≤ max M 0 := by
  by_cases hθ : 0 < θ
  · rw [B0224.planeHeat_of_pos hθ]
    have hGint : Integrable (gaussKernel 2 θ) :=
      UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ
    refine (norm_integral_le_of_norm_le (hGint.mul_const (max M 0))
      (Eventually.of_forall fun y => ?_)).trans ?_
    · rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)]
      exact mul_le_mul_of_nonneg_left ((hu _).trans (le_max_left M 0))
        (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)
    · rw [integral_mul_const, UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) hθ, one_mul]
  · rw [B0224.planeHeat_of_nonpos (not_lt.1 hθ)]
    exact (hu x).trans (le_max_left M 0)

theorem norm_flatAdjointSlice_le (ν : ℝ) (μ : ℂ) {w : Profile → MeridC} {M : ℝ}
    (hw : ∀ q, ‖w q‖ ≤ M) (t : ℝ) (p : Profile) :
    ‖flatAdjointSlice ν μ w t p‖ ≤ max M 0 * Real.exp (-(μ.re + 1 / 2) * t) := by
  rw [flatAdjointSlice, norm_smul, Infra.ExpSemigroup.norm_cexp_neg_mul]
  have hre : (starRingEnd ℂ μ + (1 / 2 : ℂ)).re = μ.re + 1 / 2 := by
    simp [Complex.add_re, Complex.conj_re]
  rw [hre, neg_mul, mul_comm (Real.exp _)]
  exact mul_le_mul_of_nonneg_right (norm_planeHeat_le _ (fun y => hw _) p.2) (Real.exp_pos _).le

theorem integrableOn_thetaWeight_flatAdjointSlice (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    (k : ℕ) {w : Profile → MeridC} (hw_cont : Continuous w) (hw_bdd : ∃ M : ℝ, ∀ q, ‖w q‖ ≤ M)
    (p : Profile) :
    IntegrableOn (fun t : ℝ => thetaWeight k t • flatAdjointSlice ν μ w t p) (Ioi 0) volume := by
  obtain ⟨M, hM⟩ := hw_bdd
  have hμ2 : 0 < μ.re + 1 / 2 := by linarith
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hμ2).const_mul (max M 0)) ?_ ?_
  · exact ((continuous_thetaWeight k).stronglyMeasurable.smul
      (stronglyMeasurable_flatAdjointSlice ν μ hw_cont.stronglyMeasurable p)).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    rw [norm_smul]
    calc ‖thetaWeight k t‖ * ‖flatAdjointSlice ν μ w t p‖
        ≤ 1 * (max M 0 * Real.exp (-(μ.re + 1 / 2) * t)) :=
          mul_le_mul (norm_thetaWeight_le k t) (norm_flatAdjointSlice_le ν μ hM t p)
            (norm_nonneg _) zero_le_one
      _ = max M 0 * Real.exp (-(μ.re + 1 / 2) * t) := one_mul _

theorem bdd_nuSMul_of_support_s {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (l : ℕ) {w : Profile → MeridC}
    (hw_supp : ∀ q : Profile, q.1 < σ ∨ H1 < q.1 → w q = 0)
    (hw_bdd : ∃ M : ℝ, ∀ q, ‖w q‖ ≤ M) :
    ∃ M' : ℝ, ∀ q, ‖nuSMul ν l w q‖ ≤ M' := by
  obtain ⟨M, hM⟩ := hw_bdd
  have hH1 : 0 < H1 := hσ.trans_le hσH1
  refine ⟨(ν * H1) ^ l * max M 0, fun q => ?_⟩
  refine (norm_nuSMul_le_of_support_s hν hσ l hw_supp q).trans ?_
  exact mul_le_mul_of_nonneg_left ((hM q).trans (le_max_left M 0)) (by positivity)

/-- Commutation of `etaMul` (`p.2.2 • ·`) with `thetaWeight k t • flatAdjointSlice ν μ w t`
at fixed `t > 0` and `p.1 > 0`. -/
theorem etaMul_thetaWeight_flatAdjointSlice {ν : ℝ} (hν : 0 < ν) (μ : ℂ) (k : ℕ)
    {w : Profile → MeridC} (hws : ContDiff ℝ ∞ w)
    (hB0 : ∃ M0 : ℝ, ∀ q, ‖w q‖ ≤ M0)
    (hB1 : ∃ M1 : ℝ, ∀ q, ‖pdEta w q‖ ≤ M1)
    (hB2 : ∃ M2 : ℝ, ∀ q, ‖etaMul w q‖ ≤ M2)
    {t : ℝ} (ht : 0 < t) {p : Profile} (hp : 0 < p.1) :
    (p.2.2 : ℝ) • (thetaWeight k t • flatAdjointSlice ν μ w t p) =
      thetaWeight k t • flatAdjointSlice ν μ (etaMul w) t p -
        (2 : ℝ) • (thetaWeight (k + 1) t • flatAdjointSlice ν μ (nuSMul ν 1 (pdEta w)) t p) := by
  have hexp : 1 < Real.exp t := Real.one_lt_exp_iff.2 ht
  have hsub : 0 < Real.exp t - 1 := sub_pos.2 hexp
  have hθ : 0 < ν * p.1 * (Real.exp t - 1) := mul_pos (mul_pos hν hp) hsub
  have heta := etaMul_planeHeat_of_bdd hθ (Real.exp t * p.1) hws hB0 hB1 hB2 p.2
  have hslice : (p.2.2 : ℝ) • flatAdjointSlice ν μ w t p =
      flatAdjointSlice ν μ (etaMul w) t p -
        (2 : ℝ) • (thetaWeight 1 t • flatAdjointSlice ν μ (nuSMul ν 1 (pdEta w)) t p) := by
    simp only [flatAdjointSlice]
    rw [smul_comm (p.2.2 : ℝ) (Complex.exp _), heta, smul_sub]
    congr 1
    have hpow := heatTimeAdj_pow_smul_flatAdjointSlice ν μ 1 (pdEta w) ht p
    simp only [pow_one, flatAdjointSlice] at hpow
    rw [mul_smul (2 : ℝ) (ν * p.1 * (Real.exp t - 1)),
      smul_comm (Complex.exp _) (2 : ℝ)]
    congr 1
    rw [smul_comm (Complex.exp _) (ν * p.1 * (Real.exp t - 1)),
      RCLike.real_smul_eq_coe_smul (K := ℂ) (ν * p.1 * (Real.exp t - 1))]
    exact hpow
  rw [smul_comm (p.2.2 : ℝ) (thetaWeight k t), hslice, smul_sub,
    smul_comm (thetaWeight k t) (2 : ℝ), ← mul_smul (thetaWeight k t) (thetaWeight 1 t),
    thetaWeight_mul k 1 t]

/-- Commutation of `etaMul` with `causalAdjointRep ν μ (thetaWeight k)` on `{p | 0 < p.1}`:
`etaMul (causalAdjointRep ν μ (thetaWeight k) w) p =
  causalAdjointRep ν μ (thetaWeight k) (etaMul w) p -
    (2 : ℝ) • causalAdjointRep ν μ (thetaWeight (k + 1)) (nuSMul ν 1 (pdEta w)) p`. -/
theorem etaMul_causalAdjointRep {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (k : ℕ)
    {w : Profile → MeridC} (hws : ContDiff ℝ ∞ w)
    (hw_supp : ∀ q : Profile, q.1 < σ ∨ H1 < q.1 → w q = 0)
    (hB0 : ∃ M0 : ℝ, ∀ q, ‖w q‖ ≤ M0)
    (hB1 : ∃ M1 : ℝ, ∀ q, ‖pdEta w q‖ ≤ M1)
    (hB2 : ∃ M2 : ℝ, ∀ q, ‖etaMul w q‖ ≤ M2)
    {p : Profile} (hp : 0 < p.1) :
    etaMul (causalAdjointRep ν μ (thetaWeight k) w) p =
      causalAdjointRep ν μ (thetaWeight k) (etaMul w) p -
        (2 : ℝ) • causalAdjointRep ν μ (thetaWeight (k + 1)) (nuSMul ν 1 (pdEta w)) p := by
  simp only [etaMul, causalAdjointRep, hp, ↓reduceIte]
  rw [← integral_smul (p.2.2 : ℝ), ← integral_smul (2 : ℝ)]
  have hint_eta : IntegrableOn
      (fun t : ℝ => thetaWeight k t • flatAdjointSlice ν μ (etaMul w) t p) (Ioi 0) volume :=
    integrableOn_thetaWeight_flatAdjointSlice ν hμ k (contDiff_etaMul hws).continuous hB2 p
  have hint_pd : IntegrableOn
      (fun t : ℝ => (2 : ℝ) •
        (thetaWeight (k + 1) t • flatAdjointSlice ν μ (nuSMul ν 1 (pdEta w)) t p))
      (Ioi 0) volume :=
    (integrableOn_thetaWeight_flatAdjointSlice ν hμ (k + 1)
      (contDiff_nuSMul ν 1 (contDiff_pdEta hws)).continuous
      (bdd_nuSMul_of_support_s hν hσ hσH1 1 (support_s_pdEta hw_supp) hB1) p).smul (2 : ℝ)
  rw [← integral_sub hint_eta hint_pd]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  exact etaMul_thetaWeight_flatAdjointSlice hν μ k hws hB0 hB1 hB2 ht hp

end FlatAdjointElemAux

end UnforcedLeray.Short.PartIIa
