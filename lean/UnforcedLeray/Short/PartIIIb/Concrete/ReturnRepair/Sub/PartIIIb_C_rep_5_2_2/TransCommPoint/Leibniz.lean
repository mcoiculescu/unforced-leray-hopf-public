import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Leibniz.Cut

/-!
# `tcLeibniz`: the algebraic expansion of `[D_{μ+1}, 𝒞_y]Z` (`TCLeibniz`)

Source `the November 2 reference manuscript` 4176-4214, 3700-3712.
With `𝒞_yZ = c(ϱ) Z + F(ϱ) ψ_Z` (`Leibniz/Cut.lean`), the Leibniz rules for `∂_τ`, `y·∇`, `Δ`
(`Leibniz/Prod.lean`, with `∇(g∘ϱ) = g'(ϱ)e_r`, `Δ(g∘ϱ) = g'' + g'/ϱ` of `Leibniz/Rho.lean`),
linearity of the outward primitive on integrable data, and the four identities `TCTime`, `TCGrad`,
`TCLap`, `TCRad` at the point give the explicit commutator `tcComm`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Linearity of the outward primitive on the four integrable pieces of `D_{μ'}Z`. -/
theorem tcle_outPrim_lin (ν μ' : ℝ) (Z : ℝ → Space → Space) (τ r z : ℝ)
    (i1 : IntegrableOn (fun ρ : ℝ => ρ * Z τ !₂[ρ, 0, z] 2) (Ioi r))
    (i2 : IntegrableOn (fun ρ : ℝ => ρ * (deriv (fun s => Z s !₂[ρ, 0, z]) τ) 2) (Ioi r))
    (i3 : IntegrableOn (fun ρ : ℝ => ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, z] !₂[ρ, 0, z]) 2) (Ioi r))
    (i4 : IntegrableOn (fun ρ : ℝ => ρ * (physLap (Z τ) !₂[ρ, 0, z]) 2) (Ioi r)) :
    outPrim (physDmu ν μ' Z) τ r z =
      outPrim (fun t y' => deriv (fun s => Z s y') t) τ r z -
        (1 / 2 : ℝ) * outPrim (fun t y' => fderiv ℝ (Z t) y' y') τ r z -
          ν * outPrim (fun t y' => physLap (Z t) y') τ r z + (μ' - 1 / 2) * outPrim Z τ r z := by
  unfold outPrim
  have e : (fun ρ : ℝ => ρ * (physDmu ν μ' Z τ !₂[ρ, 0, z]) 2) =
      fun ρ => ((ρ * (deriv (fun s => Z s !₂[ρ, 0, z]) τ) 2 -
        (1 / 2 : ℝ) * (ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, z] !₂[ρ, 0, z]) 2)) -
          ν * (ρ * (physLap (Z τ) !₂[ρ, 0, z]) 2)) + (μ' - 1 / 2) * (ρ * Z τ !₂[ρ, 0, z] 2) := by
    funext ρ
    simp only [physDmu, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have j3 := i3.const_mul (1 / 2 : ℝ)
  have j4 := i4.const_mul ν
  have j1 := i1.const_mul (μ' - 1 / 2)
  have k23 : Integrable (fun ρ : ℝ => ρ * (deriv (fun s => Z s !₂[ρ, 0, z]) τ) 2 -
      (1 / 2 : ℝ) * (ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, z] !₂[ρ, 0, z]) 2))
      (volume.restrict (Ioi r)) := i2.sub j3
  have k234 : Integrable (fun ρ : ℝ => (ρ * (deriv (fun s => Z s !₂[ρ, 0, z]) τ) 2 -
      (1 / 2 : ℝ) * (ρ * (fderiv ℝ (Z τ) !₂[ρ, 0, z] !₂[ρ, 0, z]) 2)) -
        ν * (ρ * (physLap (Z τ) !₂[ρ, 0, z]) 2)) (volume.restrict (Ioi r)) := k23.sub j4
  rw [e, integral_add k234 j1, integral_sub k23 j4, integral_sub i2 j3,
    integral_const_mul, integral_const_mul, integral_const_mul]
  beta_reduce
  ring

theorem tcLeibniz : TCLeibniz := by
  intro ν μ R χy hχ hν hR Z τ y hρ hZc hZt hψc hψt i1 i2 i3 i4 hT hG hL hRad μ'
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
  -- time derivative
  have ht : deriv (fun t => wardStreamCut ν R χy Z t y) τ =
      tcC0 ν R χy (ϱ y) • deriv (fun t => Z t y) τ +
        tcF0 ν R χy (ϱ y) • deriv (fun t => psiFld Z t y) τ := by
    have : (fun t => wardStreamCut ν R χy Z t y) = fun t =>
        tcC0 ν R χy (ϱ y) • Z t y + tcF0 ν R χy (ϱ y) • psiFld Z t y :=
      funext fun t => tcle_wsc_eq ν R χy Z t y
    rw [this]
    exact ((hZt.hasDerivAt.const_smul (tcC0 ν R χy (ϱ y))).add
      (hψt.hasDerivAt.const_smul (tcF0 ν R χy (ϱ y)))).deriv
  -- dilation derivative
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
  -- Laplacian
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
  -- the primitive of `D Z`
  have hP := tcle_outPrim_lin ν μ' Z τ (ϱ y) (y 2) i1 i2 i3 i4
  -- the identities at the point, in vector form
  have eψ : psiFld Z τ y = outPrim Z τ (ϱ y) (y 2) • (coordinateVector 2 : Space) := rfl
  have eT : deriv (fun t => psiFld Z t y) τ =
      outPrim (fun t y' => deriv (fun s => Z s y') t) τ (ϱ y) (y 2) • (coordinateVector 2 : Space) :=
    hT
  have eG : fderiv ℝ (psiFld Z τ) y y =
      outPrim (fun t y' => fderiv ℝ (Z t) y' y') τ (ϱ y) (y 2) • (coordinateVector 2 : Space) +
        (2 : ℝ) • (outPrim Z τ (ϱ y) (y 2) • (coordinateVector 2 : Space)) := by
    have := hG
    change outPrim (fun t y' => fderiv ℝ (Z t) y' y') τ (ϱ y) (y 2) • (coordinateVector 2 : Space) = _ at this
    rw [this]
    rw [eψ]
    abel
  have eL : physLap (psiFld Z τ) y =
      outPrim (fun t y' => physLap (Z t) y') τ (ϱ y) (y 2) • (coordinateVector 2 : Space) +
        (2 * Z τ y 2) • (coordinateVector 2 : Space) := by
    have := hL
    change outPrim (fun t y' => physLap (Z t) y') τ (ϱ y) (y 2) • (coordinateVector 2 : Space) = _ at this
    rw [this]
    abel
  have eR : fderiv ℝ (psiFld Z τ) y (radialUnit y) = (ϱ y * Z τ y 2) • (coordinateVector 2 : Space) :=
    hRad
  have hrhs : wardStreamCut ν R χy (physDmu ν μ' Z) τ y =
      tcC0 ν R χy (ϱ y) • physDmu ν μ' Z τ y +
        tcF0 ν R χy (ϱ y) • ((outPrim (physDmu ν μ' Z) τ (ϱ y) (y 2)) •
          (coordinateVector 2 : Space)) := tcle_wsc_eq ν R χy (physDmu ν μ' Z) τ y
  have hW0 : wardStreamCut ν R χy Z τ y = tcC0 ν R χy (ϱ y) • Z τ y +
      tcF0 ν R χy (ϱ y) • psiFld Z τ y := tcle_wsc_eq ν R χy Z τ y
  have hDW : physDmu ν μ' (wardStreamCut ν R χy Z) τ y =
      deriv (fun t => wardStreamCut ν R χy Z t y) τ -
        (1 / 2 : ℝ) • fderiv ℝ (wardStreamCut ν R χy Z τ) y y -
          ν • physLap (wardStreamCut ν R χy Z τ) y + (μ' - 1 / 2) • wardStreamCut ν R χy Z τ y :=
    rfl
  have hDZ : physDmu ν μ' Z τ y = deriv (fun t => Z t y) τ - (1 / 2 : ℝ) • fderiv ℝ (Z τ) y y -
      ν • physLap (Z τ) y + (μ' - 1 / 2) • Z τ y := rfl
  rw [hDW, hrhs, ht, hD, hLap, hW0, hDZ, hP]
  rw [eT, eG, eL, eR, eψ]
  unfold tcComm tcA1 tcA2 tcB1 tcB2
  module

end UnforcedLeray.Short.PartIIIb.Concrete
