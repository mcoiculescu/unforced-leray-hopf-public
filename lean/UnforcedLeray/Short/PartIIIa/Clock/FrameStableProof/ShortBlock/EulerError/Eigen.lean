import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_3
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound.SubBound.SectorLimit
import UnforcedLeray.Short.PartI.Tasks.SeedModeRegularityProof
import UnforcedLeray.Short.PartI.Tasks.AdjointEigenvectorExplicit
import UnforcedLeray.Short.PartI.Tasks.SeedFunctional.GreenTwoSmooth
import UnforcedLeray.Short.PartI.Tasks.BiotSavartPerpGrad.Curl
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_1
import UnforcedLeray.Lib.PlanarSectorsB.BiotSavartSector
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.GradPerSum.PolarJet
import UnforcedLeray.Units.B0169

/-!
# Pointwise planar eigen equation of the seed modes (helper for `PartIII-a:T21/c3/3/3`)

Source of record: `the November 2 reference manuscript` (SP), lines 593-610,
662-670, 2866-2870.

For the Part I seed triple `(lam, h, ℓ)` realizing `κ` (`κ.e 0 = h(|y|)e^{2iϑ}`,
`κ.e 1 = conj (κ.e 0)`), the eigen equation `L₀h = lam h` gives the radial identity
`(Ω - i lam/2) h = k Δ₂⁻¹h` on `(0,∞)` (`radial_eigen`). The transport is
`v₀·∇e₀ = Ω ∂_ϑ e₀ = 2iΩ e₀` (`trans_seed`), and with `∇ω₀(y) = k(|y|) y` (`pd_omega0`) the
interaction is `(K e₀)·∇ω₀ = k y·(K e₀) = -2ik Δ₂⁻¹h e^{2iϑ}`
(`PlanarDualSub.dot_biotSavart_ofProfile_lim`). Hence `movLPlanar e₀ = lam e₀`; the second
mode follows by conjugation (`movLPlanar_conj`). This proves `SeedPlanarPointwiseEigen κ`
for every `κ` (`seedPlanarPointwiseEigen`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa

namespace EulerErrorEig

open UnforcedLeray UnforcedLeray.Planar.NUE

/-! ## 1. The Gaussian vortex: `ω₀ = curl v₀`, `∇ω₀ = k(|x|) x` -/

theorem gauss0_eq_radialOmega (y : ℝ × ℝ) :
    Train.gauss0 y = GaussianVortex.radialOmega ‖planeToC y‖ := by
  rw [Train.gauss0, GaussianVortex.radialOmega, OscillatorForceSub.norm_planeToC_sq]
  congr 1; ring

theorem curl_v0_eq : Cyl.curl Train.v0 = GaussianVortex.vorticity := by
  funext z
  have hg : ∀ w : ℝ × ℝ, Train.gauss0 w = GaussianVortex.planarGaussian w := by
    intro w
    simp only [Train.gauss0, GaussianVortex.planarGaussian, GaussianVortex.radiusSq]
    congr 1; ring
  have hv1 : (fun q : ℝ => Train.v0 (q, z.2) 1) =
      fun q => GaussianVortex.planarGaussian (q, z.2) * q := by
    funext q; simp [Train.v0, hg]
  have hv0 : (fun η : ℝ => Train.v0 (z.1, η) 0) =
      fun η => GaussianVortex.planarGaussian (z.1, η) * (-η) := by
    funext η; simp [Train.v0, hg]
  have d1 : HasDerivAt (fun q : ℝ => GaussianVortex.planarGaussian (q, z.2) * q)
      (-z.1 / 2 * GaussianVortex.planarGaussian (z.1, z.2) * z.1 +
        GaussianVortex.planarGaussian (z.1, z.2) * 1) z.1 :=
    (GaussianVortex.hasDerivAt_planarGaussian_x z.1 z.2).mul (hasDerivAt_id' z.1)
  have d2 : HasDerivAt (fun η : ℝ => GaussianVortex.planarGaussian (z.1, η) * (-η))
      (-z.2 / 2 * GaussianVortex.planarGaussian (z.1, z.2) * (-z.2) +
        GaussianVortex.planarGaussian (z.1, z.2) * (-1)) z.2 :=
    (GaussianVortex.hasDerivAt_planarGaussian_y z.1 z.2).mul (hasDerivAt_id' z.2).neg
  simp only [Cyl.curl, Cyl.partialQ, Cyl.partialEta]
  rw [hv1, hv0, d1.deriv, d2.deriv]
  simp only [GaussianVortex.vorticity, GaussianVortex.radiusSq, Prod.mk.eta]
  ring

/-- `ω₀ = curl v₀`. -/
theorem omega0_eq_curl_v0 : Train.omega0 = Cyl.curl Train.v0 := by
  rw [curl_v0_eq, B0169.vorticity_eq_omega0]

/-- `∂_l ω₀(x) = k(|x|) x_l`. -/
theorem pd_omega0 (l : Fin 2) (x : ℝ × ℝ) :
    B0579.pd l Train.omega0 x =
      GaussianVortex.radialK ‖planeToC x‖ * (if l = 0 then x.1 else x.2) := by
  rw [← B0169.vorticity_eq_omega0]
  have hd : DifferentiableAt ℝ GaussianVortex.vorticity x :=
    (GaussianVortex.contDiff_vorticity.differentiable (by simp)) x
  have hr : GaussianVortex.radialK ‖planeToC x‖ =
      (GaussianVortex.radiusSq x / 4 - 2) * GaussianVortex.planarGaussian x := by
    rw [GaussianVortex.radialK, GaussianVortex.radialOmega, OscillatorForceSub.norm_planeToC_sq]
    simp only [GaussianVortex.planarGaussian, GaussianVortex.radiusSq]
  fin_cases l
  · simp only [B0579.pd, B0579.dir, Fin.zero_eta, Matrix.cons_val_zero, ite_true]
    rw [← GaussianVortex.partialX_eq_fderiv hd, GaussianVortex.partialX_vorticity, hr]
    ring
  · simp only [B0579.pd, B0579.dir, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      one_ne_zero, ite_false]
    rw [← GaussianVortex.partialY_eq_fderiv hd, GaussianVortex.partialY_vorticity, hr]
    ring

/-! ## 2. The seed facts for the given triple -/

theorem seedPlanar_eq_of_eqOn {f g : ℝ → ℂ} (hfg : EqOn f g (Ioi 0)) :
    PartI.seedPlanar f = PartI.seedPlanar g := by
  funext z
  unfold PartI.seedPlanar Planar.NUE.Ang.ofProfile Planar.NUE.Ang.angPhase
  by_cases hz : z = 0
  · subst hz; simp
  · rw [hfg (norm_pos_iff.mpr hz)]

theorem seed_smooth_given {κ : PlanarFrameKernels} {lam : ℂ} {h : ℝ → ℂ}
    {hh : MemLp h 2 B0010.xGMeasure} {ℓ : B0010.XG →L[ℂ] ℂ}
    (hIS : PartI.IsSeedXG lam (hh.toLp h) ℓ)
    (he0 : ∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y)) :
    ContDiff ℝ ∞ (PartI.seedPlanar h) ∧ ContDiffOn ℝ ∞ h (Ioi 0) ∧
      ∃ C : ℝ, ∃ N : ℕ, ∀ y : ℂ,
        ‖PartI.seedPlanar h y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4) := by
  obtain ⟨_, _, h', hae', hsm', hder', _, _, _, _, _, _⟩ :=
    PartI.seedModeRegularity_proof lam h hh ℓ hIS
  have hcont_h' : ContinuousOn h' (Ioi 0) := by
    have hcd : ContinuousOn (fun r : ℝ => PartI.seedPlanar h' (r : ℂ)) (Ioi 0) :=
      (hsm'.continuous.comp Complex.continuous_ofReal).continuousOn
    exact hcd.congr (fun r hr => (seedPlanar_ofReal_eq h' r hr).symm)
  have hcont_h : ContinuousOn h (Ioi 0) := by
    have hce : ContinuousOn (fun r : ℝ => κ.e 0 (r, 0)) (Ioi 0) :=
      ((κ.e_cont 0).comp (continuous_id.prodMk continuous_const)).continuousOn
    refine hce.congr (fun r hr => ?_)
    have hpl : planeToC (r, 0) = (r : ℂ) := by
      apply Complex.ext <;> simp [planeToC]
    dsimp only
    rw [he0 (r, 0), hpl, seedPlanar_ofReal_eq h r hr]
  have heq_h'h : EqOn h' h (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hae' isOpen_Ioi hcont_h' hcont_h
  have hsp_eq : PartI.seedPlanar h = PartI.seedPlanar h' :=
    (seedPlanar_eq_of_eqOn heq_h'h).symm
  have hsm : ContDiff ℝ ∞ (PartI.seedPlanar h) := hsp_eq ▸ hsm'
  have hcd_h : ContDiffOn ℝ ∞ h (Ioi 0) := by
    have hcd : ContDiffOn ℝ ∞ (fun r : ℝ => PartI.seedPlanar h (r : ℂ)) (Ioi 0) :=
      (hsm.comp Complex.ofRealCLM.contDiff).contDiffOn.mono (subset_univ _)
    exact hcd.congr (fun r hr => (seedPlanar_ofReal_eq h r hr).symm)
  obtain ⟨C, N, hC⟩ := hder' 0
  refine ⟨hsm, hcd_h, C, N, fun y => ?_⟩
  rw [hsp_eq]
  have := hC y
  rwa [norm_iteratedFDeriv_zero] at this

/-- The radial eigen equation `(Ω - i lam/2) h = k Δ₂⁻¹h` on `(0,∞)`. -/
theorem radial_eigen {lam : ℂ} {h : ℝ → ℂ} {hh : MemLp h 2 B0010.xGMeasure}
    {ℓ : B0010.XG →L[ℂ] ℂ} (hI : PartI.IsSeedXG lam (hh.toLp h) ℓ)
    (hs : ContDiffOn ℝ ∞ h (Ioi 0)) (r : ℝ) (hr : 0 < r) :
    ((GaussianVortex.radialOmega r : ℂ) - Complex.I * lam / 2) * h r =
      (GaussianVortex.radialK r : ℂ) * Planar.greenN 2 h r := by
  set q : B0010.XG := hh.toLp h with hq
  have hGs := PartI.greenTwoSmooth_proof h hh hs
  have hΩ : Continuous (fun r : ℝ => (GaussianVortex.radialOmega r : ℂ)) :=
    Complex.continuous_ofReal.comp GaussianVortex.radialOmega_smooth.continuous
  have hK : Continuous (fun r : ℝ => (GaussianVortex.radialK r : ℂ)) :=
    Complex.continuous_ofReal.comp GaussianVortex.radialK_smooth.continuous
  have hqh : (⇑q) =ᵐ[volume.restrict (Ioi (0 : ℝ))] h :=
    B0012.restrict_ac.ae_le hh.coeFn_toLp
  have hgreen : ∀ r, Planar.greenN 2 (⇑q) r = Planar.greenN 2 h r :=
    PartI.adjEig_greenN_congr hqh
  have hae : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      ((GaussianVortex.radialOmega x : ℂ) - Complex.I * lam / 2) * h x =
        (GaussianVortex.radialK x : ℂ) * Planar.greenN 2 h x := by
    have h0 := B0012.restrict_ac.ae_le (PartI.adjEig_pointwise hI.eigen)
    filter_upwards [h0, hqh] with x hx hx'
    rw [← hx', ← hgreen x]
    exact hx
  have hcont : ContinuousOn
      (fun x : ℝ => ((GaussianVortex.radialOmega x : ℂ) - Complex.I * lam / 2) * h x) (Ioi 0) :=
    ((hΩ.sub continuous_const).continuousOn).mul hs.continuousOn
  have hcont2 : ContinuousOn
      (fun x : ℝ => (GaussianVortex.radialK x : ℂ) * Planar.greenN 2 h x) (Ioi 0) :=
    hK.continuousOn.mul hGs.continuousOn
  exact Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hcont hcont2 hr

/-! ## 3. The transport part `v₀·∇e₀ = 2iΩ e₀` -/

theorem trans_seed {h : ℝ → ℂ} (hsm : ContDiff ℝ ∞ (PartI.seedPlanar h)) (y : ℝ × ℝ) :
    ((Train.v0 y 0 : ℝ) : ℂ) * pdCx 0 (fun x => PartI.seedPlanar h (planeToC x)) y +
      ((Train.v0 y 1 : ℝ) : ℂ) * pdCx 1 (fun x => PartI.seedPlanar h (planeToC x)) y =
    (Train.gauss0 y : ℂ) * (Complex.I * 2 * PartI.seedPlanar h (planeToC y)) := by
  set Λc : ℂ → ℂ := PartI.seedPlanar h with hΛcdef
  have hdc : DifferentiableAt ℝ Λc (planeToC y) :=
    (hsm.differentiable (by simp)) _
  set L := fderiv ℝ Λc (planeToC y) with hLdef
  have hL : HasFDerivAt Λc L (planeToC y) := hdc.hasFDerivAt
  have hfun : (fun x => Λc (planeToC x)) = Λc ∘ GradPerSumLeaves.planeCLM := by
    funext x; simp [GradPerSumLeaves.planeCLM_apply]
  have hcomp : HasFDerivAt (fun x => Λc (planeToC x)) (L.comp GradPerSumLeaves.planeCLM) y := by
    rw [hfun]
    exact hL.comp y GradPerSumLeaves.planeCLM.hasFDerivAt
  have hpd0 : pdCx 0 (fun x => Λc (planeToC x)) y = L 1 := by
    rw [pdCx, hcomp.fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, GradPerSumLeaves.planeCLM_apply]
    congr 1
  have hpd1 : pdCx 1 (fun x => Λc (planeToC x)) y = L Complex.I := by
    rw [pdCx, hcomp.fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, GradPerSumLeaves.planeCLM_apply]
    congr 1
  have hrot := Planar.fderiv_sector_rot (n := 2) hL (fun θ => by
    simp only [hΛcdef, PartI.seedPlanar]
    rw [Planar.ofProfile_rot])
  have hIy : Complex.I * planeToC y = (-y.2) • (1 : ℂ) + y.1 • Complex.I := by
    apply Complex.ext <;> simp [planeToC]
  have hLI : L (Complex.I * planeToC y) = -y.2 * L 1 + y.1 * L Complex.I := by
    rw [hIy, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hv0 : Train.v0 y 0 = Train.gauss0 y * (-y.2) := by simp [Train.v0]
  have hv1 : Train.v0 y 1 = Train.gauss0 y * y.1 := by simp [Train.v0]
  rw [hpd0, hpd1, hv0, hv1]
  push_cast at hrot ⊢
  linear_combination (↑(Train.gauss0 y) : ℂ) * (hrot - hLI)

/-! ## 4. The eigen equation for the first mode -/

theorem planeToC_toPlane (z : ℂ) : planeToC (B0009.toPlane z) = z :=
  Complex.ext (by simp [planeToC, B0009.toPlane]) (by simp [planeToC, B0009.toPlane])

theorem eig_zero {lam : ℂ} {h : ℝ → ℂ}
    (hsm : ContDiff ℝ ∞ (PartI.seedPlanar h)) (hon : ContDiffOn ℝ ∞ h (Ioi 0))
    {C : ℝ} {N : ℕ}
    (hC : ∀ y : ℂ, ‖PartI.seedPlanar h y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4))
    (hrad : ∀ r : ℝ, 0 < r →
      ((GaussianVortex.radialOmega r : ℂ) - Complex.I * lam / 2) * h r =
        (GaussianVortex.radialK r : ℂ) * Planar.greenN 2 h r) (y : ℝ × ℝ) :
    movLPlanar (fun x => PartI.seedPlanar h (planeToC x)) y =
      lam * PartI.seedPlanar h (planeToC y) := by
  set A : ℝ := |C| * Real.exp (2 * (N : ℝ) ^ 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hqc : Continuous (Ang.ofProfile 2 h) := hsm.continuous
  have hqb : ∀ z, ‖Ang.ofProfile 2 h z‖ ≤ A * Real.exp (-(‖z‖ ^ 2) / 8) := fun z =>
    PartI.BiotSavartCurlAux.gauss_dominated z (hC z)
  have hK : ∀ z, ‖Ang.ofProfile 2 h z‖ ≤ A := by
    intro z
    refine (hqb z).trans ?_
    have h1 : Real.exp (-(‖z‖ ^ 2) / 8) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := sq_nonneg ‖z‖; linarith)
    exact mul_le_of_le_one_right hA0 h1
  have hint : Integrable (Ang.ofProfile 2 h) :=
    Integrable.mono' (PartI.BiotSavartCurlAux.integrable_exp_neg_sq_div_eight.const_mul A)
      hqc.aestronglyMeasurable (Eventually.of_forall hqb)
  have hi : IntegrableOn (fun ρ => ‖h ρ‖ * ρ) (Ioi 0) := by
    have hg := ((integrable_mul_exp_neg_mul_sq (b := 1 / 8) (by norm_num)).const_mul A).integrableOn
      (s := Ioi (0 : ℝ))
    refine Integrable.mono' hg ?_ ?_
    · exact (hon.continuousOn.norm.mul continuousOn_id).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      have hρ' : (0 : ℝ) < ρ := hρ
      have hb := hqb (ρ : ℂ)
      have hsp : Ang.ofProfile 2 h (ρ : ℂ) = h ρ := seedPlanar_ofReal_eq h ρ hρ'
      rw [hsp, Complex.norm_real, Real.norm_of_nonneg hρ'.le] at hb
      have hb' : ‖h ρ‖ ≤ A * Real.exp (-(1 / 8) * ρ ^ 2) := by
        refine hb.trans (le_of_eq ?_)
        congr 2; ring
      rw [norm_mul, norm_norm, Real.norm_of_nonneg hρ'.le]
      calc ‖h ρ‖ * ρ ≤ A * Real.exp (-(1 / 8) * ρ ^ 2) * ρ :=
            mul_le_mul_of_nonneg_right hb' hρ'.le
        _ = A * (ρ * Real.exp (-(1 / 8) * ρ ^ 2)) := by ring
  have hlim := PlanarDualSub.dot_biotSavart_ofProfile_lim (m := 2) (by norm_num) hon hqc hK
    hint hi (planeToC y)
  have hre' : (planeToC y).re = y.1 := rfl
  have him' : (planeToC y).im = y.2 := rfl
  rw [hre', him'] at hlim
  have hbs : (fun z => (fun x => PartI.seedPlanar h (planeToC x)) (B0009.toPlane z)) =
      Ang.ofProfile 2 h := by
    funext z
    simp only [planeToC_toPlane, PartI.seedPlanar]
  have htr := trans_seed hsm y
  unfold movLPlanar kerVelPlanarCx
  rw [hbs, htr, pd_omega0 0 y, pd_omega0 1 y]
  simp only [Fin.isValue, ite_true, one_ne_zero, ite_false]
  have hcomb : B0009.biotSavart (Ang.ofProfile 2 h) 0 (planeToC y) *
        (((GaussianVortex.radialK ‖planeToC y‖ * y.1 : ℝ)) : ℂ) +
      B0009.biotSavart (Ang.ofProfile 2 h) 1 (planeToC y) *
        (((GaussianVortex.radialK ‖planeToC y‖ * y.2 : ℝ)) : ℂ) =
      (GaussianVortex.radialK ‖planeToC y‖ : ℂ) *
        ((y.1 : ℂ) * B0009.biotSavart (Ang.ofProfile 2 h) 0 (planeToC y) +
          (y.2 : ℂ) * B0009.biotSavart (Ang.ofProfile 2 h) 1 (planeToC y)) := by
    push_cast; ring
  rw [hcomb, hlim]
  simp only [PartI.seedPlanar, Ang.ofProfile]
  rw [gauss0_eq_radialOmega]
  have hnat : Int.natAbs (2 : ℤ) = 2 := rfl
  rw [hnat]
  by_cases hy : planeToC y = 0
  · have hphase : Ang.angPhase 2 (planeToC y) = 0 := by rw [hy]; simp [Ang.angPhase]
    rw [hphase]; simp
  · have hr : 0 < ‖planeToC y‖ := norm_pos_iff.2 hy
    have hR := hrad ‖planeToC y‖ hr
    push_cast
    linear_combination (-(2 * Complex.I * Ang.angPhase 2 (planeToC y))) * hR +
      (-(lam * h ‖planeToC y‖ * Ang.angPhase 2 (planeToC y))) * Complex.I_sq

/-! ## 5. Conjugation and the second mode -/

theorem pdCx_conj {f : ℝ × ℝ → ℂ} (l : Fin 2) (y : ℝ × ℝ) :
    pdCx l (fun x => conj (f x)) y = conj (pdCx l f y) := by
  unfold pdCx
  have hfun : (fun x => conj (f x)) = fun x => star (f x) := rfl
  rw [hfun, fderiv_star]
  simp

theorem biotSavart_conj (g : ℂ → ℂ) (i : Fin 2) (Y : ℂ) :
    B0009.biotSavart (fun z => conj (g z)) i Y = conj (B0009.biotSavart g i Y) := by
  rw [B0009.biotSavart_apply, B0009.biotSavart_apply, ← integral_conj]
  congr 1
  funext z
  simp only [B0009.kernel, map_mul, Complex.conj_ofReal]

theorem movLPlanar_conj (f : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    movLPlanar (fun x => conj (f x)) y = conj (movLPlanar f y) := by
  unfold movLPlanar kerVelPlanarCx
  rw [pdCx_conj 0 y, pdCx_conj 1 y]
  have h0 : B0009.biotSavart (fun z => conj (f (B0009.toPlane z))) 0 (planeToC y) =
      conj (B0009.biotSavart (fun z => f (B0009.toPlane z)) 0 (planeToC y)) :=
    biotSavart_conj _ 0 _
  have h1 : B0009.biotSavart (fun z => conj (f (B0009.toPlane z))) 1 (planeToC y) =
      conj (B0009.biotSavart (fun z => f (B0009.toPlane z)) 1 (planeToC y)) :=
    biotSavart_conj _ 1 _
  simp only [h0, h1, map_sub, map_neg, map_add, map_mul, Complex.conj_ofReal]

/-- **Leaf `SeedPlanarPointwiseEigen`** (SP 593-610, 662-670, 2866-2870): the planar seed modes
satisfy the classical eigen equation `movLPlanar (κ.e j) = λ_j κ.e j` on the plane. -/
theorem seedPlanarPointwiseEigen (κ : PlanarFrameKernels) : SeedPlanarPointwiseEigen κ := by
  intro lam h hh ℓ hIS he0 he1 j y
  obtain ⟨hsm, hon, C, N, hC⟩ := seed_smooth_given hIS he0
  have hrad := radial_eigen hIS hon
  have he0f : κ.e 0 = fun x => PartI.seedPlanar h (planeToC x) := funext he0
  have he1f : κ.e 1 = fun x => conj (PartI.seedPlanar h (planeToC x)) := funext he1
  have h0 := eig_zero hsm hon hC hrad
  fin_cases j
  · simp only [Fin.zero_eta, seedModeEigen, ite_true]
    rw [he0f]
    exact h0 y
  · simp only [Fin.mk_one, seedModeEigen, one_ne_zero, ite_false]
    rw [he1f, movLPlanar_conj, h0 y, map_mul]

end EulerErrorEig

end UnforcedLeray.Short.IIIa
