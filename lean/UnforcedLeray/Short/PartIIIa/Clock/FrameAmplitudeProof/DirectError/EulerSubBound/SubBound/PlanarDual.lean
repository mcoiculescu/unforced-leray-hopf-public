import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound.SubBound.SectorLimit
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.GaussCore
import UnforcedLeray.Short.PartI.Tasks.AdjointEigenvectorExplicit
import UnforcedLeray.Short.PartI.Tasks.SeedFunctional.GreenTwoSmooth
import UnforcedLeray.Short.PartI.Tasks.SeedModeRegularityProof

/-!
# Planar seed duality `v₀·∇λ_k - K_∞^T(λ_k ∇ω₀) = λ_k λ_k` (helper for `PartIII-a:T21/c5/2/2/2`)

Source of record: `the November 2 reference manuscript` (SP), lines 593-610,
662-670, 788-803, 2891-2918 (`eq:short-seed-functional`).

For the seed triple `(lam, h, ℓ)` the planar dual kernel is
`λ₀ = c G(|y|) e^{-2iϑ}`, `G = Δ₂⁻¹h / (Ω - i lam/2)`, `c = J_q⁻¹/(2π)`
(`CutFTCGradPerSum.seedDualExplicit`), and the eigen equation `L₀h = lam h` gives `k G = h`
(`kG_eq_h`). Hence `λ₀ ∇ω₀ = c q̃ y` with `q̃ = h(|y|)e^{-2iϑ}`, and the planar adjoint is
`K_∞^T(λ₀∇ω₀)(y) = -c y·(K q̃)(y) = -2ic Δ₂⁻¹h(|y|) e^{-2iϑ}` (`kerAdjPl_seedDual` and
`PlanarDualSub.dot_biotSavart_ofProfile_lim`), while `v₀·∇λ₀ = Ω ∂_ϑ λ₀ = -2iΩ λ₀`
(`transCx_v0_seedDual`). Their difference is `2ic(Δ₂⁻¹h - ΩG)e^{-2iϑ} = lam λ₀`. The second row
`λ₁ = \bar λ₀` follows by conjugation.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa

namespace DirectEulerSub

/-- **Planar seed duality for the realizing seed triple** (SP 593-610, 2891-2918,
`eq:short-seed-functional`): for the Part I seed triple `(lam, h, ℓ)` realizing `κ`,
`v₀·∇λ_k - K_∞^T(λ_k ∇ω₀) = λ_k λ_k` on the plane (`λ₀ = lam`, `λ₁ = conj lam`), where
`v₀ = e^{-|y|²/4} y^⊥` is the Gaussian vortex, `ω₀ = curl v₀`, and `K_∞^T` is the planar
Biot-Savart adjoint `EulerSubCore.kerAdjPl`. -/
def SeedPlanarDualEigen (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h) ℓ →
    (∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y)) →
    (∀ y, κ.e 1 y = starRingEnd ℂ (PartI.seedPlanar h (planeToC y))) →
    (∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ y, κ.lamP 0 y * f (planeToC y) = PartI.seedEll h (Planar.NUE.Polar.angularSector f 2) ∧
      ∫ y, κ.lamP 1 y * f (planeToC y) =
        starRingEnd ℂ (PartI.seedEll h (fun r => starRingEnd ℂ
          (Planar.NUE.Polar.angularSector f (-2) r)))) →
    ∀ (k : Fin 2) (y : ℝ × ℝ),
      E0.transCx (fun z l => UnforcedLeray.Train.v0 z l) (κ.lamP k) y -
        EulerSubCore.kerAdjPl (fun l x => κ.lamP k x *
          ((B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x : ℝ) : ℂ)) y =
      seedModeEigen lam k * κ.lamP k y

end DirectEulerSub

namespace PlanarDualSub

open UnforcedLeray UnforcedLeray.Planar.NUE

/-! ## 1. The Gaussian vortex: `curl v₀ = ω₀`, `∇ω₀ = k(|x|) x` -/

theorem gauss0_eq_radialOmega (y : ℝ × ℝ) :
    Train.gauss0 y = GaussianVortex.radialOmega ‖planeToC y‖ := by
  rw [Train.gauss0, GaussianVortex.radialOmega, EulerSubCore.sq_norm_planeToC]
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

theorem pd_curl_v0 (l : Fin 2) (x : ℝ × ℝ) :
    B0579.pd l (Cyl.curl Train.v0) x =
      GaussianVortex.radialK ‖planeToC x‖ * (if l = 0 then x.1 else x.2) := by
  rw [curl_v0_eq]
  have hd : DifferentiableAt ℝ GaussianVortex.vorticity x :=
    (GaussianVortex.contDiff_vorticity.differentiable (by simp)) x
  have hr : GaussianVortex.radialK ‖planeToC x‖ =
      (GaussianVortex.radiusSq x / 4 - 2) * GaussianVortex.planarGaussian x := by
    rw [GaussianVortex.radialK, GaussianVortex.radialOmega, EulerSubCore.sq_norm_planeToC]
    simp only [GaussianVortex.planarGaussian, GaussianVortex.radiusSq]
  fin_cases l
  · simp only [B0579.pd, B0579.dir, Fin.zero_eta, Matrix.cons_val_zero, if_true]
    rw [← GaussianVortex.partialX_eq_fderiv hd, GaussianVortex.partialX_vorticity, hr]
    ring
  · simp only [B0579.pd, B0579.dir, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      one_ne_zero, if_false]
    rw [← GaussianVortex.partialY_eq_fderiv hd, GaussianVortex.partialY_vorticity, hr]
    ring

/-! ## 2. Kernel algebra: `x·K_∞(x - y) = -y·K_∞(y - x)` -/

theorem sum_mul_kerPl (x y : ℝ × ℝ) :
    (x.1 : ℂ) * ((EulerSubCore.kerPl (x - y) 0 : ℝ) : ℂ) +
        (x.2 : ℂ) * ((EulerSubCore.kerPl (x - y) 1 : ℝ) : ℂ) =
      -((y.1 : ℂ) * B0009.kernel 0 (planeToC y - planeToC x) +
        (y.2 : ℂ) * B0009.kernel 1 (planeToC y - planeToC x)) := by
  have hw : (2 * Real.pi * Complex.I * (((x - y).1 : ℂ) + ((x - y).2 : ℂ) * Complex.I)) =
      ⟨-(2 * Real.pi * (x.2 - y.2)), 2 * Real.pi * (x.1 - y.1)⟩ := by
    apply Complex.ext <;> simp
  have hz : ‖planeToC y - planeToC x‖ ^ 2 = (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2 := by
    rw [← EulerSubCore.planeToC_sub, EulerSubCore.sq_norm_planeToC]
    simp only [Prod.fst_sub, Prod.snd_sub]; ring
  have hpre : (planeToC y - planeToC x).re = -(x.1 - y.1) := by simp [planeToC]
  have hpim : (planeToC y - planeToC x).im = -(x.2 - y.2) := by simp [planeToC]
  set N := (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2 with hNdef
  have hD : -(2 * Real.pi * (x.2 - y.2)) * -(2 * Real.pi * (x.2 - y.2)) +
      2 * Real.pi * (x.1 - y.1) * (2 * Real.pi * (x.1 - y.1)) = (2 * Real.pi) ^ 2 * N := by
    rw [hNdef]; ring
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hab : N = 0 → x.1 - y.1 = 0 ∧ x.2 - y.2 = 0 := fun hN =>
    ⟨by nlinarith [sq_nonneg (x.1 - y.1), sq_nonneg (x.2 - y.2)],
      by nlinarith [sq_nonneg (x.1 - y.1), sq_nonneg (x.2 - y.2)]⟩
  have hk0 : EulerSubCore.kerPl (x - y) 0 = -(x.2 - y.2) * (2 * Real.pi * N)⁻¹ := by
    rw [EulerSubCore.kerPl_zero, hw, Complex.inv_re, Complex.normSq_mk, hD]
    by_cases hN : N = 0
    · obtain ⟨_, hb0⟩ := hab hN
      rw [hN, hb0]; simp
    · field_simp
  have hk1 : EulerSubCore.kerPl (x - y) 1 = (x.1 - y.1) * (2 * Real.pi * N)⁻¹ := by
    rw [EulerSubCore.kerPl_one, hw, Complex.inv_im, Complex.normSq_mk, hD]
    by_cases hN : N = 0
    · obtain ⟨ha0, _⟩ := hab hN
      rw [hN, ha0]; simp
    · field_simp
  have hp0 : B0009.perpComp 0 (planeToC y - planeToC x) /
      (2 * Real.pi * ‖planeToC y - planeToC x‖ ^ 2) = (x.2 - y.2) * (2 * Real.pi * N)⁻¹ := by
    simp only [B0009.perpComp, hpim, hz]; ring
  have hp1 : B0009.perpComp 1 (planeToC y - planeToC x) /
      (2 * Real.pi * ‖planeToC y - planeToC x‖ ^ 2) = -(x.1 - y.1) * (2 * Real.pi * N)⁻¹ := by
    simp only [B0009.perpComp, hpre, hz]; ring
  have hreal : x.1 * EulerSubCore.kerPl (x - y) 0 + x.2 * EulerSubCore.kerPl (x - y) 1 =
      -(y.1 * (B0009.perpComp 0 (planeToC y - planeToC x) /
          (2 * Real.pi * ‖planeToC y - planeToC x‖ ^ 2)) +
        y.2 * (B0009.perpComp 1 (planeToC y - planeToC x) /
          (2 * Real.pi * ‖planeToC y - planeToC x‖ ^ 2))) := by
    rw [hk0, hk1, hp0, hp1]; ring
  have hc := congrArg (fun t : ℝ => (t : ℂ)) hreal
  simp only [B0009.kernel]
  push_cast at hc ⊢
  linear_combination hc

/-! ## 3. The seed facts for the given triple -/

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

/-- The eigen equation in the form `k G = h` on `(0,∞)`. -/
theorem kG_eq_h {lam : ℂ} {h : ℝ → ℂ} {hh : MemLp h 2 B0010.xGMeasure}
    {ℓ : B0010.XG →L[ℂ] ℂ} (hI : PartI.IsSeedXG lam (hh.toLp h) ℓ)
    (hs : ContDiffOn ℝ ∞ h (Ioi 0)) (r : ℝ) (hr : 0 < r) :
    (GaussianVortex.radialK r : ℂ) * CutFTCGradPerSum.seedDualRadialG lam h r = h r := by
  have hre := hI.re_pos
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
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hcont hcont2 hr
  simp only at heq
  have hD := PartI.adjEig_den_ne hre (GaussianVortex.radialOmega r)
  unfold CutFTCGradPerSum.seedDualRadialG
  rw [if_pos hr, mul_div_assoc', div_eq_iff hD]
  linear_combination -heq

/-! ## 4. The transport part `v₀·∇λ₀ = -2iΩ λ₀` -/

theorem seedDualExplicit_zero_eq_comp (lam : ℂ) (h : ℝ → ℂ) :
    CutFTCGradPerSum.seedDualExplicit lam h 0 = fun x =>
      (PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ) * Ang.ofProfile (-2) (CutFTCGradPerSum.seedDualRadialG lam h)
        (planeToC x) := by
  funext x
  unfold CutFTCGradPerSum.seedDualExplicit
  simp only [Ang.ofProfile, if_true, ite_true, ↓reduceIte]
  ring

theorem transCx_v0_seedDual {lam : ℂ} {h : ℝ → ℂ}
    (hdiff : Differentiable ℝ (CutFTCGradPerSum.seedDualExplicit lam h 0)) (y : ℝ × ℝ) :
    E0.transCx (fun z l => Train.v0 z l) (CutFTCGradPerSum.seedDualExplicit lam h 0) y =
      (Train.gauss0 y : ℂ) * (Complex.I * ((-2 : ℤ) : ℂ) * CutFTCGradPerSum.seedDualExplicit lam h 0 y) := by
  set c : ℂ := (PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ) with hc
  set Λc : ℂ → ℂ := fun z => c * Ang.ofProfile (-2) (CutFTCGradPerSum.seedDualRadialG lam h) z with hΛcdef
  have hΛ : CutFTCGradPerSum.seedDualExplicit lam h 0 = fun x => Λc (planeToC x) :=
    seedDualExplicit_zero_eq_comp lam h
  have hΛc : Λc = fun z => CutFTCGradPerSum.seedDualExplicit lam h 0 (z.re, z.im) := by
    funext z
    rw [hΛ]
    congr 1
  have hdc : DifferentiableAt ℝ Λc (planeToC y) := by
    rw [hΛc]
    have hl : DifferentiableAt ℝ (fun z : ℂ => (z.re, z.im)) (planeToC y) :=
      (Complex.reCLM.differentiableAt).prodMk (Complex.imCLM.differentiableAt)
    exact (hdiff _).comp _ hl
  set L := fderiv ℝ Λc (planeToC y) with hLdef
  have hL : HasFDerivAt Λc L (planeToC y) := hdc.hasFDerivAt
  have hfun : (fun x => Λc (planeToC x)) = Λc ∘ GradPerSumLeaves.planeCLM := by
    funext x; simp [GradPerSumLeaves.planeCLM_apply]
  have hcomp : HasFDerivAt (CutFTCGradPerSum.seedDualExplicit lam h 0) (L.comp GradPerSumLeaves.planeCLM) y := by
    rw [hΛ, hfun]
    exact hL.comp y GradPerSumLeaves.planeCLM.hasFDerivAt
  have hpd0 : pdCx 0 (CutFTCGradPerSum.seedDualExplicit lam h 0) y = L 1 := by
    rw [pdCx, hcomp.fderiv]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, GradPerSumLeaves.planeCLM_apply]
    first
      | (congr 1; done)
      | (congr 1; apply Complex.ext <;> simp [planeToC, B0579.dir])
  have hpd1 : pdCx 1 (CutFTCGradPerSum.seedDualExplicit lam h 0) y = L Complex.I := by
    rw [pdCx, hcomp.fderiv]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, GradPerSumLeaves.planeCLM_apply]
    first
      | (congr 1; done)
      | (congr 1; apply Complex.ext <;> simp [planeToC, B0579.dir])
  have hrot := Planar.fderiv_sector_rot (n := -2) hL (fun θ => by
    simp only [hΛcdef]
    rw [Planar.ofProfile_rot]
    ring)
  have hIy : Complex.I * planeToC y = (-y.2) • (1 : ℂ) + y.1 • Complex.I := by
    apply Complex.ext <;> simp [planeToC]
  have hLI : L (Complex.I * planeToC y) = -y.2 * L 1 + y.1 * L Complex.I := by
    rw [hIy, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hv0 : Train.v0 y 0 = Train.gauss0 y * (-y.2) := by simp [Train.v0]
  have hv1 : Train.v0 y 1 = Train.gauss0 y * y.1 := by simp [Train.v0]
  unfold E0.transCx
  beta_reduce
  rw [hpd0, hpd1, hv0, hv1]
  have hval : CutFTCGradPerSum.seedDualExplicit lam h 0 y = Λc (planeToC y) := by rw [hΛ]
  rw [hval]
  push_cast
  linear_combination (↑(Train.gauss0 y) : ℂ) * (hrot - hLI)

/-! ## 5. The adjoint part `K_∞^T(λ₀∇ω₀) = -c y·(K q̃)` -/

theorem integrable_kernel_planeToC {q : ℂ → ℂ} (hc : Continuous q) {K : ℝ}
    (hK : ∀ z, ‖q z‖ ≤ K) (hi : Integrable q) (i : Fin 2) (y : ℝ × ℝ) :
    Integrable (fun x : ℝ × ℝ =>
      B0009.kernel i (planeToC y - planeToC x) * q (planeToC x)) := by
  have h1 := PartI.BiotSavartCurlAux.integrable_conv_kernel (i := i) (planeToC y) hc hK hi
  have h2 := (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding).2 h1
  exact h2

theorem integral_kernel_planeToC (g : ℂ → ℂ) :
    ∫ x : ℝ × ℝ, g (planeToC x) = ∫ z : ℂ, g z :=
  (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding g

theorem kerAdjPl_seedDual {lam : ℂ} {h : ℝ → ℂ}
    (hkG : ∀ r : ℝ, 0 < r → (GaussianVortex.radialK r : ℂ) * CutFTCGradPerSum.seedDualRadialG lam h r = h r)
    (hc : Continuous (Ang.ofProfile (-2) h)) {K : ℝ}
    (hK : ∀ z, ‖Ang.ofProfile (-2) h z‖ ≤ K) (hi : Integrable (Ang.ofProfile (-2) h))
    (y : ℝ × ℝ) :
    EulerSubCore.kerAdjPl (fun l x => CutFTCGradPerSum.seedDualExplicit lam h 0 x *
        ((B0579.pd l (Cyl.curl Train.v0) x : ℝ) : ℂ)) y =
      -((PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ)) *
        ((y.1 : ℂ) * B0009.biotSavart (Ang.ofProfile (-2) h) 0 (planeToC y) +
          (y.2 : ℂ) * B0009.biotSavart (Ang.ofProfile (-2) h) 1 (planeToC y)) := by
  set c : ℂ := (PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ) with hcdef
  set q := Ang.ofProfile (-2) h with hqdef
  have hprod : ∀ (l : Fin 2) (x : ℝ × ℝ),
      CutFTCGradPerSum.seedDualExplicit lam h 0 x * ((B0579.pd l (Cyl.curl Train.v0) x : ℝ) : ℂ) =
        c * q (planeToC x) * ((if l = 0 then x.1 else x.2 : ℝ) : ℂ) := by
    intro l x
    rw [pd_curl_v0, seedDualExplicit_zero_eq_comp]
    simp only [hqdef, Ang.ofProfile]
    by_cases hx : planeToC x = 0
    · have hphase : Ang.angPhase (-2) (planeToC x) = 0 := by
        rw [hx]; simp [Ang.angPhase]
      rw [hphase]; simp
    · have hr : 0 < ‖planeToC x‖ := norm_pos_iff.2 hx
      have hk := hkG _ hr
      push_cast
      rw [← hk]
      ring
  have hpt : ∀ x : ℝ × ℝ,
      ∑ l : Fin 2, CutFTCGradPerSum.seedDualExplicit lam h 0 x * ((B0579.pd l (Cyl.curl Train.v0) x : ℝ) : ℂ) *
          ((EulerSubCore.kerPl (x - y) l : ℝ) : ℂ) =
        -c * ((y.1 : ℂ) * (B0009.kernel 0 (planeToC y - planeToC x) * q (planeToC x)) +
          (y.2 : ℂ) * (B0009.kernel 1 (planeToC y - planeToC x) * q (planeToC x))) := by
    intro x
    rw [Fin.sum_univ_two, hprod 0 x, hprod 1 x]
    simp only [eq_self_iff_true, if_true, ite_true, one_ne_zero, if_false, ite_false, ↓reduceIte]
    have hk := sum_mul_kerPl x y
    linear_combination (c * q (planeToC x)) * hk
  unfold EulerSubCore.kerAdjPl
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  have hi0 := integrable_kernel_planeToC hc hK hi 0 y
  have hi1 := integrable_kernel_planeToC hc hK hi 1 y
  rw [integral_const_mul, integral_add (hi0.const_mul _) (hi1.const_mul _), integral_const_mul,
    integral_const_mul]
  rw [integral_kernel_planeToC (fun z => B0009.kernel 0 (planeToC y - z) * q z),
    integral_kernel_planeToC (fun z => B0009.kernel 1 (planeToC y - z) * q z),
    B0009.biotSavart_apply, B0009.biotSavart_apply]

end PlanarDualSub

end UnforcedLeray.Short.IIIa
