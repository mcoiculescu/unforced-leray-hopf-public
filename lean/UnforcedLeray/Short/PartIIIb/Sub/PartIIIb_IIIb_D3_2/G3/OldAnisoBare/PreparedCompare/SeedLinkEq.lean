import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2_G3_1_4_3
import UnforcedLeray.Cons.L2.CanonicalBranch
import UnforcedLeray.Short.PartI.Tasks.AdjointKernelOneDim
import UnforcedLeray.Short.PartI.Tasks.SeedUniqueness
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.Ext
import UnforcedLeray.Short.PartIIIa.Clock.FrameKernels
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2.g2ModeBounds

/-!
# `PartIII-b:IIIb-D3/2/G3/1/4/3/1`: `SeedLinkEqPlanarMode`

Source of record: `the November 2 reference manuscript`, lines 597–610, 625–627,
4416–4426.

Proves `seedLinkEqPlanarMode_of (D : SeqData) : SeedLinkEqPlanarMode D`: under
`D.RepairStanding dm dp` and `SeedLink D κ`, the planar seed kernel `κ.e 0` agrees with
`IIIa.planarMode D.Pl.mode`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

open FlatSettingInst

private lemma norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private lemma planeToC_eq (y : ℝ × ℝ) :
    IIIa.planeToC y = (y.1 : ℂ) + (y.2 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [IIIa.planeToC]

private lemma norm_planeToC (y : ℝ × ℝ) : ‖IIIa.planeToC y‖ = planeR y := by
  have h1 : ‖IIIa.planeToC y‖ ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
    rw [norm_sq_eq]; rfl
  have h2 : 0 ≤ ‖IIIa.planeToC y‖ := norm_nonneg _
  unfold planeR
  rw [← h1, Real.sqrt_sq h2]

private lemma seedPlanar_strainProfile_eq (z : ℂ) :
    PartI.seedPlanar strainProfile z = ((strainK ‖z‖ : ℝ) : ℂ) * z ^ 2 := by
  unfold PartI.seedPlanar Planar.NUE.Ang.ofProfile Planar.NUE.Ang.angPhase strainProfile
  by_cases hz : z = 0
  · subst hz; simp
  · have hnorm : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
    push_cast
    rw [zpow_ofNat, div_pow]
    field_simp [hnorm]

private lemma contDiff_seedPlanar_strainProfile :
    ContDiff ℝ ∞ (PartI.seedPlanar strainProfile) := by
  have heq : PartI.seedPlanar strainProfile = fun z : ℂ =>
      ((((z.re ^ 2 + z.im ^ 2) / 4 - 2) * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 4) : ℝ) : ℂ) *
        z ^ 2 := by
    ext z
    rw [seedPlanar_strainProfile_eq]
    unfold strainK
    rw [norm_sq_eq]
  rw [heq]
  have hre : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hsq : ContDiff ℝ ∞ (fun z : ℂ => z.re ^ 2 + z.im ^ 2) :=
    (hre.pow 2).add (him.pow 2)
  have hreal : ContDiff ℝ ∞ (fun z : ℂ =>
      ((z.re ^ 2 + z.im ^ 2) / 4 - 2) * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 4)) :=
    ((hsq.div_const 4).sub contDiff_const).mul (Real.contDiff_exp.comp (hsq.neg.div_const 4))
  exact (Complex.ofRealCLM.contDiff.comp hreal).mul (contDiff_id.pow 2)

private lemma gaussRdE_one_eq_strainProfile (r : ℝ) :
    gaussRdE 1 r = r ^ 2 * strainK r := by
  rw [G2.g2mb_gaussRdE_one]
  unfold strainK
  ring

private lemma seedPlanar_strainProfile_planeToC (y : ℝ × ℝ) :
    PartI.seedPlanar strainProfile (IIIa.planeToC y) = hMode 1 y := by
  rw [seedPlanar_strainProfile_eq, norm_planeToC]
  unfold hMode IIIa.angTwo
  rw [gaussRdE_one_eq_strainProfile, ← planeToC_eq]
  by_cases hy : y.1 ^ 2 + y.2 ^ 2 = 0
  · have hr0 : planeR y ^ 2 = 0 := by rw [G2.g2mb_planeR_sq, hy]
    have hz : IIIa.planeToC y = 0 := by
      have h1 : y.1 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
      have h2 : y.2 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
      apply Complex.ext <;> simp [IIIa.planeToC, h1, h2]
    rw [hz, hy]
    simp [hr0]
  · have hyC : ((y.1 : ℂ) ^ 2 + (y.2 : ℂ) ^ 2) ≠ 0 := by
      exact_mod_cast hy
    have hr2 : (planeR y : ℂ) ^ 2 = (y.1 : ℂ) ^ 2 + (y.2 : ℂ) ^ 2 := by
      exact_mod_cast G2.g2mb_planeR_sq y
    push_cast
    rw [hr2]
    field_simp [hyC]

private lemma strainProfile_eq_profFun :
    strainProfile = B0094.profFun ((1 / 4 : ℂ) • Polynomial.X - 2) := by
  funext r
  unfold strainProfile strainK B0094.profFun B0094.gauss
  simp only [Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_X,
    Polynomial.eval_ofNat, smul_eq_mul, neg_div]
  push_cast
  ring

private lemma memXG_strainProfile : MemXG strainProfile := by
  have hm : AEStronglyMeasurable strainProfile (volume.restrict (Ioi 0)) := by
    rw [strainProfile_eq_profFun]
    exact (B0094.continuous_profFun _).aestronglyMeasurable
  have hlp : MemLp strainProfile 2 B0010.xGMeasure := by
    rw [strainProfile_eq_profFun]
    exact B0094.memLp_profFun _
  exact Cons.G3b.memXG_of_memLp hm hlp

private lemma seedPlanar_eq_of_eqOn_Ioi {f g : ℝ → ℂ} (hfg : EqOn f g (Ioi 0)) :
    PartI.seedPlanar f = PartI.seedPlanar g := by
  funext z
  unfold PartI.seedPlanar Planar.NUE.Ang.ofProfile Planar.NUE.Ang.angPhase
  by_cases hz : z = 0
  · subst hz; simp
  · rw [hfg (norm_pos_iff.mpr hz)]

private lemma seedPlanar_planeToC_eq_planarMode {f g : Profile} (hfg : EqOn f g (Ioi 0))
    (y : ℝ × ℝ) :
    PartI.seedPlanar f (IIIa.planeToC y) = IIIa.planarMode g y := by
  unfold PartI.seedPlanar Planar.NUE.Ang.ofProfile Planar.NUE.Ang.angPhase IIIa.planarMode
    IIIa.angTwo
  rw [norm_planeToC, ← planeToC_eq]
  unfold planeR
  by_cases hy : y.1 ^ 2 + y.2 ^ 2 = 0
  · have hz : IIIa.planeToC y = 0 := by
      have h1 : y.1 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
      have h2 : y.2 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
      apply Complex.ext <;> simp [IIIa.planeToC, h1, h2]
    rw [hz, hy]
    simp
  · have hpos : 0 < y.1 ^ 2 + y.2 ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hy)
    have hrpos : 0 < Real.sqrt (y.1 ^ 2 + y.2 ^ 2) := Real.sqrt_pos.mpr hpos
    rw [hfg hrpos, zpow_ofNat, div_pow, ← Complex.ofReal_pow, Real.sq_sqrt hpos.le]

/-- **Main theorem (`PartIII-b:IIIb-D3/2/G3/1/4/3/1`)**: under `D.RepairStanding dm dp` and
`SeedLink D κ`, the direct planar seed kernel `κ.e 0` agrees with `IIIa.planarMode D.Pl.mode`. -/
theorem seedLinkEqPlanarMode_of (D : SeqData) : SeedLinkEqPlanarMode D := by
  intro dm dp hst κ hκ
  obtain ⟨⟨lam, h, hh, ℓ, hIS, he0, he1, hcl⟩, hpair⟩ := hκ
  -- Step 2: q_Pl and qdag_Pl in B0010.XG, and uniqueness of the right eigenvector.
  let hm_Pl := Cons.G3b.memLp_of_memXG hst.planar.eigenpair.memXG
  let q_Pl : B0010.XG := hm_Pl.toLp D.Pl.mode
  let hmad_Pl := Cons.G3b.memLp_of_memXG hst.planar.adjoint.memXG
  let qdag_Pl : B0010.XG := hmad_Pl.toLp D.Pl.adjointMode
  have hq_Pl_eigen : B0012.L0 q_Pl = D.Pl.eigenvalue • q_Pl := by
    change B0012.L0 (hm_Pl.toLp D.Pl.mode) = D.Pl.eigenvalue • q_Pl
    rw [B0012.L0_toLp hm_Pl]
    apply Lp.ext
    filter_upwards [B0012.ae_xG_pos, (B0012.memLp_L0Fun hm_Pl).coeFn_toLp,
      hm_Pl.coeFn_toLp, Lp.coeFn_smul D.Pl.eigenvalue q_Pl] with r hr hL hq hsmul
    have hq' : ((q_Pl : B0010.XG) : ℝ → ℂ) r = D.Pl.mode r := hq
    rw [hL]
    change B0012.L0Fun D.Pl.mode r = ((D.Pl.eigenvalue • q_Pl : B0010.XG) : ℝ → ℂ) r
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hq', ← Cons.G3b.generatorL0_eq_L0Fun D.Pl.mode r,
      hst.planar.eigenpair.eigen r hr]
  have hq_Pl_ne : q_Pl ≠ 0 := by
    intro h0
    apply hst.planar.eigenpair.nonzero
    have hzeroX : D.Pl.mode =ᵐ[B0010.xGMeasure] (0 : ℝ → ℂ) := by
      filter_upwards [hm_Pl.coeFn_toLp,
        (show (⇑q_Pl : ℝ → ℂ) =ᵐ[B0010.xGMeasure] 0 from by
          rw [h0]; exact Lp.coeFn_zero ℂ 2 B0010.xGMeasure)] with r h1 h2
      rw [← h1, h2]
    exact B0012.restrict_ac.ae_le hzeroX
  obtain ⟨hlam_eq, c₁, hc₁⟩ := Planar.L0_eigen_unique hIS.re_pos hst.planar.eigenpair.re_pos
    hIS.eigen hq_Pl_eigen hIS.ne_zero hq_Pl_ne
  -- Step 3: Left eigenfunctional identity and uniqueness of the adjoint eigenvector.
  have hinner_L0 : ∀ f : B0010.XG,
      inner ℂ qdag_Pl (B0012.L0 f) = D.Pl.eigenvalue * inner ℂ qdag_Pl f := by
    intro f
    let p : Profile := (f : ℝ → ℂ)
    have hpMeas : AEStronglyMeasurable p (volume.restrict (Ioi (0 : ℝ))) :=
      (Lp.aestronglyMeasurable f).mono_ac B0012.restrict_ac
    have hp : MemXG p := Cons.G3b.memXG_of_memLp hpMeas (Lp.memLp f)
    have hgenAe : generatorL0 p =ᵐ[B0010.xGMeasure] (B0012.L0 f : ℝ → ℂ) := by
      filter_upwards [B0012.coeFn_L0 f] with r hr
      rw [Cons.G3b.generatorL0_eq_L0Fun p r]
      exact hr.symm
    have hgenLp : MemLp (generatorL0 p) 2 B0010.xGMeasure :=
      (Lp.memLp (B0012.L0 f)).ae_eq hgenAe.symm
    have hgenMeas : AEStronglyMeasurable (generatorL0 p) (volume.restrict (Ioi (0 : ℝ))) :=
      (B0012.memXG_coe (B0012.L0 f)).1.congr (B0012.restrict_ac.ae_le hgenAe.symm)
    have hgen : MemXG (generatorL0 p) := Cons.G3b.memXG_of_memLp hgenMeas hgenLp
    have hq : MemXG D.Pl.adjointMode := hst.planar.adjoint.memXG
    have hpRep : (Cons.G3b.memLp_of_memXG hp).toLp p = f := by
      apply Lp.ext
      filter_upwards [(Cons.G3b.memLp_of_memXG hp).coeFn_toLp] with r hr
      exact hr
    have hgenRep : (Cons.G3b.memLp_of_memXG hgen).toLp (generatorL0 p) = B0012.L0 f := by
      apply Lp.ext
      filter_upwards [(Cons.G3b.memLp_of_memXG hgen).coeFn_toLp, B0012.coeFn_L0 f] with r hr₁ hr₂
      rw [hr₁, Cons.G3b.generatorL0_eq_L0Fun]
      exact hr₂.symm
    have hleft := hst.planar.adjoint.left_eigen p hp
    rw [Cons.G3b.gaussianPairing_eq_inner hp hq, Cons.G3b.gaussianPairing_eq_inner hgen hq,
      hgenRep, hpRep] at hleft
    exact hleft
  have hadj_eigen : ContinuousLinearMap.adjoint Planar.L0 qdag_Pl =
      (starRingEnd ℂ) lam • qdag_Pl := by
    apply ext_inner_right ℂ
    intro f
    rw [ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ qdag_Pl (B0012.L0 f) = _
    rw [hinner_L0 f, hlam_eq, inner_smul_left, starRingEnd_self_apply]
  let qd : B0010.XG := (InnerProductSpace.toDual ℂ B0010.XG).symm ℓ
  have hqd : ∀ f : B0010.XG, ℓ f = inner ℂ qd f := fun f =>
    (InnerProductSpace.toDual_symm_apply).symm
  obtain ⟨c₂, hc₂⟩ := PartI.adjoint_eigenvector_unique hIS hqd hadj_eigen
  -- Step 4: Smoothness of PartI.seedPlanar h and strainCoupling identity.
  obtain ⟨_, _, h', hae', hsm', _, _, _, _, _, _, _⟩ :=
    PartI.seedModeRegularity_proof lam h hh ℓ hIS
  have hcont_h' : ContinuousOn h' (Ioi 0) := by
    have hcd : ContinuousOn (fun r : ℝ => PartI.seedPlanar h' (r : ℂ)) (Ioi 0) :=
      (hsm'.continuous.comp Complex.continuous_ofReal).continuousOn
    exact hcd.congr (fun r hr => (seedPlanar_ofReal_eq h' r hr).symm)
  have hcont_h : ContinuousOn h (Ioi 0) := by
    have hce : ContinuousOn (fun r : ℝ => κ.e 0 (r, 0)) (Ioi 0) :=
      ((κ.e_cont 0).comp (continuous_id.prodMk continuous_const)).continuousOn
    refine hce.congr (fun r hr => ?_)
    have hpl : IIIa.planeToC (r, 0) = (r : ℂ) := by
      apply Complex.ext <;> simp [IIIa.planeToC]
    dsimp only
    rw [he0 (r, 0), hpl, seedPlanar_ofReal_eq h r hr]
  have heq_h'h : EqOn h' h (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hae' isOpen_Ioi hcont_h' hcont_h
  have hsm : ContDiff ℝ ∞ (PartI.seedPlanar h) := by
    rw [← seedPlanar_eq_of_eqOn_Ioi heq_h'h]
    exact hsm'
  obtain ⟨Ce, hCe⟩ := κ.e_decay
  have hG : ∃ C : ℝ, ∀ y : ℝ × ℝ,
      ‖PartI.seedPlanar h (IIIa.planeToC y)‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
    ⟨Ce, fun y => by rw [← he0 y]; exact hCe 0 y⟩
  obtain ⟨_, _, Kh, hKh⟩ := G2.g2ModeBounds
  have hfG : ∃ C : ℝ, ∀ y : ℝ × ℝ,
      ‖PartI.seedPlanar strainProfile (IIIa.planeToC y)‖ ≤
        C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
    ⟨Kh, fun y => by rw [seedPlanar_strainProfile_planeToC]; exact (hKh y).1⟩
  have hext := (seedBiorthExt_proof PartI.seedFunctional_proof lam h hh ℓ hIS hsm hG
    κ.lamP κ.lamP_cont κ.lamP_decay hcl (PartI.seedPlanar strainProfile)
    contDiff_seedPlanar_strainProfile hfG).1
  have hint : (∫ y, κ.lamP 0 y * hMode 1 y) =
      ∫ y, κ.lamP 0 y * PartI.seedPlanar strainProfile (IIIa.planeToC y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [seedPlanar_strainProfile_planeToC]
  have hpair_ell : D.Pl.strainCoupling = PartI.seedEll h strainProfile := by
    rw [← hpair, hint, hext, IIIa.seedEll_congr h _ strainProfile
      (fun r hr => (seedSectors_proof strainProfile r hr).1)]
  let hm_str := Cons.G3b.memLp_of_memXG memXG_strainProfile
  let str_XG : B0010.XG := hm_str.toLp strainProfile
  have hell_str : ℓ str_XG = PartI.seedEll h strainProfile := by
    have hsf := (PartI.seedFunctional_proof lam h hh ℓ hIS).2.2.2.1 str_XG
    rw [hsf]
    unfold PartI.seedEll
    congr 1
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [ae_imp_of_ae_restrict (B0012.restrict_ac.ae_le hm_str.coeFn_toLp)] with r hr hmem
    rw [hr hmem]
  have hsc_ell : D.Pl.strainCoupling = ℓ str_XG := hpair_ell.trans hell_str.symm
  have hsc_inner : D.Pl.strainCoupling = (starRingEnd ℂ) c₂ * ℓ str_XG := by
    change gaussianPairing strainProfile D.Pl.adjointMode = _
    rw [Cons.G3b.gaussianPairing_eq_inner memXG_strainProfile hst.planar.adjoint.memXG]
    change inner ℂ qdag_Pl str_XG = _
    rw [hc₂, inner_smul_left, ← hqd str_XG]
  have hc₂_eq : (starRingEnd ℂ) c₂ = 1 := by
    have hne : ℓ str_XG ≠ 0 := by
      rw [← hsc_ell]
      exact D.strainCoupling_ne
    apply mul_right_cancel₀ hne
    rw [← hsc_inner, one_mul, hsc_ell]
  -- Step 5: Normalization fixes c₁ = 1, hence D.Pl.mode = h on Ioi 0 and κ.e 0 = planarMode.
  have hnorm_pair : inner ℂ qdag_Pl q_Pl = 1 := by
    rw [← Cons.G3b.gaussianPairing_eq_inner hst.planar.eigenpair.memXG hst.planar.adjoint.memXG]
    exact hst.planar.adjoint.normalized
  have hc₁_eq : c₁ = 1 := by
    have h1 := hnorm_pair
    rw [hc₂, hc₁, inner_smul_left, inner_smul_right, ← hqd (hh.toLp h), hIS.ell_q,
      hc₂_eq, mul_one, one_mul] at h1
    exact h1
  have hq_Pl_eq : q_Pl = hh.toLp h := by
    rw [hc₁, hc₁_eq, one_smul]
  have hmode_ae : D.Pl.mode =ᵐ[volume.restrict (Ioi 0)] h := by
    have hX : D.Pl.mode =ᵐ[B0010.xGMeasure] h := by
      filter_upwards [hm_Pl.coeFn_toLp, hh.coeFn_toLp] with r hr1 hr2
      have hr1' : ((q_Pl : B0010.XG) : ℝ → ℂ) r = D.Pl.mode r := hr1
      rw [← hr1', hq_Pl_eq, hr2]
    exact B0012.restrict_ac.ae_le hX
  have hcont_mode : ContinuousOn D.Pl.mode (Ioi 0) := hst.planar.eigenpair.smooth.continuousOn
  have heq_mode : EqOn h D.Pl.mode (Ioi 0) :=
    (Measure.eqOn_open_of_ae_eq hmode_ae isOpen_Ioi hcont_mode hcont_h).symm
  funext y
  rw [he0 y, seedPlanar_planeToC_eq_planarMode heq_mode y]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3
