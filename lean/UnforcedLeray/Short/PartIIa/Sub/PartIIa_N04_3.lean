import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04.Defs
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04.SymGrad
import UnforcedLeray.Short.PartIIa.Tasks.F08cLerayYResolventComm

/-!
# Sub `PartII-a_N04_3`: Projected Adjoint Resolvent Equation (`AdjointResidualEq`)

Source of record: `the November 2 reference manuscript`,
lines 1828–1848 (Lemma `near:smooth-adjoint-comparison`).

This file proves:
1. Unconditional commutation `Teps hν hε hc hP μ G = PepsC ε c (RepsVec hν hε hc hP μ G)` and
   self-adjointness `ContinuousLinearMap.adjoint (PepsC ε c) = PepsC ε c`, yielding
   `ContinuousLinearMap.adjoint (Teps hν hε hc hP μ) Z =
     ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ) (PepsC ε c Z)`.
2. Complexified meridional vector generator `AepsVecC` and the exact generator difference on
   `MeridC`-valued profiles `AepsVecC ν ε u p - AepsVecC ν 0 u p = genDiffC ν ε u p` (from
   `generatorDifference` in `PartII-a:N03`), together with `L²(measureH c)` membership of
   `u`, `μ • u - AepsVecC ν ε u`, and `genDiffC ν ε u` for smooth meridional tests `IsMeridTest c u`.
3. Reduction `adjointResidualEq_of` of `AdjointResidualEq` to three self-contained leaf propositions:
   - `FlatAdjointWeakEq` (`PartII-a:N04/3/1`): weak flat resolvent identity
     `⟨(μ - A_0) u, T_0* Z⟩_H = ⟨u, P_0 Z⟩_H`
   - `GenDiffIBP` (`PartII-a:N04/3/2`): integration by parts
     `⟨(A_ε - A_0) u, v⟩_H = ⟨u, (A_ε* - A_0*) v⟩_H`
   - `RepsVecAdjointOfWeakEq` (`PartII-a:N04/3/3`): weak characterization of `RepsVec* R_0`
     via smooth meridional tests.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0221 UnforcedLeray.B0222 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.NearInst (merC)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-! ### 1. Unconditional commutation of `PepsC` and `RepsVec`, and `Teps.adjoint` -/

/-- Decomposition of any `G : HSpace c MeridC` into real and imaginary complexified parts. -/
theorem cplxH_reHC_add_im (c : ℝ) (G : HSpace c MeridC) :
    cplxH c (reHC c G) + Complex.I • cplxH c (reHC c ((-Complex.I) • G)) = G := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (cplxH c (reHC c G))
      (Complex.I • cplxH c (reHC c ((-Complex.I) • G))),
    Lp.coeFn_smul Complex.I (cplxH c (reHC c ((-Complex.I) • G))),
    cplxH_ae c (reHC c G), reHC_ae c G,
    cplxH_ae c (reHC c ((-Complex.I) • G)), reHC_ae c ((-Complex.I) • G),
    Lp.coeFn_smul (-Complex.I) G] with p hadd hsm hc1 hr1 hc2 hr2 hsmG
  ext i
  rw [hadd, Pi.add_apply, hsm, Pi.smul_apply, hc1, hr1, hc2, hr2, hsmG]
  simp only [merC, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, merReL_apply, smul_eq_mul,
    Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im,
    neg_zero, zero_mul, neg_one_mul, neg_neg, zero_sub]
  rw [mul_comm Complex.I]
  exact Complex.re_add_im (G p i)

/-- Under the chart-to-phase lift `U ∘ liftVec`, `PepsC ε c` conjugates to `lerayY` on `Yq P 2`. -/
theorem phaseLift_liftVec_PepsC {ε c P : ℝ} [Fact (0 < P)]
    (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    {U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2} (hU : N01.IsPhaseLift ε P U)
    (G : HSpace c MeridC) :
    U (B0223.liftVec hε hc hP (PepsC ε c G)) =
      lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (U (B0223.liftVec hε hc hP G)) := by
  have hreal : ∀ g : HSpace c Merid,
      U (B0223.liftVec hε hc hP (PepsC ε c (cplxH c g))) =
        lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
          (U (B0223.liftVec hε hc hP (cplxH c g))) := by
    intro g
    rw [pepsCCplx ε c hε hc g, liftVecCplx ε c P hε hc hP (B0226.Peps hε hc g),
      B0226.J_Peps hε hc g, N01.phaseLerayConj ε c P hε hc hP U hU (B0220.J hε hc g),
      ← liftVecCplx ε c P hε hc hP g]
  conv_lhs => rw [← cplxH_reHC_add_im c G]
  conv_rhs => rw [← cplxH_reHC_add_im c G]
  simp only [map_add, map_smul, hreal]

/-- Under the chart-to-phase lift `U ∘ liftVec`, `RepsVec` conjugates to the body resolvent `Rm`. -/
theorem phaseLift_liftVec_RepsVec {ν ε c P : ℝ} [Fact (0 < P)]
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    {μ : ℂ} (hγ : 0 < μ.re + 1 / 4)
    {U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2} (hU : N01.IsPhaseLift ε P U)
    (Rm : Yq P 2 →L[ℂ] Yq P 2) (hq : (2 : ℝ≥0∞) ≠ ⊤)
    (hRm : ∀ f, Rm f = ∫ t in Set.Ioi (0 : ℝ),
      Complex.exp (-(μ * t)) • B0421.phaseT (P := P) (q := 2) hq ν t f)
    (G : HSpace c MeridC) :
    U (B0223.liftVec hε hc hP (B0223.RepsVec hν hε hc hP μ G)) =
      Rm (U (B0223.liftVec hε hc hP G)) := by
  rw [B0223.J_RepsVec hν hε hc hP hγ G,
    N01.phaseLift_physRes N01.phaseSemigroupConj hν hε hU hγ Rm hq hRm]

/-- `Teps = RepsVec ∘ PepsC` equals `PepsC ∘ RepsVec` since `lerayY` commutes with the body
resolvent `Rm` (`lerayYResolventComm_proof`). -/
theorem Teps_eq_PepsC_comp_RepsVec {ν ε c P : ℝ} [Fact (0 < P)]
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    {μ : ℂ} (hγ : 0 < μ.re + 1 / 4) (G : HSpace c MeridC) :
    Teps hν hε hc hP μ G = PepsC ε c (B0223.RepsVec hν hε hc hP μ G) := by
  obtain ⟨U, hU⟩ := N01.phaseLiftExists ε P hε
  have h1 : (1 : ℝ≥0∞) < 2 := ENNReal.one_lt_two
  have h3 : (2 : ℝ≥0∞) < 3 := by norm_num
  have hμ' : 0 < μ.re + gammaR 2 := by rw [gammaR_two]; exact hγ
  obtain ⟨Rm, -, hRm⟩ := bodyResolvent_exists 2 h1 h3 P ν hν μ hμ'
  apply (B0223.liftVec hε hc hP).injective
  apply U.injective
  change U (B0223.liftVec hε hc hP (B0223.RepsVec hν hε hc hP μ (PepsC ε c G))) =
    U (B0223.liftVec hε hc hP (PepsC ε c (B0223.RepsVec hν hε hc hP μ G)))
  rw [phaseLift_liftVec_RepsVec hν hε hc hP hγ hU Rm ENNReal.ofNat_ne_top hRm (PepsC ε c G),
    phaseLift_liftVec_PepsC hε hc hP hU G,
    phaseLift_liftVec_PepsC hε hc hP hU (B0223.RepsVec hν hε hc hP μ G),
    phaseLift_liftVec_RepsVec hν hε hc hP hγ hU Rm ENNReal.ofNat_ne_top hRm G]
  exact (lerayYResolventComm_proof 2 h1 h3 P ν hν μ hμ' Rm hRm
    (U (B0223.liftVec hε hc hP G))).symm

/-- `PepsC ε c` is an orthogonal projection (`starProjection`), hence self-adjoint. -/
theorem adjoint_PepsC (ε c : ℝ) (Z : HSpace c MeridC) :
    ContinuousLinearMap.adjoint (PepsC ε c) Z = PepsC ε c Z := by
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  unfold PepsC
  set K := solenoidalHC ε c
  have h1 : inner ℂ x (K.starProjection Z) =
      inner ℂ (K.starProjection x) (K.starProjection Z) := by
    have horth : inner ℂ (x - K.starProjection x) (K.starProjection Z) = 0 :=
      K.starProjection_inner_eq_zero x (K.starProjection Z) (K.starProjection_apply_mem Z)
    rw [inner_sub_left, sub_eq_zero] at horth
    exact horth
  have h2 : inner ℂ (K.starProjection x) Z =
      inner ℂ (K.starProjection x) (K.starProjection Z) := by
    have horth : inner ℂ (K.starProjection x) (Z - K.starProjection Z) = 0 :=
      inner_eq_zero_symm.mp
        (K.starProjection_inner_eq_zero Z (K.starProjection x) (K.starProjection_apply_mem x))
    rw [inner_sub_right, sub_eq_zero] at horth
    exact horth
  exact h2.trans h1.symm

/-- Since `Teps = PepsC ∘ RepsVec` and `PepsC` is self-adjoint,
`Teps.adjoint Z = RepsVec.adjoint (PepsC ε c Z)` (source line 1842). -/
theorem adjoint_Teps_eq {ν ε c P : ℝ} [Fact (0 < P)]
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    {μ : ℂ} (hγ : 0 < μ.re + 1 / 4) (Z : HSpace c MeridC) :
    ContinuousLinearMap.adjoint (Teps hν hε hc hP μ) Z =
      ContinuousLinearMap.adjoint (B0223.RepsVec hν hε hc hP μ) (PepsC ε c Z) := by
  have hTeps : Teps hν hε hc hP μ = (PepsC ε c).comp (B0223.RepsVec hν hε hc hP μ) :=
    ContinuousLinearMap.ext fun G => Teps_eq_PepsC_comp_RepsVec hν hε hc hP hγ G
  rw [hTeps, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, adjoint_PepsC]

/-! ### 2. Complexified vector generator `AepsVecC` and exact generator difference -/

/-- The complexified meridional vector generator
`A_ε^vec u = -S u + ν s (Q_ε² u + ∂_η² u - ε² E u)` on `Profile → MeridC`
(source lines 1838–1840, B0222 `AepsVec`). -/
def AepsVecC (ν ε : ℝ) (u : Profile → MeridC) : Profile → MeridC := fun p =>
  -opS u p + (ν * p.1) • (opQ ε (opQ ε u) p + pdEta (pdEta u) p - (ε ^ 2 : ℝ) • opE u p)

private theorem clm_fderiv_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : Profile → E} {p : Profile}
    (hf : DifferentiableAt ℝ f p) (v : Profile) :
    L (fderiv ℝ f p v) = fderiv ℝ (fun q => L (f q)) p v := by
  have h : HasFDerivAt (fun q => L (f q)) (L.comp (fderiv ℝ f p)) p :=
    L.hasFDerivAt.comp p hf.hasFDerivAt
  rw [h.fderiv]
  rfl

private theorem differentiableAt_fderiv_apply_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Profile → E} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) (v : Profile) :
    DifferentiableAt ℝ (fun q => fderiv ℝ u q v) p := by
  have hD : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact hD.clm_apply (differentiableAt_const v)

private theorem differentiableAt_opS_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Profile → E} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    DifferentiableAt ℝ (opS u) p := by
  have hS := differentiableAt_fderiv_apply_of_contDiffAt hu (1, 0, 0)
  have hfst : DifferentiableAt ℝ (fun q : Profile => q.1) p := differentiableAt_fst
  exact hfst.smul hS

private theorem differentiableAt_opK_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Profile → E} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    DifferentiableAt ℝ (opK u) p := by
  have hS := differentiableAt_opS_of_contDiffAt hu
  have hEta := differentiableAt_fderiv_apply_of_contDiffAt hu (0, 0, 1)
  have hsnd : DifferentiableAt ℝ (fun q : Profile => q.2.2) p :=
    differentiableAt_snd.comp p differentiableAt_snd
  exact (hS.const_smul (2 : ℝ)).add (hsnd.smul hEta)

private theorem differentiableAt_opLam_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : Profile → E} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    DifferentiableAt ℝ (opLam u) p :=
  (differentiableAt_opK_of_contDiffAt hu).add (hu.differentiableAt (by norm_num))

private theorem differentiableAt_opQ_of_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ε : ℝ) {u : Profile → E} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    DifferentiableAt ℝ (opQ ε u) p := by
  have hQ := differentiableAt_fderiv_apply_of_contDiffAt hu (0, 1, 0)
  have hLam := differentiableAt_opLam_of_contDiffAt hu
  exact hQ.sub (hLam.const_smul ε)

private theorem clm_opS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {f : Profile → E} {p : Profile} (hf : DifferentiableAt ℝ f p) :
    L (opS f p) = B0221.opS (fun q => L (f q)) p := by
  simp only [opS, pdS, B0221.opS, B0221.dS, B0221.eS, map_smul, smul_eq_mul,
    clm_fderiv_apply L hf]

private theorem clm_opK {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {f : Profile → E} {p : Profile} (hf : DifferentiableAt ℝ f p) :
    L (opK f p) = B0221.opK (fun q => L (f q)) p := by
  simp only [opK, opS, pdS, pdEta, B0221.opK, B0221.dS, B0221.dEta, B0221.eS, B0221.eEta,
    map_add, map_smul, smul_eq_mul, clm_fderiv_apply L hf]
  ring

private theorem clm_opLam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {f : Profile → E} {p : Profile} (hf : DifferentiableAt ℝ f p) :
    L (opLam f p) = B0221.opK (fun q => L (f q)) p + L (f p) := by
  simp only [opLam, map_add, clm_opK L hf]

private theorem clm_opQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (ε : ℝ) {f : Profile → E} {p : Profile} (hf : DifferentiableAt ℝ f p) :
    L (opQ ε f p) = B0221.opQ ε (fun q => L (f q)) p := by
  simp only [opQ, pdQ, B0221.opQ, B0221.dQ, B0221.eQ, map_sub, map_add, map_smul, smul_eq_mul,
    clm_fderiv_apply L hf, clm_opK L hf]

private theorem clm_opQ_opQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (ε : ℝ) {u : Profile → E} {p : Profile} (hu : ContDiffAt ℝ 2 u p) :
    L (opQ ε (opQ ε u) p) = B0221.opQ ε (B0221.opQ ε (fun q => L (u q))) p := by
  rw [clm_opQ L ε (differentiableAt_opQ_of_contDiffAt ε hu)]
  have hev : (fun q => L (opQ ε u q)) =ᶠ[nhds p] B0221.opQ ε (fun q => L (u q)) := by
    filter_upwards [hu.eventually (by simp)] with q hq
    exact clm_opQ L ε (hq.differentiableAt (by norm_num))
  simp only [B0221.opQ, B0221.opK, B0221.dQ, B0221.dS, B0221.dEta, hev.fderiv_eq, hev.self_of_nhds]

private theorem clm_pdEta_pdEta {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {u : Profile → E} {p : Profile} (hu : ContDiffAt ℝ 2 u p) :
    L (pdEta (pdEta u) p) = B0221.dEta (B0221.dEta (fun q => L (u q))) p := by
  have hEta : DifferentiableAt ℝ (pdEta u) p :=
    differentiableAt_fderiv_apply_of_contDiffAt hu (0, 0, 1)
  change L (fderiv ℝ (pdEta u) p (0, 0, 1)) = B0221.dEta (B0221.dEta (fun q => L (u q))) p
  rw [clm_fderiv_apply L hEta]
  have hev : (fun q => L (pdEta u q)) =ᶠ[nhds p] B0221.dEta (fun q => L (u q)) := by
    filter_upwards [hu.eventually (by simp)] with q hq
    exact clm_fderiv_apply L (hq.differentiableAt (by norm_num)) (0, 0, 1)
  change fderiv ℝ (fun q => L (pdEta u q)) p B0221.eEta =
    fderiv ℝ (B0221.dEta (fun q => L (u q))) p B0221.eEta
  rw [hev.fderiv_eq]

private theorem clm_opLam_pdQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {u : Profile → E} {p : Profile} (hu : ContDiffAt ℝ 2 u p) :
    L (opLam (pdQ u) p) =
      B0221.opK (B0221.dQ (fun q => L (u q))) p + B0221.dQ (fun q => L (u q)) p := by
  have hQ : DifferentiableAt ℝ (pdQ u) p :=
    differentiableAt_fderiv_apply_of_contDiffAt hu (0, 1, 0)
  rw [clm_opLam L hQ]
  have hev : (fun q => L (pdQ u q)) =ᶠ[nhds p] B0221.dQ (fun q => L (u q)) := by
    filter_upwards [hu.eventually (by simp)] with q hq
    exact clm_fderiv_apply L (hq.differentiableAt (by norm_num)) (0, 1, 0)
  simp only [B0221.opK, B0221.dS, B0221.dEta, hev.fderiv_eq, hev.self_of_nhds]

private theorem clm_opLam_opLam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) {u : Profile → E} {p : Profile} (hu : ContDiffAt ℝ 2 u p) :
    L (opLam (opLam u) p) =
      B0221.opK (fun q => B0221.opK (fun x => L (u x)) q + L (u q)) p +
        (B0221.opK (fun x => L (u x)) p + L (u p)) := by
  have hLam := differentiableAt_opLam_of_contDiffAt hu
  rw [clm_opLam L hLam]
  have hev : (fun q => L (opLam u q)) =ᶠ[nhds p]
      fun q => B0221.opK (fun x => L (u x)) q + L (u q) := by
    filter_upwards [hu.eventually (by simp)] with q hq
    exact clm_opLam L (hq.differentiableAt (by norm_num))
  simp only [B0221.opK, B0221.dS, B0221.dEta, hev.fderiv_eq, hev.self_of_nhds]

private theorem clm_AepsVecC_sub_genDiffC (L : MeridC →L[ℝ] ℝ)
    (i : Fin 2) {u : Profile → MeridC} {p : Profile}
    (hLi : L (opE u p) = radialSel i * L (u p))
    (ν ε : ℝ) (hu : ContDiffAt ℝ 2 u p) :
    L (AepsVecC ν ε u p - AepsVecC ν 0 u p) = L (genDiffC ν ε u p) := by
  have hu0 : DifferentiableAt ℝ u p := hu.differentiableAt (by norm_num)
  have hLu : ContDiffAt ℝ 2 (fun q => L (u q)) p := L.contDiff.contDiffAt.comp p hu
  have hgen := generatorDifference ν ε (fun q => L (u q)) p hLu
  have h1 : L (AepsVecC ν ε u p) =
      B0221.Aeps ν ε (fun q => L (u q)) p - ν * p.1 * (radialSel i * ε ^ 2 * L (u p)) := by
    simp only [AepsVecC, B0221.Aeps, map_add, map_sub, map_neg, map_smul, smul_eq_mul,
      clm_opS L hu0, clm_opQ_opQ L ε hu, clm_pdEta_pdEta L hu, hLi]
    ring
  have h0 : L (AepsVecC ν 0 u p) = B0221.A0 ν (fun q => L (u q)) p := by
    have hA0 : B0221.Aeps ν 0 (fun q => L (u q)) p = B0221.A0 ν (fun q => L (u q)) p :=
      congr_fun (B0221.Aeps_zero ν (fun q => L (u q))) p
    have h10 : L (AepsVecC ν 0 u p) = B0221.Aeps ν 0 (fun q => L (u q)) p := by
      simp only [AepsVecC, B0221.Aeps, map_add, map_sub, map_neg, map_smul, smul_eq_mul,
        clm_opS L hu0, clm_opQ_opQ L 0 hu, clm_pdEta_pdEta L hu, hLi]
      ring
    exact h10.trans hA0
  have hgd : L (genDiffC ν ε u p) =
      ν * p.1 * (-2 * ε * (B0221.opK (B0221.dQ (fun q => L (u q))) p +
          B0221.dQ (fun q => L (u q)) p) +
        ε ^ 2 * (B0221.opK (fun q => B0221.opK (fun x => L (u x)) q + L (u q)) p +
          (B0221.opK (fun x => L (u x)) p + L (u p))) -
        radialSel i * ε ^ 2 * L (u p)) := by
    simp only [genDiffC, genDiff1, genDiff2, Complex.coe_smul,
      map_add, map_sub, map_smul, smul_eq_mul, clm_opLam_pdQ L hu, clm_opLam_opLam L hu, hLi]
    ring
  rw [map_sub, h1, h0, hgd]
  linear_combination hgen

/-- **Exact generator difference on `MeridC`-valued profiles** (source lines 1838–1840):
`AepsVecC ν ε u p - AepsVecC ν 0 u p = genDiffC ν ε u p` for `u` of class `C²` at `p`. -/
theorem AepsVecC_sub_eq_genDiffC (ν ε : ℝ) {u : Profile → MeridC} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    AepsVecC ν ε u p - AepsVecC ν 0 u p = genDiffC ν ε u p := by
  ext i
  set Lre : MeridC →L[ℝ] ℝ :=
    Complex.reCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  set Lim : MeridC →L[ℝ] ℝ :=
    Complex.imCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  have hre : Lre (opE u p) = radialSel i * Lre (u p) := by
    fin_cases i <;> simp [Lre, opE, radialSel]
  have him : Lim (opE u p) = radialSel i * Lim (u p) := by
    fin_cases i <;> simp [Lim, opE, radialSel]
  apply Complex.ext
  · exact clm_AepsVecC_sub_genDiffC Lre i hre ν ε hu
  · exact clm_AepsVecC_sub_genDiffC Lim i him ν ε hu

/-- `(μ - A_ε) u = (μ - A_0) u - (A_ε - A_0) u` pointwise for `u` of class `C²` at `p`. -/
theorem mu_sub_AepsVecC_eq (ν ε : ℝ) (μ : ℂ) {u : Profile → MeridC} {p : Profile}
    (hu : ContDiffAt ℝ 2 u p) :
    (μ • u p - AepsVecC ν ε u p) = (μ • u p - AepsVecC ν 0 u p) - genDiffC ν ε u p := by
  rw [← AepsVecC_sub_eq_genDiffC ν ε hu]
  abel

/-! ### 3. `L²(measureH c)` membership for smooth meridional tests (`IsMeridTest`) -/

private theorem contDiff_pd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} (hf : ContDiff ℝ ∞ f) (v : Profile) :
    ContDiff ℝ ∞ (fun p => fderiv ℝ f p v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem contDiff_opS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (opS f) :=
  contDiff_fst.smul (contDiff_pd hf (1, 0, 0))

private theorem contDiff_opK {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (opK f) :=
  ((contDiff_const.smul (contDiff_opS hf)).add
    (contDiff_snd.snd.smul (contDiff_pd hf (0, 0, 1))))

private theorem contDiff_opLam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (opLam f) :=
  (contDiff_opK hf).add hf

private theorem contDiff_opQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) {f : Profile → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (opQ ε f) :=
  (contDiff_pd hf (0, 1, 0)).sub (contDiff_const.smul (contDiff_opLam hf))

private theorem continuous_opE {f : Profile → MeridC} (hf : ContDiff ℝ ∞ f) :
    Continuous (opE f) := by
  have h0 : Continuous (fun p => f p 0) :=
    (EuclideanSpace.proj 0 : MeridC →L[ℂ] ℂ).continuous.comp hf.continuous
  unfold opE
  refine (PiLp.continuous_toLp 2 _).comp ?_
  exact Continuous.matrixVecCons h0 (Continuous.matrixVecCons continuous_const continuous_const)

private theorem vanish_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} {p : Profile} (h : ∀ᶠ y in nhds p, f y = 0) (v : Profile) :
    fderiv ℝ f p v = 0 := by
  have h' : f =ᶠ[nhds p] fun _ => (0 : E) := h
  rw [h'.fderiv_eq]
  simp

private theorem vanish_opQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) {f : Profile → E} {p : Profile} (h : ∀ᶠ y in nhds p, f y = 0) :
    opQ ε f p = 0 := by
  have h0 : f p = 0 := h.self_of_nhds
  simp [opQ, opK, opS, pdQ, pdS, pdEta, vanish_fderiv h, h0]

/-- Any continuous `MeridC`-valued profile that vanishes outside `dtdBand s0 s1 L` (`s0 > 0`)
belongs to `L²(measureH c)`. -/
theorem memLp_of_continuous_of_vanish_off_dtdBand {c : ℝ} (s0 s1 L : ℝ) (hs0 : 0 < s0)
    {f : Profile → MeridC} (hfc : Continuous f)
    (hsupp : ∀ p, p ∉ dtdBand s0 s1 L → f p = 0) :
    MemLp f 2 (measureH c) := by
  obtain ⟨Bd, hBd⟩ := (dtdBox_compact s0 s1 c L).exists_bound_of_continuousOn hfc.continuousOn
  have hdm : MeasurableSet (dtdBox s0 s1 c L) :=
    (dtdBox_compact s0 s1 c L).isClosed.measurableSet
  have hfin : measureH c (dtdBox s0 s1 c L) < ⊤ := by
    unfold measureH
    rw [withDensity_apply _ hdm]
    have hmono : ∫⁻ x in dtdBox s0 s1 c L, weightH x ∂(cellMeasure c) ≤
        ∫⁻ x in dtdBox s0 s1 c L, ENNReal.ofReal (s0 ^ (-(3 / 2 : ℝ))) ∂(cellMeasure c) := by
      apply setLIntegral_mono' hdm
      intro x hx
      have hx1 : s0 ≤ x.1 := by
        simp only [dtdBox, Set.mem_prod, Set.mem_Icc] at hx
        exact hx.1.1
      unfold weightH
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hs0 hx1 (by norm_num))
    refine lt_of_le_of_lt hmono ?_
    rw [setLIntegral_const]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    unfold cellMeasure
    exact lt_of_le_of_lt (Measure.le_iff'.mp Measure.restrict_le_self _)
      (dtdBox_compact s0 s1 c L).measure_lt_top
  have hcellm : MeasurableSet (cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hcell : ∀ᵐ x ∂(measureH c), x ∈ cell c := by
    unfold measureH cellMeasure
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hcellm)
  have hMem : MemLp f 2 ((measureH c).restrict (dtdBox s0 s1 c L)) := by
    have : IsFiniteMeasure ((measureH c).restrict (dtdBox s0 s1 c L)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    exact MemLp.of_bound hfc.aestronglyMeasurable Bd
      (ae_restrict_of_forall_mem hdm fun x hx => hBd x hx)
  have hind : f =ᵐ[measureH c] (dtdBox s0 s1 c L).indicator f := by
    filter_upwards [hcell] with x hx
    by_cases hxC : x ∈ dtdBox s0 s1 c L
    · rw [Set.indicator_of_mem hxC]
    · rw [Set.indicator_of_notMem hxC]
      apply hsupp x
      intro hB
      apply hxC
      obtain ⟨h1, h2, h3⟩ := hB
      simp only [cell, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioc, Set.mem_univ] at hx
      exact ⟨⟨h1, h2⟩, ⟨hx.2.1.1.le, hx.2.1.2⟩, abs_le.mp h3⟩
  exact ((memLp_indicator_iff_restrict hdm).mpr hMem).ae_eq hind.symm

/-- A smooth meridional test `u` (`IsMeridTest c u`) belongs to `L²(measureH c)`. -/
theorem memLp_isMeridTest {c : ℝ} {u : Profile → MeridC} (hu : IsMeridTest c u) :
    MemLp u 2 (measureH c) := by
  obtain ⟨s0, s1, L, hs0, hband⟩ := hu.band
  refine memLp_of_continuous_of_vanish_off_dtdBand s0 s1 L hs0 hu.smooth.continuous fun p hp => ?_
  by_contra hne
  exact hp ⟨(hband p hne).1.1, (hband p hne).1.2, (hband p hne).2⟩

/-- For a smooth meridional test `u` (`IsMeridTest c u`), `μ • u - AepsVecC ν ε u` belongs to
`L²(measureH c)`. -/
theorem memLp_mu_sub_AepsVecC {c : ℝ} (ν ε : ℝ) (μ : ℂ) {u : Profile → MeridC}
    (hu : IsMeridTest c u) :
    MemLp (fun p => μ • u p - AepsVecC ν ε u p) 2 (measureH c) := by
  obtain ⟨s0, s1, L, hs0, hband⟩ := hu.band
  have hcontA : Continuous (AepsVecC ν ε u) := by
    have hS := (contDiff_opS hu.smooth).continuous
    have hQ2 := (contDiff_opQ ε (contDiff_opQ ε hu.smooth)).continuous
    have hEta2 := (contDiff_pd (contDiff_pd hu.smooth (0, 0, 1)) (0, 0, 1)).continuous
    have hE : Continuous (fun p => (ε ^ 2 : ℝ) • opE u p) :=
      (continuous_opE hu.smooth).const_smul (ε ^ 2)
    unfold AepsVecC pdEta
    exact hS.neg.add ((continuous_const.mul continuous_fst).smul ((hQ2.add hEta2).sub hE))
  have hcont : Continuous (fun p => μ • u p - AepsVecC ν ε u p) :=
    (hu.smooth.continuous.const_smul μ).sub hcontA
  refine memLp_of_continuous_of_vanish_off_dtdBand s0 s1 L hs0 hcont fun p hp => ?_
  have hev : ∀ᶠ y in nhds p, u y = 0 := by
    filter_upwards [(dtdBand_closed s0 s1 L).isOpen_compl.mem_nhds hp] with y hy
    by_contra hne
    exact hy ⟨(hband y hne).1.1, (hband y hne).1.2, (hband y hne).2⟩
  have hu0 : u p = 0 := hev.self_of_nhds
  have hQev : ∀ᶠ y in nhds p, opQ ε u y = 0 :=
    hev.eventually_nhds.mono fun y hy => vanish_opQ ε hy
  have hEtaev : ∀ᶠ y in nhds p, pdEta u y = 0 :=
    hev.eventually_nhds.mono fun y hy => vanish_fderiv hy (0, 0, 1)
  have hS0 : opS u p = 0 := by simp [opS, pdS, vanish_fderiv hev]
  have hQ20 : opQ ε (opQ ε u) p = 0 := vanish_opQ ε hQev
  have hEta20 : pdEta (pdEta u) p = 0 := vanish_fderiv hEtaev (0, 0, 1)
  have hE0 : opE u p = 0 := by
    ext i
    fin_cases i <;> simp [opE, hu0]
  simp [AepsVecC, hu0, hS0, hQ20, hEta20, hE0]

/-- For a smooth meridional test `u` (`IsMeridTest c u`), `genDiffC ν ε u` belongs to
`L²(measureH c)`. -/
theorem memLp_genDiffC_isMeridTest {c : ℝ} (ν ε : ℝ) {u : Profile → MeridC}
    (hu : IsMeridTest c u) :
    MemLp (genDiffC ν ε u) 2 (measureH c) := by
  have h1 := memLp_mu_sub_AepsVecC ν 0 0 hu
  have h2 := memLp_mu_sub_AepsVecC ν ε 0 hu
  have heq : genDiffC ν ε u =
      (fun p => (0 : ℂ) • u p - AepsVecC ν 0 u p) -
        (fun p => (0 : ℂ) • u p - AepsVecC ν ε u p) := by
    funext p
    simp only [Pi.sub_apply, zero_smul, zero_sub]
    rw [← AepsVecC_sub_eq_genDiffC ν ε (hu.smooth.contDiffAt.of_le (by simp))]
    abel
  rw [heq]
  exact h1.sub h2

/-! ### 4. Leaf propositions for `AdjointResidualEq` and assembly -/

/-- **Leaf 1 (`FlatAdjointWeakEq`, task `PartII-a:N04/3/1`)**: weak flat resolvent identity for
`T0flat.adjoint Z` (source lines 1842–1843). Since `T0flat hc ν μ = B0225.R0 hc ν μ ∘L PepsC 0 c`,
`PepsC 0 c` commutes with `B0225.R0 hc ν μ`, and `B0225.R0 hc ν μ ((μ - A_0) u) = u` on smooth
meridional tests `u`, taking inner products with `Z` yields
`⟨(μ - A_0) u, T0flat.adjoint Z⟩_H = ⟨u, PepsC 0 c Z⟩_H`. -/
def FlatAdjointWeakEq : Prop :=
  ∀ (ν c : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ Z : HSpace c MeridC, ∀ (u : Profile → MeridC) (U AU0 : HSpace c MeridC),
      IsMeridTest c u →
      (U : Profile → MeridC) =ᵐ[measureH c] u →
      (AU0 : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν 0 u p) →
      inner ℂ AU0 (ContinuousLinearMap.adjoint (T0flat hc ν μ) Z) =
        inner ℂ U (PepsC 0 c Z)

/-- Helper reduction for `FlatAdjointWeakEq`: once `T0flat hc ν μ AU0 = PepsC 0 c U` on smooth
meridional tests `u` (from commutation `T0flat = PepsC 0 c ∘ R0` and left-inverse `R0 AU0 = U`),
`FlatAdjointWeakEq` follows immediately by self-adjointness of `PepsC 0 c` (`adjoint_PepsC`). -/
theorem flatAdjointWeakEq_of_apply
    (hApply : ∀ (ν c : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
      ∀ (u : Profile → MeridC) (U AU0 : HSpace c MeridC),
        IsMeridTest c u →
        (U : Profile → MeridC) =ᵐ[measureH c] u →
        (AU0 : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν 0 u p) →
        T0flat hc ν μ AU0 = PepsC 0 c U) :
    FlatAdjointWeakEq := by
  intro ν c hc hν μ hγ Z u U AU0 hu hU hAU0
  rw [ContinuousLinearMap.adjoint_inner_right, hApply ν c hc hν μ hγ u U AU0 hu hU hAU0,
    ← ContinuousLinearMap.adjoint_inner_right, adjoint_PepsC]

/-- **Leaf 2 (`GenDiffIBP`, task `PartII-a:N04/3/2`)**: integration by parts of the generator
difference `A_ε - A_0` on `measureH c` (source lines 1838–1840). Since `s^{1/2} Λ s^{-1/2}` and
`∂_q` are skew-adjoint on `L²(s^{-3/2} ds dq dη)`, `s Λ` and `∂_q` are skew-symmetric on
`measureH c`, so `A_ε - A_0` is formally symmetric on `H`: for any smooth meridional test `u`
(`IsMeridTest c u`, compactly supported in `(0, ∞) × ℝ/cℤ × ℝ`) and any `c`-periodic smooth profile
`v` on `{s > 0}` with `genDiff1 ν v, genDiff2 ν v ∈ L²(measureH c)`,
`⟨genDiffC ν ε u, V⟩_H = ⟨U, genDiffC ν ε v⟩_H`. -/
def GenDiffIBP : Prop :=
  ∀ (ν c ε : ℝ), 0 < ν → 0 < c →
    ∀ (u v : Profile → MeridC) (U DU V : HSpace c MeridC),
      IsMeridTest c u →
      (U : Profile → MeridC) =ᵐ[measureH c] u →
      (DU : Profile → MeridC) =ᵐ[measureH c] genDiffC ν ε u →
      ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1} → QPeriodic c v →
      (V : Profile → MeridC) =ᵐ[measureH c] v →
      ∀ (h1 : MemLp (genDiff1 ν v) 2 (measureH c))
        (h2 : MemLp (genDiff2 ν v) 2 (measureH c)),
        inner ℂ DU V = inner ℂ U ((memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v))

/-- **Leaf 3 (`RepsVecAdjointOfWeakEq`, task `PartII-a:N04/3/3`)**: weak characterization of
`RepsVec.adjoint R0` via smooth meridional tests (source lines 1842–1845). Since
`RepsVec hν hε hc hP μ` is the resolvent `(μ - A_ε^vec)⁻¹` on `HSpace c MeridC` and `(μ - A_ε^vec)`
on `IsMeridTest c` has dense range in `HSpace c MeridC` (`RepsVec (μ • u - AepsVecC ν ε u) = u`),
any `V, R0 ∈ H` satisfying `⟨(μ - A_ε^vec) u, V⟩_H = ⟨u, R0⟩_H` for all smooth meridional tests `u`
satisfy `V = RepsVec.adjoint R0`. -/
def RepsVecAdjointOfWeakEq : Prop :=
  ∀ (ν c ε : ℝ) (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε), ε ≤ 1 →
    ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
      ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
        ∀ V R0 : HSpace c MeridC,
          (∀ (u : Profile → MeridC) (U AUε : HSpace c MeridC),
            IsMeridTest c u →
            (U : Profile → MeridC) =ᵐ[measureH c] u →
            (AUε : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν ε u p) →
            inner ℂ AUε V = inner ℂ U R0) →
          V = ContinuousLinearMap.adjoint (B0223.RepsVec hν hε hc hP μ) R0

/-- Helper reduction for `RepsVecAdjointOfWeakEq`: from the left-inverse identity
`RepsVec AUε = U` on `IsMeridTest c u` and vanishing of vectors orthogonal to all `AUε`. -/
theorem repsVecAdjointOfWeakEq_of_left_and_ortho
    (hLeft : ∀ (ν c ε : ℝ) (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε), ε ≤ 1 →
      ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
          ∀ (u : Profile → MeridC) (U AUε : HSpace c MeridC),
            IsMeridTest c u →
            (U : Profile → MeridC) =ᵐ[measureH c] u →
            (AUε : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν ε u p) →
            B0223.RepsVec hν hε hc hP μ AUε = U)
    (hOrtho : ∀ (ν c ε : ℝ), 0 < ν → 0 < c → 0 < ε → ε ≤ 1 →
      ∀ (P : ℝ) [Fact (0 < P)], P = 2 * ε * c → P ≤ 1 →
        ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
          ∀ W : HSpace c MeridC,
            (∀ (u : Profile → MeridC) (AUε : HSpace c MeridC),
              IsMeridTest c u →
              (AUε : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν ε u p) →
              inner ℂ AUε W = 0) →
            W = 0) :
    RepsVecAdjointOfWeakEq := by
  intro ν c ε hν hc hε hε1 P _ hP hP1 μ hγ V R0 hweak
  rw [← sub_eq_zero]
  refine hOrtho ν c ε hν hc hε hε1 P hP hP1 μ hγ
    (V - ContinuousLinearMap.adjoint (B0223.RepsVec hν hε hc hP μ) R0) ?_
  intro u AUε hu hAUε
  have hU_mem : MemLp u 2 (measureH c) := memLp_isMeridTest hu
  set U : HSpace c MeridC := hU_mem.toLp u
  rw [inner_sub_right, hweak u U AUε hu hU_mem.coeFn_toLp hAUε,
    ContinuousLinearMap.adjoint_inner_right,
    hLeft ν c ε hν hc hε hε1 P hP hP1 μ hγ u U AUε hu hU_mem.coeFn_toLp hAUε, sub_self]

/-- Reduction of `AdjointResidualEq` (`PartII-a:N04/3`) to the three leaf propositions
`FlatAdjointWeakEq`, `GenDiffIBP`, and `RepsVecAdjointOfWeakEq`. -/
theorem adjointResidualEq_of (hFlat : FlatAdjointWeakEq) (hIBP : GenDiffIBP)
    (hWeak : RepsVecAdjointOfWeakEq) : AdjointResidualEq := by
  intro ν c σ H1 L1 hν hc _hσ _hσH1 _hL1 ε hε hε1 P _ hP hP1 μ hγ z v Z _hz _hsupp _hZ
    hv_smooth hv_per _hv_supp hV h1 h2
  rw [sub_apply, adjoint_Teps_eq hν hε hc hP hγ Z]
  set GD : HSpace c MeridC := (memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v)
  suffices hT0 : ContinuousLinearMap.adjoint (T0flat hc ν μ) Z =
      ContinuousLinearMap.adjoint (B0223.RepsVec hν hε hc hP μ) (PepsC 0 c Z - GD) by
    rw [hT0, ← map_sub]
    congr 1
    simp only [sub_apply]
    abel
  refine hWeak ν c ε hν hc hε hε1 P hP hP1 μ hγ
    (ContinuousLinearMap.adjoint (T0flat hc ν μ) Z) (PepsC 0 c Z - GD) ?_
  intro u U AUε hu hU hAUε
  have hAU0_mem : MemLp (fun p => μ • u p - AepsVecC ν 0 u p) 2 (measureH c) :=
    memLp_mu_sub_AepsVecC ν 0 μ hu
  have hDU_mem : MemLp (genDiffC ν ε u) 2 (measureH c) :=
    memLp_genDiffC_isMeridTest ν ε hu
  set AU0 : HSpace c MeridC := hAU0_mem.toLp (fun p => μ • u p - AepsVecC ν 0 u p)
  set DU : HSpace c MeridC := hDU_mem.toLp (genDiffC ν ε u)
  have hdecomp : AUε = AU0 - DU := by
    apply Lp.ext
    filter_upwards [hAUε, Lp.coeFn_sub AU0 DU, hAU0_mem.coeFn_toLp, hDU_mem.coeFn_toLp]
      with p hp1 hp2 hp3 hp4
    rw [hp1, hp2, Pi.sub_apply, hp3, hp4]
    exact mu_sub_AepsVecC_eq ν ε μ (hu.smooth.contDiffAt.of_le (by simp))
  rw [hdecomp, inner_sub_left, inner_sub_right,
    hFlat ν c hc hν μ hγ Z u U AU0 hu hU hAU0_mem.coeFn_toLp,
    hIBP ν c ε hν hc u v U DU (ContinuousLinearMap.adjoint (T0flat hc ν μ) Z)
      hu hU hDU_mem.coeFn_toLp hv_smooth hv_per hV h1 h2]

end UnforcedLeray.Short.PartIIa
