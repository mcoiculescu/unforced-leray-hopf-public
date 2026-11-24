import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen1Bound.OuterBounds

/-!


Source of record: `the November 2 reference manuscript`,
lines 1809–1835 (Lemma `near:adjoint-polynomial`, step 2).

Proves `flatAdjointGen1Bound : FlatAdjointGen1Bound`:
1. `genDiff1 ν (flatAdjointRep ν μ h) ∈ L²(measureH c)` with norm bounded by a polynomial in
   `GammaBox ν c σ H1 L1 M γs` times `flatProjMomentNorm c h`.
2. `gradDiff1 (flatAdjointRep ν μ h) ∈ L²(measureHT c)` with norm bounded by a polynomial in
   `GammaBox ν c σ H1 L1 M γs` times `flatProjMomentNorm c h`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0226
open FlatAdjointElemAux

namespace Gen1BoundProof

/-! ### 1. Pointwise and `L²(measureH c)` bounds for `genDiff1 ν (flatAdjointRep ν μ h)` -/

theorem genDiff1_flatAdjointRep_eq_on_pos {c σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    {p : Profile} (hp : 0 < p.1) :
    genDiff1 ν (flatAdjointRep ν μ h) p = (ν * p.1) • opLamRep ν μ (pdQ h) p := by
  have hopen : IsOpen {q : Profile | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  have hev : pdQ (flatAdjointRep ν μ h) =ᶠ[𝓝 p]
      causalAdjointRep ν μ (thetaWeight 0) (pdQ h) := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    rw [← causalAdjointRep_thetaWeight_zero]
    exact pdQ_causalAdjointRep hν hσ hσH1 hμ 0 (isDiffProfile_base hh) hq
  have hopLam : opLam (pdQ (flatAdjointRep ν μ h)) p =
      opLam (causalAdjointRep ν μ (thetaWeight 0) (pdQ h)) p := by
    simp only [opLam, opK, opS, pdS, pdEta, hev.fderiv_eq, hev.self_of_nhds]
  rw [genDiff1, hopLam,
    opLam_causalAdjointRep_eq_opLamRep hν hσ hσH1 hμ (isDiffProfile_pdQ hh)
      (bdd_etaMul_of_isBaseDeriv hh (isBaseDeriv_pdEta_pdQ hh 0 (by decide))) hp]

theorem memLp_opLamRep_pdQ {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    MemLp (opLamRep ν μ (pdQ h)) 2 (measureH c) := by
  have hwS : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 1 1 (opS (pdQ h)) := by
    rw [opS_pdQ_comm hh.smooth]
    exact isBaseDeriv_pdQ hh 1 (by decide)
  exact memLp_opLamRep hc hν hσ hσH1 hγs hμγ hh
    (contDiff_pdQ hh.smooth) (periodic_pdQ hh.periodic)
    (isBaseDeriv_pdQ hh 0 (by decide)) hwS
    (isBaseDeriv_pdQ3 hh 0 (by decide))
    (isBaseDeriv_pdEta_pdQ hh 0 (by decide))
    (isBaseDeriv_pdEta_pdEta_pdQ hh 0 (by decide))

theorem norm_toLp_opLamRep_pdQ_le {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    ‖(memLp_opLamRep_pdQ hc hν hσ hσH1 hγs hμγ hh).toLp (opLamRep ν μ (pdQ h))‖ ≤
      (4 + 6 * (ν * H1)) * γs⁻¹ * flatProjMomentNorm c h := by
  have hwS : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 1 1 (opS (pdQ h)) := by
    rw [opS_pdQ_comm hh.smooth]
    exact isBaseDeriv_pdQ hh 1 (by decide)
  exact norm_toLp_opLamRep_le hc hν hσ hσH1 hγs hμγ hh
    (contDiff_pdQ hh.smooth) (periodic_pdQ hh.periodic)
    (isBaseDeriv_pdQ hh 0 (by decide)) hwS
    (isBaseDeriv_pdQ3 hh 0 (by decide))
    (isBaseDeriv_pdEta_pdQ hh 0 (by decide))
    (isBaseDeriv_pdEta_pdEta_pdQ hh 0 (by decide))

theorem memLp_genDiff1_flatAdjointRep {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    MemLp (genDiff1 ν (flatAdjointRep ν μ h)) 2 (measureH c) :=
  memLp_of_eqOn_pos_nuSMul_one hν (hσ.trans_le hσH1)
    (memLp_opLamRep_pdQ hc hν hσ hσH1 hγs hμγ hh)
    (fun _ hp => opLamRep_eq_zero_of_H1_lt hσ hσH1 ν μ (isDiffProfile_pdQ hh) hp)
    (fun _ hp => genDiff1_flatAdjointRep_eq_on_pos hν hσ hσH1 (hγs.trans_le hμγ) hh hp)

theorem norm_toLp_genDiff1_flatAdjointRep_le {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    ‖(memLp_genDiff1_flatAdjointRep hc hν hσ hσH1 hγs hμγ hh).toLp
      (genDiff1 ν (flatAdjointRep ν μ h))‖ ≤
      (ν * H1) * ((4 + 6 * (ν * H1)) * γs⁻¹ * flatProjMomentNorm c h) := by
  refine (norm_toLp_of_eqOn_pos_nuSMul_one_le hν (hσ.trans_le hσH1)
    (memLp_opLamRep_pdQ hc hν hσ hσH1 hγs hμγ hh)
    (fun _ hp => opLamRep_eq_zero_of_H1_lt hσ hσH1 ν μ (isDiffProfile_pdQ hh) hp)
    (fun _ hp => genDiff1_flatAdjointRep_eq_on_pos hν hσ hσH1 (hγs.trans_le hμγ) hh hp)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (norm_toLp_opLamRep_pdQ_le hc hν hσ hσH1 hγs hμγ hh)
    (mul_pos hν (hσ.trans_le hσH1)).le

/-! ### 2. Pointwise and `L²(measureHT c)` bounds for `gradDiff1 (flatAdjointRep ν μ h)` -/

theorem proj_opLam {v : Profile → MeridC} {p : Profile} (hv : DifferentiableAt ℝ v p) (i : Fin 2) :
    opLam (fun q => v q i) p = (opLam v p) i := by
  set P : MeridC →L[ℝ] ℂ := (EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ
  have hfd : ∀ w : Profile, fderiv ℝ (fun q => v q i) p w = (fderiv ℝ v p w) i := by
    intro w
    have h : HasFDerivAt (fun q => P (v q)) (P.comp (fderiv ℝ v p)) p :=
      P.hasFDerivAt.comp p hv.hasFDerivAt
    exact congrArg (fun L : Profile →L[ℝ] ℂ => L w) h.fderiv
  simp only [opLam, opK, opS, pdS, pdEta, PiLp.add_apply, PiLp.smul_apply, hfd]

/-- Continuous linear lift `(u_0, u_1) ↦ (u_0, u_1, 0, 0)` from `MeridC` to `TensorVal`. -/
def tensorLift01 : MeridC →L[ℂ] TensorVal :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (WithLp.toLp 2 ![1, 0, 0, 0])).comp
    (EuclideanSpace.proj 0) +
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (WithLp.toLp 2 ![0, 1, 0, 0])).comp
    (EuclideanSpace.proj 1)

/-- Continuous linear lift `(v_0, v_1) ↦ (0, 0, 0, -v_0)` from `MeridC` to `TensorVal`. -/
def tensorLift3 : MeridC →L[ℂ] TensorVal :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (WithLp.toLp 2 ![0, 0, 0, -1])).comp
    (EuclideanSpace.proj 0)

theorem tensorLift_add_eq (u v : MeridC) :
    tensorLift01 u + tensorLift3 v = WithLp.toLp 2 ![u 0, u 1, 0, -(v 0)] := by
  ext i
  fin_cases i <;> simp [tensorLift01, tensorLift3, EuclideanSpace.proj]

theorem norm_tensorLift_add_le (u v : MeridC) :
    ‖tensorLift01 u + tensorLift3 v‖ ≤ ‖u‖ + ‖v‖ := by
  rw [tensorLift_add_eq]
  set x : TensorVal := WithLp.toLp 2 ![u 0, u 1, 0, -(v 0)]
  have hx : ‖x‖ ^ 2 = ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2 + ‖-(v 0)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_four]
    rfl
  have hu : ‖u‖ ^ 2 = ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have hv : ‖v‖ ^ 2 = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have hsq : ‖x‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    have h1 : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg u) (norm_nonneg v)
    have h2 : 0 ≤ ‖v 1‖ ^ 2 := sq_nonneg _
    rw [norm_zero, norm_neg] at hx
    nlinarith
  exact (abs_le_of_sq_le_sq' hsq (add_nonneg (norm_nonneg u) (norm_nonneg v))).2

/-- Explicit causal representation of `gradDiff1 (flatAdjointRep ν μ h)` on `{p | 0 < p.1}`. -/
def gradDiff1Rep (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) (p : Profile) : TensorVal :=
  tensorLift01 (opLamRep ν μ h p) + tensorLift3 (causalAdjointRep ν μ (thetaWeight 0) h p)

theorem gradDiff1_flatAdjointRep_eq_on_pos {c σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    {p : Profile} (hp : 0 < p.1) :
    gradDiff1 (flatAdjointRep ν μ h) p = gradDiff1Rep ν μ h p := by
  have hd : DifferentiableAt ℝ (flatAdjointRep ν μ h) p := by
    rw [← causalAdjointRep_thetaWeight_zero]
    exact differentiableAt_causalAdjointRep hν hσ hσH1 hμ 0 (isDiffProfile_base hh) hp
  have h0 := proj_opLam hd 0
  have h1 := proj_opLam hd 1
  have hlam : opLam (flatAdjointRep ν μ h) p = opLamRep ν μ h p := by
    rw [← causalAdjointRep_thetaWeight_zero]
    exact opLam_causalAdjointRep_eq_opLamRep hν hσ hσH1 hμ (isDiffProfile_base hh)
      (bdd_etaMul_of_isBaseDeriv hh (isBaseDeriv_pdEta hh 0 (by decide))) hp
  unfold gradDiff1 gradDiff1Rep
  rw [tensorLift_add_eq, h0, h1, hlam, ← causalAdjointRep_thetaWeight_zero]

theorem gradDiff1Rep_eq_zero_of_H1_lt {c σ H1 : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (ν : ℝ) (μ : ℂ) {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    {p : Profile} (hp : H1 < p.1) :
    gradDiff1Rep ν μ h p = 0 := by
  unfold gradDiff1Rep
  rw [opLamRep_eq_zero_of_H1_lt hσ hσH1 ν μ (isDiffProfile_base hh) hp,
    causalAdjointRep_eq_zero_of_support_s hσ hσH1 ν μ (thetaWeight 0) hh.support_s hp,
    map_zero, map_zero, add_zero]

theorem memLp_opLamRep_base {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    MemLp (opLamRep ν μ h) 2 (measureH c) :=
  memLp_opLamRep hc hν hσ hσH1 hγs hμγ hh hh.smooth hh.periodic
    (isBaseDeriv_base hh 0 (by decide))
    (isBaseDeriv_base hh 1 (by decide))
    (isBaseDeriv_pdQ_pdQ hh 0 (by decide))
    (isBaseDeriv_pdEta hh 0 (by decide))
    (isBaseDeriv_pdEta_pdEta hh 0 (by decide))

theorem norm_toLp_opLamRep_base_le {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    ‖(memLp_opLamRep_base hc hν hσ hσH1 hγs hμγ hh).toLp (opLamRep ν μ h)‖ ≤
      (4 + 6 * (ν * H1)) * γs⁻¹ * flatProjMomentNorm c h :=
  norm_toLp_opLamRep_le hc hν hσ hσH1 hγs hμγ hh hh.smooth hh.periodic
    (isBaseDeriv_base hh 0 (by decide))
    (isBaseDeriv_base hh 1 (by decide))
    (isBaseDeriv_pdQ_pdQ hh 0 (by decide))
    (isBaseDeriv_pdEta hh 0 (by decide))
    (isBaseDeriv_pdEta_pdEta hh 0 (by decide))

theorem memLp_gradDiff1Rep_measureH {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    MemLp (gradDiff1Rep ν μ h) 2 (measureH c) := by
  have mU := memLp_opLamRep_base hc hν hσ hσH1 hγs hμγ hh
  have mV : MemLp (causalAdjointRep ν μ (thetaWeight 0) h) 2 (measureH c) := by
    simpa [nuSMul_zero] using
      memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh (isBaseDeriv_base hh 0 (by decide))
        (j := 0) (by decide) 0 0
  have hmeas : AEStronglyMeasurable (gradDiff1Rep ν μ h) (measureH c) :=
    (tensorLift01.continuous.comp_aestronglyMeasurable mU.1).add
      (tensorLift3.continuous.comp_aestronglyMeasurable mV.1)
  refine (mU.norm.add mV.norm).mono hmeas (Eventually.of_forall fun p => ?_)
  dsimp only [gradDiff1Rep, Pi.add_apply]
  have hnn : 0 ≤ ‖opLamRep ν μ h p‖ + ‖causalAdjointRep ν μ (thetaWeight 0) h p‖ := by positivity
  rw [Real.norm_of_nonneg hnn]
  exact norm_tensorLift_add_le _ _

theorem norm_toLp_gradDiff1Rep_measureH_le {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    ‖(memLp_gradDiff1Rep_measureH hc hν hσ hσH1 hγs hμγ hh).toLp (gradDiff1Rep ν μ h)‖ ≤
      (5 + 6 * (ν * H1)) * γs⁻¹ * flatProjMomentNorm c h := by
  set mU := memLp_opLamRep_base hc hν hσ hσH1 hγs hμγ hh
  set mV : MemLp (causalAdjointRep ν μ (thetaWeight 0) h) 2 (measureH c) := by
    simpa [nuSMul_zero] using
      memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh (isBaseDeriv_base hh 0 (by decide))
        (j := 0) (by decide) 0 0
  have hle_ae : ∀ᵐ p ∂(measureH c), ‖gradDiff1Rep ν μ h p‖ ≤
      ‖((fun q => ‖opLamRep ν μ h q‖) + fun q => ‖causalAdjointRep ν μ (thetaWeight 0) h q‖) p‖ := by
    refine Eventually.of_forall fun p => ?_
    dsimp only [gradDiff1Rep, Pi.add_apply]
    rw [Real.norm_of_nonneg (by positivity)]
    exact norm_tensorLift_add_le _ _
  have he : eLpNorm (gradDiff1Rep ν μ h) 2 (measureH c) ≤
      eLpNorm ((fun q => ‖opLamRep ν μ h q‖) + fun q => ‖causalAdjointRep ν μ (thetaWeight 0) h q‖)
        2 (measureH c) := eLpNorm_mono_ae hle_ae
  have h1 : ‖(memLp_gradDiff1Rep_measureH hc hν hσ hσH1 hγs hμγ hh).toLp (gradDiff1Rep ν μ h)‖ ≤
      ‖(mU.norm.add mV.norm).toLp
        ((fun q => ‖opLamRep ν μ h q‖) + fun q => ‖causalAdjointRep ν μ (thetaWeight 0) h q‖)‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    exact ENNReal.toReal_mono (mU.norm.add mV.norm).2.ne he
  have h2 := norm_toLp_add_le mU.norm mV.norm
  have h3 : ‖mU.norm.toLp (fun q => ‖opLamRep ν μ h q‖)‖ = ‖mU.toLp (opLamRep ν μ h)‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm]
  have h4 : ‖mV.norm.toLp (fun q => ‖causalAdjointRep ν μ (thetaWeight 0) h q‖)‖ =
      ‖mV.toLp (causalAdjointRep ν μ (thetaWeight 0) h)‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm]
  have hU_le := norm_toLp_opLamRep_base_le hc hν hσ hσH1 hγs hμγ hh
  have hV_le : ‖mV.toLp (causalAdjointRep ν μ (thetaWeight 0) h)‖ ≤
      γs⁻¹ * flatProjMomentNorm c h := by
    simpa [nuSMul_zero] using
      norm_causal_baseDeriv_le hc hν hσ hσH1 hγs hμγ hh (isBaseDeriv_base hh 0 (by decide))
        (j := 0) (by decide) 0 0
  linarith

theorem memLp_gradDiff1_flatAdjointRep {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    MemLp (gradDiff1 (flatAdjointRep ν μ h)) 2 (measureHT c) := by
  have hm := memLp_measureHT_of_support_H1 (hσ.trans_le hσH1)
    (memLp_gradDiff1Rep_measureH hc hν hσ hσH1 hγs hμγ hh)
    (fun p hp => gradDiff1Rep_eq_zero_of_H1_lt hσ hσH1 ν μ hh hp)
  refine hm.ae_eq ?_
  filter_upwards [(measureHT_ac_measureH c).ae_le (ae_pos_of_measureH c)] with p hp
  exact (gradDiff1_flatAdjointRep_eq_on_pos hν hσ hσH1 (hγs.trans_le hμγ) hh hp).symm

theorem norm_toLp_gradDiff1_flatAdjointRep_le {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    ‖(memLp_gradDiff1_flatAdjointRep hc hν hσ hσH1 hγs hμγ hh).toLp
      (gradDiff1 (flatAdjointRep ν μ h))‖ ≤
      (1 + H1) * ((5 + 6 * (ν * H1)) * γs⁻¹ * flatProjMomentNorm c h) := by
  have hae : gradDiff1Rep ν μ h =ᵐ[measureHT c] gradDiff1 (flatAdjointRep ν μ h) := by
    filter_upwards [(measureHT_ac_measureH c).ae_le (ae_pos_of_measureH c)] with p hp
    exact (gradDiff1_flatAdjointRep_eq_on_pos hν hσ hσH1 (hγs.trans_le hμγ) hh hp).symm
  have hcongr : (memLp_gradDiff1_flatAdjointRep hc hν hσ hσH1 hγs hμγ hh).toLp
      (gradDiff1 (flatAdjointRep ν μ h)) =
      (memLp_measureHT_of_support_H1 (hσ.trans_le hσH1)
        (memLp_gradDiff1Rep_measureH hc hν hσ hσH1 hγs hμγ hh)
        (fun p hp => gradDiff1Rep_eq_zero_of_H1_lt hσ hσH1 ν μ hh hp)).toLp
      (gradDiff1Rep ν μ h) :=
    MemLp.toLp_congr _ _ hae.symm
  rw [hcongr]
  refine (norm_toLp_measureHT_le_of_support_H1 (hσ.trans_le hσH1)
    (memLp_gradDiff1Rep_measureH hc hν hσ hσH1 hγs hμγ hh)
    (fun p hp => gradDiff1Rep_eq_zero_of_H1_lt hσ hσH1 ν μ hh hp)).trans ?_
  have h1H : 0 ≤ 1 + H1 := by linarith [hσ.trans_le hσH1]
  exact mul_le_mul_of_nonneg_left
    (norm_toLp_gradDiff1Rep_measureH_le hc hν hσ hσH1 hγs hμγ hh) h1H

/-! ### 3. Polynomial `GammaBox` domination -/

theorem coeff_le_GammaBox_pow {ν c σ H1 L1 M γs : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1) (hM : 0 ≤ M) (hγs : 0 < γs) :
    (ν * H1) * ((4 + 6 * (ν * H1)) * γs⁻¹) +
      (1 + H1) * ((5 + 6 * (ν * H1)) * γs⁻¹) ≤
      21 * GammaBox ν c σ H1 L1 M γs ^ 5 := by
  set G := GammaBox ν c σ H1 L1 M γs
  have hH1 : 0 < H1 := hσ.trans_le hσH1
  have h1G : 1 ≤ G := one_le_GammaBox hν hc hσ hσH1 hL1 hM hγs
  have hG0 : 0 ≤ G := zero_le_one.trans h1G
  have hνG : ν ≤ G := by
    unfold G GammaBox
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    have : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
    have : 0 ≤ γs⁻¹ := inv_nonneg.2 hγs.le
    linarith
  have h1HG : 1 + H1 ≤ G := by
    unfold G GammaBox
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    have : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
    have : 0 ≤ γs⁻¹ := inv_nonneg.2 hγs.le
    linarith
  have hHG : H1 ≤ G := by linarith
  have hγG : γs⁻¹ ≤ G := inv_gammas_le_GammaBox ν c σ H1 L1 M γs hν hc hσ hσH1 hL1 hM
  have hνH : ν * H1 ≤ G ^ 2 := by
    calc ν * H1 ≤ G * G := mul_le_mul hνG hHG hH1.le hG0
      _ = G ^ 2 := (sq G).symm
  have h1G2 : 1 ≤ G ^ 2 := by nlinarith
  have h46 : 4 + 6 * (ν * H1) ≤ 10 * G ^ 2 := by linarith
  have h56 : 5 + 6 * (ν * H1) ≤ 11 * G ^ 2 := by linarith
  have hT1 : (ν * H1) * ((4 + 6 * (ν * H1)) * γs⁻¹) ≤ 10 * G ^ 5 := by
    have hp1 : (4 + 6 * (ν * H1)) * γs⁻¹ ≤ (10 * G ^ 2) * G :=
      mul_le_mul h46 hγG (inv_nonneg.2 hγs.le) (by positivity)
    have hp2 : (ν * H1) * ((4 + 6 * (ν * H1)) * γs⁻¹) ≤ G ^ 2 * ((10 * G ^ 2) * G) :=
      mul_le_mul hνH hp1 (by positivity) (by positivity)
    calc (ν * H1) * ((4 + 6 * (ν * H1)) * γs⁻¹)
        ≤ G ^ 2 * ((10 * G ^ 2) * G) := hp2
      _ = 10 * G ^ 5 := by ring
  have hT2 : (1 + H1) * ((5 + 6 * (ν * H1)) * γs⁻¹) ≤ 11 * G ^ 5 := by
    have hp1 : (5 + 6 * (ν * H1)) * γs⁻¹ ≤ (11 * G ^ 2) * G :=
      mul_le_mul h56 hγG (inv_nonneg.2 hγs.le) (by positivity)
    have hp2 : (1 + H1) * ((5 + 6 * (ν * H1)) * γs⁻¹) ≤ G * ((11 * G ^ 2) * G) :=
      mul_le_mul h1HG hp1 (by positivity) hG0
    have hpow45 : G ^ 4 ≤ G ^ 5 := pow_le_pow_right₀ h1G (by omega)
    calc (1 + H1) * ((5 + 6 * (ν * H1)) * γs⁻¹)
        ≤ G * ((11 * G ^ 2) * G) := hp2
      _ = 11 * G ^ 4 := by ring
      _ ≤ 11 * G ^ 5 := by linarith
  linarith

end Gen1BoundProof

open Gen1BoundProof

/-- **Leaf 2 (`FlatAdjointGen1Bound`, task `PartII-a:N04/2/2/2`)**: `L²` membership and
polynomial `GammaBox` bound for `genDiff1 ν (flatAdjointRep ν μ h)` in `L²(measureH c)` and
`gradDiff1 (flatAdjointRep ν μ h)` in `L²(measureHT c)`. -/
theorem flatAdjointGen1Bound : FlatAdjointGen1Bound := by
  refine ⟨5, 21, by norm_num, ?_⟩
  intro ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ h hh
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  refine ⟨memLp_genDiff1_flatAdjointRep hc hν hσ hσH1 hγs hμγ hh,
    memLp_gradDiff1_flatAdjointRep hc hν hσ hσH1 hγs hμγ hh, ?_⟩
  have h1 := norm_toLp_genDiff1_flatAdjointRep_le hc hν hσ hσH1 hγs hμγ hh
  have h2 := norm_toLp_gradDiff1_flatAdjointRep_le hc hν hσ hσH1 hγs hμγ hh
  have hcoeff := coeff_le_GammaBox_pow (L1 := L1) hc hν hσ hσH1 hL1 hM0 hγs
  have hF0 : 0 ≤ flatProjMomentNorm c h := flatProjMomentNorm_nonneg c h
  have hmul := mul_le_mul_of_nonneg_right hcoeff hF0
  linarith

end UnforcedLeray.Short.PartIIa
