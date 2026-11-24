import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen1Bound.GaussIBP
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivPt

/-!
# Spatial and Age Differentiation of `flatAdjointSlice` and `causalAdjointRep` (`SliceDerivs`)

Differentiates `q ↦ flatAdjointSlice ν μ w t q` at fixed `t > 0` and `q.1 > 0` under the planar
Gaussian integral, applies `gaussDt_lap_of_bdd` (`GaussIBP.lean`) to eliminate the `t → 0⁺`
singularity of `gaussDt 2 θ`, and differentiates `causalAdjointRep ν μ (thetaWeight k) w` under
the `t ∈ Ioi 0` integral to obtain exact formulas for `pdQ`, `pdEta`, `pdS`, and `opS`.
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

/-! ### 1. Coordinate projections on `Profile = ℝ × ℝ × ℝ` and `smulRightCLM` -/

theorem integrable_add_fun {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun a => f a + g a) μ :=
  hf.add hg

def fstProfileCLM : Profile →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

def snd1ProfileCLM : Profile →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

def snd2ProfileCLM : Profile →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

@[simp]
theorem fstProfileCLM_apply (p : Profile) : fstProfileCLM p = p.1 := rfl

@[simp]
theorem snd1ProfileCLM_apply (p : Profile) : snd1ProfileCLM p = p.2.1 := rfl

@[simp]
theorem snd2ProfileCLM_apply (p : Profile) : snd2ProfileCLM p = p.2.2 := rfl

theorem norm_fstProfileCLM_le : ‖fstProfileCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
  rw [one_mul, fstProfileCLM_apply]
  exact norm_fst_le p

theorem norm_snd1ProfileCLM_le : ‖snd1ProfileCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
  rw [one_mul, snd1ProfileCLM_apply]
  exact (norm_fst_le p.2).trans (norm_snd_le p)

theorem norm_snd2ProfileCLM_le : ‖snd2ProfileCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
  rw [one_mul, snd2ProfileCLM_apply]
  exact (norm_snd_le p.2).trans (norm_snd_le p)

def smulRightCLM (L : Profile →L[ℝ] ℝ) : MeridC →L[ℝ] (Profile →L[ℝ] MeridC) :=
  ContinuousLinearMap.smulRightL ℝ Profile MeridC L

@[simp]
theorem smulRightCLM_apply (L : Profile →L[ℝ] ℝ) (v : MeridC) :
    smulRightCLM L v = L.smulRight v := rfl

theorem norm_smulRight_le (L : Profile →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (v : MeridC) :
    ‖L.smulRight v‖ ≤ ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun dq => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left ((L.le_opNorm dq).trans (mul_le_of_le_one_left (norm_nonneg dq) hL))
    (norm_nonneg v)

theorem integral_smulRight {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (L : Profile →L[ℝ] ℝ) {f : α → MeridC} (hf : Integrable f μ) :
    ∫ a, L.smulRight (f a) ∂μ = L.smulRight (∫ a, f a ∂μ) :=
  (smulRightCLM L).integral_comp_comm hf

theorem profile_eq_sum_basis (dq : Profile) :
    dq = dq.1 • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) +
      dq.2.1 • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
      dq.2.2 • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
  ext <;> simp

theorem fderiv_profile_eq {w : Profile → MeridC} (z : Profile) :
    fderiv ℝ w z =
      fstProfileCLM.smulRight (pdS w z) +
      snd1ProfileCLM.smulRight (pdQ w z) +
      snd2ProfileCLM.smulRight (pdEta w z) := by
  refine ContinuousLinearMap.ext fun dq => ?_
  have hdq := congrArg (fun x : Profile => fderiv ℝ w z x) (profile_eq_sum_basis dq)
  simp only [map_add, map_smul] at hdq
  exact hdq

/-! ### 2. Bundled regularity and boundedness for differentiable source profiles -/

/-- A smooth band-supported profile with globally bounded derivatives `w, opS w, pdQ w, pdQ² w,
pdEta w, pdEta² w`. -/
structure IsDiffProfile (σ H1 : ℝ) (w : Profile → MeridC) : Prop where
  smooth : ContDiff ℝ ∞ w
  support_s : ∀ q : Profile, q.1 < σ ∨ H1 < q.1 → w q = 0
  bdd_w : ∃ M0 : ℝ, ∀ q, ‖w q‖ ≤ M0
  bdd_opS : ∃ MOS : ℝ, ∀ q, ‖opS w q‖ ≤ MOS
  bdd_pdQ : ∃ MQ1 : ℝ, ∀ q, ‖pdQ w q‖ ≤ MQ1
  bdd_pdQ2 : ∃ MQ2 : ℝ, ∀ q, ‖pdQ (pdQ w) q‖ ≤ MQ2
  bdd_pdEta : ∃ ME1 : ℝ, ∀ q, ‖pdEta w q‖ ≤ ME1
  bdd_pdEta2 : ∃ ME2 : ℝ, ∀ q, ‖pdEta (pdEta w) q‖ ≤ ME2

theorem IsDiffProfile.bdd_pdS {σ H1 : ℝ} (hσ : 0 < σ) {w : Profile → MeridC}
    (hw : IsDiffProfile σ H1 w) :
    ∃ MS : ℝ, ∀ q, ‖pdS w q‖ ≤ MS := by
  obtain ⟨MOS, hMOS⟩ := hw.bdd_opS
  refine ⟨σ⁻¹ * max MOS 0, fun q => ?_⟩
  by_cases hq : q.1 < σ ∨ H1 < q.1
  · rw [support_s_pdS hw.support_s q hq, norm_zero]
    positivity
  · rw [not_or, not_lt, not_lt] at hq
    have hq_pos : 0 < q.1 := hσ.trans_le hq.1
    have hpd : pdS w q = q.1⁻¹ • opS w q := by
      rw [opS, smul_smul, inv_mul_cancel₀ hq_pos.ne', one_smul]
    have hinv : q.1⁻¹ ≤ σ⁻¹ := inv_anti₀ hσ hq.1
    rw [hpd, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hq_pos.le)]
    exact mul_le_mul hinv ((hMOS q).trans (le_max_left MOS 0)) (norm_nonneg _) (by positivity)

theorem IsDiffProfile.bdd_laplaceQEta {σ H1 : ℝ} {w : Profile → MeridC}
    (hw : IsDiffProfile σ H1 w) :
    ∃ ML : ℝ, ∀ q, ‖laplaceQEta w q‖ ≤ ML := by
  obtain ⟨MQ2, hMQ2⟩ := hw.bdd_pdQ2
  obtain ⟨ME2, hME2⟩ := hw.bdd_pdEta2
  refine ⟨MQ2 + ME2, fun q => ?_⟩
  exact (norm_add_le _ _).trans (add_le_add (hMQ2 q) (hME2 q))

theorem IsDiffProfile.bdd_nuSMul_laplaceQEta {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w) :
    ∃ MNL : ℝ, ∀ q, ‖nuSMul ν 1 (laplaceQEta w) q‖ ≤ MNL :=
  bdd_nuSMul_of_support_s hν hσ hσH1 1 (support_s_laplaceQEta hw.support_s) hw.bdd_laplaceQEta

theorem bdd_of_isBaseDeriv {c σ H1 : ℝ} {h u : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) {a m : ℕ}
    (hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m u) :
    ∃ B : ℝ, ∀ q : Profile, ‖u q‖ ≤ B := by
  obtain ⟨B, hB⟩ := hh.bounded_moments a hu.ha 0 (by decide) m hu.hm
  exact ⟨B, fun q => (hu.norm_le q).trans (by simpa using hB q)⟩

theorem isDiffProfile_base {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    IsDiffProfile σ H1 h where
  smooth := hh.smooth
  support_s := hh.support_s
  bdd_w := bdd_of_isBaseDeriv hh (isBaseDeriv_base hh 0 (by decide))
  bdd_opS := bdd_of_isBaseDeriv hh (isBaseDeriv_base hh 1 (by decide))
  bdd_pdQ := bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ hh 0 (by decide))
  bdd_pdQ2 := bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ_pdQ hh 0 (by decide))
  bdd_pdEta := bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta hh 0 (by decide))
  bdd_pdEta2 := bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta_pdEta hh 0 (by decide))

theorem isDiffProfile_pdQ {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    IsDiffProfile σ H1 (pdQ h) where
  smooth := contDiff_pdQ hh.smooth
  support_s := support_s_pdQ hh.support_s
  bdd_w := bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ hh 0 (by decide))
  bdd_opS := by
    rw [opS_pdQ_comm hh.smooth]
    exact bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ hh 1 (by decide))
  bdd_pdQ := bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ_pdQ hh 0 (by decide))
  bdd_pdQ2 := bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ3 hh 0 (by decide))
  bdd_pdEta := bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta_pdQ hh 0 (by decide))
  bdd_pdEta2 := bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta_pdEta_pdQ hh 0 (by decide))

theorem isDiffProfile_pdEta {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) :
    IsDiffProfile σ H1 (pdEta h) where
  smooth := contDiff_pdEta hh.smooth
  support_s := support_s_pdEta hh.support_s
  bdd_w := bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta hh 0 (by decide))
  bdd_opS := by
    rw [opS_pdEta_comm hh.smooth]
    exact bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta hh 1 (by decide))
  bdd_pdQ := by
    obtain ⟨B, hB⟩ := hh.bounded_moments 0 (by decide) 0 (by decide) 2 (by decide)
    refine ⟨B, fun q => ?_⟩
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdQ_le (contDiff_pdEta hh.smooth) 0 q).trans
      ((norm_iteratedFDeriv_pdEta_le hh.smooth 1 q).trans (by simpa using hB q))
  bdd_pdQ2 := bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ_pdQ_pdEta hh 0 (by decide))
  bdd_pdEta := bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta_pdEta hh 0 (by decide))
  bdd_pdEta2 := bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta3 hh 0 (by decide))

theorem isDiffProfile_pdQ_pdQ {c σ H1 : ℝ} {h : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) :
    IsDiffProfile σ H1 (pdQ (pdQ h)) where
  smooth := contDiff_pdQ (contDiff_pdQ hh.smooth)
  support_s := support_s_pdQ (support_s_pdQ hh.support_s)
  bdd_w := bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ_pdQ hh 0 (by decide))
  bdd_opS := by
    have hcomm : opS (pdQ (pdQ h)) = pdQ (pdQ (opS h)) := by
      rw [opS_pdQ_comm (contDiff_pdQ hh.smooth), opS_pdQ_comm hh.smooth]
    rw [hcomm]
    exact bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ_pdQ hh 1 (by decide))
  bdd_pdQ := bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ3 hh 0 (by decide))
  bdd_pdQ2 := bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ4 hh 0 (by decide))
  bdd_pdEta := by
    obtain ⟨B, hB⟩ := hh.bounded_moments 0 (by decide) 0 (by decide) 3 (by decide)
    refine ⟨B, fun q => ?_⟩
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdEta_le (contDiff_pdQ (contDiff_pdQ hh.smooth)) 0 q).trans
      ((norm_iteratedFDeriv_pdQ_le (contDiff_pdQ hh.smooth) 1 q).trans
        ((norm_iteratedFDeriv_pdQ_le hh.smooth 2 q).trans (by simpa using hB q)))
  bdd_pdEta2 := bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta2_pdQ2 hh 0 (by decide))

theorem isDiffProfile_pdEta_pdEta {c σ H1 : ℝ} {h : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) :
    IsDiffProfile σ H1 (pdEta (pdEta h)) where
  smooth := contDiff_pdEta (contDiff_pdEta hh.smooth)
  support_s := support_s_pdEta (support_s_pdEta hh.support_s)
  bdd_w := bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta_pdEta hh 0 (by decide))
  bdd_opS := by
    have hcomm : opS (pdEta (pdEta h)) = pdEta (pdEta (opS h)) := by
      rw [opS_pdEta_comm (contDiff_pdEta hh.smooth), opS_pdEta_comm hh.smooth]
    rw [hcomm]
    exact bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta_pdEta hh 1 (by decide))
  bdd_pdQ := by
    obtain ⟨B, hB⟩ := hh.bounded_moments 0 (by decide) 0 (by decide) 3 (by decide)
    refine ⟨B, fun q => ?_⟩
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdQ_le (contDiff_pdEta (contDiff_pdEta hh.smooth)) 0 q).trans
      ((norm_iteratedFDeriv_pdEta_le (contDiff_pdEta hh.smooth) 1 q).trans
        ((norm_iteratedFDeriv_pdEta_le hh.smooth 2 q).trans (by simpa using hB q)))
  bdd_pdQ2 := bdd_of_isBaseDeriv hh (isBaseDeriv_pdQ2_pdEta2 hh 0 (by decide))
  bdd_pdEta := bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta3 hh 0 (by decide))
  bdd_pdEta2 := bdd_of_isBaseDeriv hh (isBaseDeriv_pdEta4 hh 0 (by decide))

/-! ### 3. Differentiation of `planeHeat` and `flatAdjointSlice` at fixed `t > 0` -/

/-- Kernel integrand `G_{θ(q.1, t)}(y) • w(e^t q.1, q.2 - planeι y)` for fixed `t`. -/
def sliceKerIntegrand (ν : ℝ) (w : Profile → MeridC) (t : ℝ) (q : Profile) (y : Euc 2) :
    MeridC :=
  gaussKernel 2 (ptTh ν q.1 t) y • w (Real.exp t * q.1, q.2 - planeι y)

/-- Pointwise `q`-Fréchet derivative of `sliceKerIntegrand ν w t q y`. -/
def sliceKerFDeriv (ν : ℝ) (w : Profile → MeridC) (t : ℝ) (q : Profile) (y : Euc 2) :
    Profile →L[ℝ] MeridC :=
  fstProfileCLM.smulRight
    ((gaussDt 2 (ptTh ν q.1 t) y * (ν * (Real.exp t - 1))) •
        w (Real.exp t * q.1, q.2 - planeι y) +
      gaussKernel 2 (ptTh ν q.1 t) y •
        (Real.exp t • pdS w (Real.exp t * q.1, q.2 - planeι y))) +
  snd1ProfileCLM.smulRight
    (gaussKernel 2 (ptTh ν q.1 t) y • pdQ w (Real.exp t * q.1, q.2 - planeι y)) +
  snd2ProfileCLM.smulRight
    (gaussKernel 2 (ptTh ν q.1 t) y • pdEta w (Real.exp t * q.1, q.2 - planeι y))

/-- Target `q`-Fréchet derivative of `B0224.planeHeat (ptTh ν q.1 t) (w(e^t q.1, ·)) q.2`
after applying Gaussian integration by parts `gaussDt_lap_of_bdd`. -/
def planeHeatSliceFDeriv (ν : ℝ) (w : Profile → MeridC) (t : ℝ) (p : Profile) :
    Profile →L[ℝ] MeridC :=
  fstProfileCLM.smulRight
    ((ν * (Real.exp t - 1)) •
        B0224.planeHeat (ptTh ν p.1 t) (fun z => laplaceQEta w (Real.exp t * p.1, z)) p.2 +
      p.1⁻¹ • B0224.planeHeat (ptTh ν p.1 t) (fun z => opS w (Real.exp t * p.1, z)) p.2) +
  snd1ProfileCLM.smulRight
    (B0224.planeHeat (ptTh ν p.1 t) (fun z => pdQ w (Real.exp t * p.1, z)) p.2) +
  snd2ProfileCLM.smulRight
    (B0224.planeHeat (ptTh ν p.1 t) (fun z => pdEta w (Real.exp t * p.1, z)) p.2)

/-- Target `q`-Fréchet derivative of `flatAdjointSlice ν μ w t` at `p` (`0 < p.1`, `0 < t`),
uniformly bounded as `t → 0⁺`. -/
def sliceFDeriv (ν : ℝ) (μ : ℂ) (w : Profile → MeridC) (t : ℝ) (p : Profile) :
    Profile →L[ℝ] MeridC :=
  (p.1⁻¹ • fstProfileCLM).smulRight
    (flatAdjointSlice ν μ (opS w) t p +
      thetaWeight 1 t • flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t p) +
  snd1ProfileCLM.smulRight (flatAdjointSlice ν μ (pdQ w) t p) +
  snd2ProfileCLM.smulRight (flatAdjointSlice ν μ (pdEta w) t p)

theorem hasFDerivAt_ptTh_profile (ν t : ℝ) (q : Profile) :
    HasFDerivAt (fun r : Profile => ptTh ν r.1 t)
      ((ν * (Real.exp t - 1)) • fstProfileCLM) q := by
  have heq : (fun r : Profile => ptTh ν r.1 t) =
      fun r : Profile => (ν * (Real.exp t - 1)) * fstProfileCLM r := by
    funext r
    simp only [ptTh, fstProfileCLM_apply]
    ring
  rw [heq]
  exact ((ν * (Real.exp t - 1)) • fstProfileCLM).hasFDerivAt

theorem hasFDerivAt_shift_profile {w : Profile → MeridC} (hws : ContDiff ℝ ∞ w)
    (t : ℝ) (y : Euc 2) (q : Profile) :
    HasFDerivAt (fun r : Profile => w (Real.exp t * r.1, r.2 - planeι y))
      (fstProfileCLM.smulRight (Real.exp t • pdS w (Real.exp t * q.1, q.2 - planeι y)) +
        snd1ProfileCLM.smulRight (pdQ w (Real.exp t * q.1, q.2 - planeι y)) +
        snd2ProfileCLM.smulRight (pdEta w (Real.exp t * q.1, q.2 - planeι y))) q := by
  set L : Profile →L[ℝ] Profile :=
    (Real.exp t • fstProfileCLM).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have hAff : HasFDerivAt (fun r : Profile => (Real.exp t * r.1, r.2 - planeι y)) L q := by
    refine HasFDerivAt.prodMk ?_ ?_
    · exact (Real.exp t • fstProfileCLM).hasFDerivAt
    · exact (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).hasFDerivAt.sub_const (planeι y)
  have hw_diff : HasFDerivAt w (fderiv ℝ w (Real.exp t * q.1, q.2 - planeι y))
      (Real.exp t * q.1, q.2 - planeι y) :=
    (hws.differentiable (by simp) _).hasFDerivAt
  refine (hw_diff.comp q hAff).congr_fderiv ?_
  rw [fderiv_profile_eq]
  refine ContinuousLinearMap.ext fun dq => ?_
  simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.coe_snd', fstProfileCLM_apply, snd1ProfileCLM_apply,
    snd2ProfileCLM_apply, smul_smul, smul_eq_mul, mul_comm (Real.exp t) dq.1]

theorem hasFDerivAt_sliceKerIntegrand {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    {w : Profile → MeridC} (hws : ContDiff ℝ ∞ w) (y : Euc 2) {q : Profile} (hq : 0 < q.1) :
    HasFDerivAt (fun r : Profile => sliceKerIntegrand ν w t r y)
      (sliceKerFDeriv ν w t q y) q := by
  have hθq : 0 < ptTh ν q.1 t := ptTh_pos hν hq ht
  have hG : HasFDerivAt (fun r : Profile => gaussKernel 2 (ptTh ν r.1 t) y)
      ((gaussDt 2 (ptTh ν q.1 t) y * (ν * (Real.exp t - 1))) • fstProfileCLM) q := by
    have h1 := (UnforcedLeray.Heat.hasDerivAt_gaussKernel_time hθq y).hasFDerivAt.comp q
      (hasFDerivAt_ptTh_profile ν t q)
    refine h1.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun dq => ?_
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.toSpanSingleton_apply, fstProfileCLM_apply, smul_eq_mul]
    ring
  have hW := hasFDerivAt_shift_profile hws t y q
  refine (hG.smul hW).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun dq => ?_
  simp only [sliceKerFDeriv, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    fstProfileCLM_apply, snd1ProfileCLM_apply, snd2ProfileCLM_apply]
  module

theorem norm_sliceKerFDeriv_le (ν t : ℝ) (w : Profile → MeridC) (q : Profile) (y : Euc 2) :
    ‖sliceKerFDeriv ν w t q y‖ ≤
      |gaussDt 2 (ptTh ν q.1 t) y * (ν * (Real.exp t - 1))| *
        ‖w (Real.exp t * q.1, q.2 - planeι y)‖ +
      |gaussKernel 2 (ptTh ν q.1 t) y| *
        (Real.exp t * ‖pdS w (Real.exp t * q.1, q.2 - planeι y)‖ +
          ‖pdQ w (Real.exp t * q.1, q.2 - planeι y)‖ +
          ‖pdEta w (Real.exp t * q.1, q.2 - planeι y)‖) := by
  unfold sliceKerFDeriv
  have h1 := norm_smulRight_le fstProfileCLM norm_fstProfileCLM_le
    ((gaussDt 2 (ptTh ν q.1 t) y * (ν * (Real.exp t - 1))) •
        w (Real.exp t * q.1, q.2 - planeι y) +
      gaussKernel 2 (ptTh ν q.1 t) y •
        (Real.exp t • pdS w (Real.exp t * q.1, q.2 - planeι y)))
  have h2 := norm_smulRight_le snd1ProfileCLM norm_snd1ProfileCLM_le
    (gaussKernel 2 (ptTh ν q.1 t) y • pdQ w (Real.exp t * q.1, q.2 - planeι y))
  have h3 := norm_smulRight_le snd2ProfileCLM norm_snd2ProfileCLM_le
    (gaussKernel 2 (ptTh ν q.1 t) y • pdEta w (Real.exp t * q.1, q.2 - planeι y))
  have h1' : ‖(gaussDt 2 (ptTh ν q.1 t) y * (ν * (Real.exp t - 1))) •
        w (Real.exp t * q.1, q.2 - planeι y) +
      gaussKernel 2 (ptTh ν q.1 t) y •
        (Real.exp t • pdS w (Real.exp t * q.1, q.2 - planeι y))‖ ≤
      |gaussDt 2 (ptTh ν q.1 t) y * (ν * (Real.exp t - 1))| *
        ‖w (Real.exp t * q.1, q.2 - planeι y)‖ +
      |gaussKernel 2 (ptTh ν q.1 t) y| *
        (Real.exp t * ‖pdS w (Real.exp t * q.1, q.2 - planeι y)‖) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.exp_pos t).le]
  rw [norm_smul, Real.norm_eq_abs] at h2 h3
  calc ‖fstProfileCLM.smulRight _ + snd1ProfileCLM.smulRight _ + snd2ProfileCLM.smulRight _‖
      ≤ ‖fstProfileCLM.smulRight _ + snd1ProfileCLM.smulRight _‖ + ‖snd2ProfileCLM.smulRight _‖ :=
        norm_add_le _ _
    _ ≤ ‖fstProfileCLM.smulRight _‖ + ‖snd1ProfileCLM.smulRight _‖ + ‖snd2ProfileCLM.smulRight _‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by linarith [h1.trans h1', h2, h3]

set_option maxHeartbeats 400000 in
/-- Differentiation of `q ↦ B0224.planeHeat (ptTh ν q.1 t) (w(e^t q.1, ·)) q.2` at `p` (`0 < p.1`,
`0 < t`) under the planar Gaussian integral, combined with `gaussDt_lap_of_bdd`. -/
theorem hasFDerivAt_planeHeatSlice {σ H1 ν t : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (ht : 0 < t)
    {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w) {p : Profile} (hp : 0 < p.1) :
    HasFDerivAt
      (fun q : Profile => B0224.planeHeat (ptTh ν q.1 t) (fun z => w (Real.exp t * q.1, z)) q.2)
      (planeHeatSliceFDeriv ν w t p) p := by
  have hθ0 : 0 < ptTh ν p.1 t := ptTh_pos hν hp ht
  have hexp1 : 0 < Real.exp t - 1 := sub_pos.2 (Real.one_lt_exp_iff.2 ht)
  have hνe : 0 < ν * (Real.exp t - 1) := mul_pos hν hexp1
  set U : Set Profile := {q : Profile | p.1 / 2 < q.1 ∧ q.1 < 2 * p.1}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have hpU : p ∈ U := ⟨by linarith, by linarith⟩
  have hU_nhds : U ∈ 𝓝 p := hU_open.mem_nhds hpU
  have hev_eq : (fun q : Profile =>
      B0224.planeHeat (ptTh ν q.1 t) (fun z => w (Real.exp t * q.1, z)) q.2) =ᶠ[𝓝 p]
      fun q : Profile => ∫ y : Euc 2, sliceKerIntegrand ν w t q y := by
    filter_upwards [hU_nhds] with q hq
    have hq_pos : 0 < q.1 := by linarith [hq.1]
    rw [B0224.planeHeat_of_pos (ptTh_pos hν hq_pos ht)]
    rfl
  obtain ⟨A, hA0, hA⟩ := UnforcedLeray.Heat.abs_gaussDt_le (d := 2) hθ0
  obtain ⟨K, hK0, hK⟩ := ptGaussEnv hθ0
  obtain ⟨M0, hM0⟩ := hw.bdd_w
  obtain ⟨MS, hMS⟩ := hw.bdd_pdS hσ
  obtain ⟨MQ1, hMQ1⟩ := hw.bdd_pdQ
  obtain ⟨ME1, hME1⟩ := hw.bdd_pdEta
  have hM0_nn : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
  have hMS_nn : 0 ≤ MS := (norm_nonneg _).trans (hMS 0)
  have hMQ1_nn : 0 ≤ MQ1 := (norm_nonneg _).trans (hMQ1 0)
  have hME1_nn : 0 ≤ ME1 := (norm_nonneg _).trans (hME1 0)
  set C_dom : ℝ := A * (ν * (Real.exp t - 1)) * M0 + K * (Real.exp t * MS + MQ1 + ME1)
  set bd : Euc 2 → ℝ := fun y => C_dom * Real.exp (-(1 / (16 * ptTh ν p.1 t)) * ‖y‖ ^ 2)
  have hpos_b : 0 < 1 / (16 * ptTh ν p.1 t) := one_div_pos.mpr (by linarith)
  have hbd_int : Integrable bd (volume : Measure (Euc 2)) :=
    (UnforcedLeray.Gaussian.integrable_exp_neg_mul_sq_norm (d := 2) hpos_b).const_mul C_dom
  have hwc : Continuous w := hw.smooth.continuous
  have hpdSc : Continuous (pdS w) := (contDiff_pdS hw.smooth).continuous
  have hpdQc : Continuous (pdQ w) := (contDiff_pdQ hw.smooth).continuous
  have hpdEtac : Continuous (pdEta w) := (contDiff_pdEta hw.smooth).continuous
  have hF_meas : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable (sliceKerIntegrand ν w t q) volume := by
    refine Eventually.of_forall fun q => ?_
    exact ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) (ptTh ν q.1 t)).smul
      (ptCont_shift hwc (Real.exp t * q.1) q.2)).aestronglyMeasurable
  have hF_int : Integrable (sliceKerIntegrand ν w t p) volume :=
    ptIntKer hθ0 (ptCont_shift hwc (Real.exp t * p.1) p.2) (fun y => hM0 _)
  have hF'_cont : Continuous (sliceKerFDeriv ν w t p) := by
    unfold sliceKerFDeriv
    have c1 : Continuous (fun y : Euc 2 =>
        (gaussDt 2 (ptTh ν p.1 t) y * (ν * (Real.exp t - 1))) •
          w (Real.exp t * p.1, p.2 - planeι y) +
        gaussKernel 2 (ptTh ν p.1 t) y •
          (Real.exp t • pdS w (Real.exp t * p.1, p.2 - planeι y))) :=
      (((UnforcedLeray.Heat.continuous_gaussDt 2 (ptTh ν p.1 t)).mul continuous_const).smul
        (ptCont_shift hwc _ _)).add
        ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) (ptTh ν p.1 t)).smul
          ((ptCont_shift hpdSc (Real.exp t * p.1) p.2).const_smul (Real.exp t)))
    have c2 : Continuous (fun y : Euc 2 =>
        gaussKernel 2 (ptTh ν p.1 t) y • pdQ w (Real.exp t * p.1, p.2 - planeι y)) :=
      (UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) (ptTh ν p.1 t)).smul
        (ptCont_shift hpdQc _ _)
    have c3 : Continuous (fun y : Euc 2 =>
        gaussKernel 2 (ptTh ν p.1 t) y • pdEta w (Real.exp t * p.1, p.2 - planeι y)) :=
      (UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) (ptTh ν p.1 t)).smul
        (ptCont_shift hpdEtac _ _)
    exact (((smulRightCLM fstProfileCLM).continuous.comp c1).add
      ((smulRightCLM snd1ProfileCLM).continuous.comp c2)).add
      ((smulRightCLM snd2ProfileCLM).continuous.comp c3)
  have hbound : ∀ᵐ y ∂(volume : Measure (Euc 2)), ∀ q ∈ U,
      ‖sliceKerFDeriv ν w t q y‖ ≤ bd y := by
    refine Eventually.of_forall fun y q hq => ?_
    have hq1 : ptTh ν p.1 t / 2 < ptTh ν q.1 t := by
      unfold ptTh
      have : p.1 / 2 * (ν * (Real.exp t - 1)) < q.1 * (ν * (Real.exp t - 1)) :=
        mul_lt_mul_of_pos_right hq.1 hνe
      linarith
    have hq2 : ptTh ν q.1 t < 2 * ptTh ν p.1 t := by
      unfold ptTh
      have : q.1 * (ν * (Real.exp t - 1)) < (2 * p.1) * (ν * (Real.exp t - 1)) :=
        mul_lt_mul_of_pos_right hq.2 hνe
      linarith
    have hθq : 0 < ptTh ν q.1 t := by linarith
    have hgD := hA (ptTh ν q.1 t) hq1 hq2 y
    have hgK := hK (ptTh ν q.1 t) hq1 hq2 y
    have hgK0 : 0 ≤ gaussKernel 2 (ptTh ν q.1 t) y :=
      UnforcedLeray.Gaussian.gaussKernel_nonneg (d := 2) hθq y
    have hE : 0 ≤ Real.exp (-(1 / (16 * ptTh ν p.1 t)) * ‖y‖ ^ 2) := (Real.exp_pos _).le
    refine (norm_sliceKerFDeriv_le ν t w q y).trans ?_
    rw [abs_mul, abs_of_pos hνe, abs_of_nonneg hgK0]
    have hT1 : |gaussDt 2 (ptTh ν q.1 t) y| * (ν * (Real.exp t - 1)) *
        ‖w (Real.exp t * q.1, q.2 - planeι y)‖ ≤
        A * (ν * (Real.exp t - 1)) * M0 * Real.exp (-(1 / (16 * ptTh ν p.1 t)) * ‖y‖ ^ 2) := by
      have h1 : |gaussDt 2 (ptTh ν q.1 t) y| * (ν * (Real.exp t - 1)) ≤
          A * Real.exp (-(1 / (16 * ptTh ν p.1 t)) * ‖y‖ ^ 2) * (ν * (Real.exp t - 1)) :=
        mul_le_mul_of_nonneg_right hgD hνe.le
      have h2 := mul_le_mul h1 (hM0 (Real.exp t * q.1, q.2 - planeι y))
        (norm_nonneg (w (Real.exp t * q.1, q.2 - planeι y))) (by positivity)
      linarith
    have hT2 : gaussKernel 2 (ptTh ν q.1 t) y *
        (Real.exp t * ‖pdS w (Real.exp t * q.1, q.2 - planeι y)‖ +
          ‖pdQ w (Real.exp t * q.1, q.2 - planeι y)‖ +
          ‖pdEta w (Real.exp t * q.1, q.2 - planeι y)‖) ≤
        K * (Real.exp t * MS + MQ1 + ME1) * Real.exp (-(1 / (16 * ptTh ν p.1 t)) * ‖y‖ ^ 2) := by
      have hsum : Real.exp t * ‖pdS w (Real.exp t * q.1, q.2 - planeι y)‖ +
          ‖pdQ w (Real.exp t * q.1, q.2 - planeι y)‖ +
          ‖pdEta w (Real.exp t * q.1, q.2 - planeι y)‖ ≤
          Real.exp t * MS + MQ1 + ME1 := by
        have hS' : Real.exp t * ‖pdS w (Real.exp t * q.1, q.2 - planeι y)‖ ≤ Real.exp t * MS :=
          mul_le_mul_of_nonneg_left (hMS _) (Real.exp_pos t).le
        linarith [hMQ1 (Real.exp t * q.1, q.2 - planeι y),
          hME1 (Real.exp t * q.1, q.2 - planeι y)]
      have h3 := mul_le_mul hgK hsum (by positivity) (by positivity)
      linarith
    unfold bd C_dom
    linarith
  have hdiff : ∀ᵐ y ∂(volume : Measure (Euc 2)), ∀ q ∈ U,
      HasFDerivAt (fun r : Profile => sliceKerIntegrand ν w t r y)
        (sliceKerFDeriv ν w t q y) q := by
    refine Eventually.of_forall fun y q hq => ?_
    have hq_pos : 0 < q.1 := by linarith [hq.1]
    exact hasFDerivAt_sliceKerIntegrand hν ht hw.smooth y hq_pos
  have hIntDiff := hasFDerivAt_integral_of_dominated_of_fderiv_le
    hU_nhds hF_meas hF_int hF'_cont.aestronglyMeasurable hbound hbd_int hdiff
  refine (hIntDiff.congr_of_eventuallyEq hev_eq).congr_fderiv ?_
  have hI_dt : Integrable (fun y : Euc 2 =>
      (gaussDt 2 (ptTh ν p.1 t) y * (ν * (Real.exp t - 1))) •
        w (Real.exp t * p.1, p.2 - planeι y)) := by
    refine ptIntEnv (f := fun y => gaussDt 2 (ptTh ν p.1 t) y * (ν * (Real.exp t - 1)))
      (g := fun y => w (Real.exp t * p.1, p.2 - planeι y))
      (b := 1 / (16 * ptTh ν p.1 t)) (C := A * (ν * (Real.exp t - 1))) (M := M0)
      hpos_b ((UnforcedLeray.Heat.continuous_gaussDt 2 (ptTh ν p.1 t)).mul continuous_const)
      (ptCont_shift hwc _ _) (mul_nonneg hA0 hνe.le) hM0_nn ?_ (fun y => hM0 _)
    intro y
    rw [abs_mul, abs_of_pos hνe]
    calc |gaussDt 2 (ptTh ν p.1 t) y| * (ν * (Real.exp t - 1))
        ≤ (A * Real.exp (-(1 / (16 * ptTh ν p.1 t)) * ‖y‖ ^ 2)) * (ν * (Real.exp t - 1)) :=
          mul_le_mul_of_nonneg_right (hA (ptTh ν p.1 t) (by linarith) (by linarith) y) hνe.le
      _ = A * (ν * (Real.exp t - 1)) * Real.exp (-(1 / (16 * ptTh ν p.1 t)) * ‖y‖ ^ 2) := by ring
  have hI_S : Integrable (fun y : Euc 2 =>
      gaussKernel 2 (ptTh ν p.1 t) y •
        (Real.exp t • pdS w (Real.exp t * p.1, p.2 - planeι y))) :=
    ptIntKer hθ0 ((ptCont_shift hpdSc (Real.exp t * p.1) p.2).const_smul (Real.exp t))
      (M := Real.exp t * MS) (fun y => by
        rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos t).le]
        exact mul_le_mul_of_nonneg_left (hMS _) (Real.exp_pos t).le)
  have hI_Q : Integrable (fun y : Euc 2 =>
      gaussKernel 2 (ptTh ν p.1 t) y • pdQ w (Real.exp t * p.1, p.2 - planeι y)) :=
    ptIntKer hθ0 (ptCont_shift hpdQc _ _) (fun y => hMQ1 _)
  have hI_Eta : Integrable (fun y : Euc 2 =>
      gaussKernel 2 (ptTh ν p.1 t) y • pdEta w (Real.exp t * p.1, p.2 - planeι y)) :=
    ptIntKer hθ0 (ptCont_shift hpdEtac _ _) (fun y => hME1 _)
  have hI_1 : Integrable (fun y : Euc 2 =>
      fstProfileCLM.smulRight
        ((gaussDt 2 (ptTh ν p.1 t) y * (ν * (Real.exp t - 1))) •
            w (Real.exp t * p.1, p.2 - planeι y) +
          gaussKernel 2 (ptTh ν p.1 t) y •
            (Real.exp t • pdS w (Real.exp t * p.1, p.2 - planeι y)))) :=
    (smulRightCLM fstProfileCLM).integrable_comp (integrable_add_fun hI_dt hI_S)
  have hI_2 : Integrable (fun y : Euc 2 =>
      snd1ProfileCLM.smulRight
        (gaussKernel 2 (ptTh ν p.1 t) y • pdQ w (Real.exp t * p.1, p.2 - planeι y))) :=
    (smulRightCLM snd1ProfileCLM).integrable_comp hI_Q
  have hI_3 : Integrable (fun y : Euc 2 =>
      snd2ProfileCLM.smulRight
        (gaussKernel 2 (ptTh ν p.1 t) y • pdEta w (Real.exp t * p.1, p.2 - planeι y))) :=
    (smulRightCLM snd2ProfileCLM).integrable_comp hI_Eta
  unfold sliceKerFDeriv planeHeatSliceFDeriv
  rw [integral_add (integrable_add_fun hI_1 hI_2) hI_3, integral_add hI_1 hI_2,
    integral_smulRight fstProfileCLM (integrable_add_fun hI_dt hI_S),
    integral_smulRight snd1ProfileCLM hI_Q,
    integral_smulRight snd2ProfileCLM hI_Eta,
    integral_add hI_dt hI_S]
  congr 2
  · congr 1
    have hdt_eq : ∫ y : Euc 2,
        (gaussDt 2 (ptTh ν p.1 t) y * (ν * (Real.exp t - 1))) •
          w (Real.exp t * p.1, p.2 - planeι y) =
        (ν * (Real.exp t - 1)) •
          B0224.planeHeat (ptTh ν p.1 t) (fun z => laplaceQEta w (Real.exp t * p.1, z)) p.2 := by
      have hcomm : (fun y : Euc 2 =>
          (gaussDt 2 (ptTh ν p.1 t) y * (ν * (Real.exp t - 1))) •
            w (Real.exp t * p.1, p.2 - planeι y)) =
          fun y : Euc 2 => (ν * (Real.exp t - 1)) •
            (gaussDt 2 (ptTh ν p.1 t) y • w (Real.exp t * p.1, p.2 - planeι y)) := by
        funext y
        rw [mul_comm, mul_smul]
      rw [hcomm, integral_smul,
        gaussDt_lap_of_bdd hθ0 (Real.exp t * p.1) hw.smooth
          hw.bdd_w hw.bdd_pdQ hw.bdd_pdQ2 hw.bdd_pdEta hw.bdd_pdEta2 p.2]
    have hS_eq : ∫ y : Euc 2,
        gaussKernel 2 (ptTh ν p.1 t) y •
          (Real.exp t • pdS w (Real.exp t * p.1, p.2 - planeι y)) =
        p.1⁻¹ • B0224.planeHeat (ptTh ν p.1 t) (fun z => opS w (Real.exp t * p.1, z)) p.2 := by
      rw [B0224.planeHeat_of_pos hθ0, ← integral_smul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      have hp_ne : p.1 ≠ 0 := hp.ne'
      rw [smul_comm p.1⁻¹ (gaussKernel 2 (ptTh ν p.1 t) y)]
      congr 1
      simp only [opS, smul_smul]
      congr 1
      field_simp
    rw [hdt_eq, hS_eq]
  · rw [B0224.planeHeat_of_pos hθ0]
  · rw [B0224.planeHeat_of_pos hθ0]

/-- Exact `q`-Fréchet derivative of `flatAdjointSlice ν μ w t` at `p` (`0 < p.1`, `0 < t`). -/
theorem hasFDerivAt_flatAdjointSlice {σ H1 ν t : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (ht : 0 < t)
    (μ : ℂ) {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w) {p : Profile} (hp : 0 < p.1) :
    HasFDerivAt (flatAdjointSlice ν μ w t) (sliceFDeriv ν μ w t p) p := by
  set c_t : ℂ := Complex.exp (-((starRingEnd ℂ μ + (1 / 2 : ℂ)) * (t : ℂ)))
  have h1 := (hasFDerivAt_planeHeatSlice hν hσ ht hw hp).const_smul c_t
  refine h1.congr_fderiv ?_
  have hpow := heatTimeAdj_pow_smul_flatAdjointSlice ν μ 1 (laplaceQEta w) ht p
  simp only [pow_one, flatAdjointSlice] at hpow
  have hlap : c_t • ((ν * (Real.exp t - 1)) •
      B0224.planeHeat (ptTh ν p.1 t) (fun z => laplaceQEta w (Real.exp t * p.1, z)) p.2) =
      p.1⁻¹ • (thetaWeight 1 t • flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t p) := by
    have hp_ne : p.1 ≠ 0 := hp.ne'
    have hmul : ν * (Real.exp t - 1) = p.1⁻¹ * (ν * p.1 * (Real.exp t - 1)) := by
      field_simp
    rw [hmul, mul_smul p.1⁻¹, smul_comm c_t p.1⁻¹]
    congr 1
    rw [smul_comm c_t (ν * p.1 * (Real.exp t - 1)),
      RCLike.real_smul_eq_coe_smul (K := ℂ) (ν * p.1 * (Real.exp t - 1))]
    exact hpow
  unfold ptTh at hlap
  refine ContinuousLinearMap.ext fun dq => ?_
  simp only [planeHeatSliceFDeriv, sliceFDeriv, flatAdjointSlice, ptTh,
    smul_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    fstProfileCLM_apply, snd1ProfileCLM_apply, snd2ProfileCLM_apply,
    smul_add, smul_eq_mul, smul_comm c_t dq.1, smul_comm c_t dq.2.1, smul_comm c_t dq.2.2]
  rw [hlap, smul_comm c_t p.1⁻¹]
  simp only [c_t, flatAdjointSlice, smul_smul, mul_comm dq.1 p.1⁻¹]
  abel

/-! ### 4. Differentiation of `causalAdjointRep` under the `t ∈ Ioi 0` integral -/

theorem stronglyMeasurable_sliceFDeriv (ν : ℝ) (μ : ℂ) {w : Profile → MeridC}
    (hws : ContDiff ℝ ∞ w) (p : Profile) :
    StronglyMeasurable (fun t : ℝ => sliceFDeriv ν μ w t p) := by
  unfold sliceFDeriv
  have s1 := stronglyMeasurable_flatAdjointSlice ν μ (contDiff_opS hws).continuous.stronglyMeasurable p
  have s2 := (continuous_thetaWeight 1).stronglyMeasurable.smul
    (stronglyMeasurable_flatAdjointSlice ν μ
      (contDiff_nuSMul ν 1 (contDiff_laplaceQEta hws)).continuous.stronglyMeasurable p)
  have s3 := stronglyMeasurable_flatAdjointSlice ν μ (contDiff_pdQ hws).continuous.stronglyMeasurable p
  have s4 := stronglyMeasurable_flatAdjointSlice ν μ (contDiff_pdEta hws).continuous.stronglyMeasurable p
  exact (((smulRightCLM (p.1⁻¹ • fstProfileCLM)).continuous.comp_stronglyMeasurable (s1.add s2)).add
    ((smulRightCLM snd1ProfileCLM).continuous.comp_stronglyMeasurable s3)).add
    ((smulRightCLM snd2ProfileCLM).continuous.comp_stronglyMeasurable s4)

theorem norm_sliceFDeriv_le (ν : ℝ) (μ : ℂ) (w : Profile → MeridC) (t : ℝ)
    {p q : Profile} (hp : 0 < p.1) (hq : p.1 / 2 ≤ q.1) :
    ‖sliceFDeriv ν μ w t q‖ ≤
      (2 / p.1) * (‖flatAdjointSlice ν μ (opS w) t q‖ +
        ‖flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t q‖) +
      ‖flatAdjointSlice ν μ (pdQ w) t q‖ +
      ‖flatAdjointSlice ν μ (pdEta w) t q‖ := by
  have hq_pos : 0 < q.1 := by linarith
  have hinv_le : q.1⁻¹ ≤ 2 / p.1 := by
    rw [← one_div, div_le_div_iff₀ hq_pos hp]
    linarith
  have h1 : ‖(q.1⁻¹ • fstProfileCLM).smulRight
      (flatAdjointSlice ν μ (opS w) t q +
        thetaWeight 1 t • flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t q)‖ ≤
      (2 / p.1) * (‖flatAdjointSlice ν μ (opS w) t q‖ +
        ‖flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t q‖) := by
    have hsm : (q.1⁻¹ • fstProfileCLM).smulRight =
        fun v : MeridC => q.1⁻¹ • fstProfileCLM.smulRight v := by
      funext v
      refine ContinuousLinearMap.ext fun dq => ?_
      simp [smul_smul]
    rw [hsm, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hq_pos.le)]
    have hle1 := (norm_smulRight_le fstProfileCLM norm_fstProfileCLM_le
      (flatAdjointSlice ν μ (opS w) t q +
        thetaWeight 1 t • flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t q)).trans
      (norm_add_le _ _)
    have hle2 : ‖thetaWeight 1 t • flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t q‖ ≤
        ‖flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t q‖ := by
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_thetaWeight_le 1 t)
    exact mul_le_mul hinv_le (hle1.trans (add_le_add le_rfl hle2)) (norm_nonneg _) (by positivity)
  have h2 := norm_smulRight_le snd1ProfileCLM norm_snd1ProfileCLM_le
    (flatAdjointSlice ν μ (pdQ w) t q)
  have h3 := norm_smulRight_le snd2ProfileCLM norm_snd2ProfileCLM_le
    (flatAdjointSlice ν μ (pdEta w) t q)
  unfold sliceFDeriv
  calc ‖(q.1⁻¹ • fstProfileCLM).smulRight _ + snd1ProfileCLM.smulRight _ +
          snd2ProfileCLM.smulRight _‖
      ≤ ‖(q.1⁻¹ • fstProfileCLM).smulRight _ + snd1ProfileCLM.smulRight _‖ +
          ‖snd2ProfileCLM.smulRight _‖ := norm_add_le _ _
    _ ≤ ‖(q.1⁻¹ • fstProfileCLM).smulRight _‖ + ‖snd1ProfileCLM.smulRight _‖ +
          ‖snd2ProfileCLM.smulRight _‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3

/-- Target Fréchet derivative of `causalAdjointRep ν μ (thetaWeight k) w` at `p` (`0 < p.1`). -/
def causalAdjointFDeriv (ν : ℝ) (μ : ℂ) (k : ℕ) (w : Profile → MeridC) (p : Profile) :
    Profile →L[ℝ] MeridC :=
  (p.1⁻¹ • fstProfileCLM).smulRight
    (causalAdjointRep ν μ (thetaWeight k) (opS w) p +
      causalAdjointRep ν μ (thetaWeight (k + 1)) (nuSMul ν 1 (laplaceQEta w)) p) +
  snd1ProfileCLM.smulRight (causalAdjointRep ν μ (thetaWeight k) (pdQ w) p) +
  snd2ProfileCLM.smulRight (causalAdjointRep ν μ (thetaWeight k) (pdEta w) p)

set_option maxHeartbeats 400000 in
/-- Exact Fréchet derivative of `causalAdjointRep ν μ (thetaWeight k) w` on `{p | 0 < p.1}`
for any `IsDiffProfile σ H1 w`. -/
theorem hasFDerivAt_causalAdjointRep {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (k : ℕ)
    {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w) {p : Profile} (hp : 0 < p.1) :
    HasFDerivAt (causalAdjointRep ν μ (thetaWeight k) w)
      (causalAdjointFDeriv ν μ k w p) p := by
  set U : Set Profile := {q : Profile | p.1 / 2 < q.1}
  have hU_open : IsOpen U := isOpen_lt continuous_const continuous_fst
  have hpU : p ∈ U := by show p.1 / 2 < p.1; linarith
  have hU_nhds : U ∈ 𝓝 p := hU_open.mem_nhds hpU
  have hev_eq : causalAdjointRep ν μ (thetaWeight k) w =ᶠ[𝓝 p]
      fun q : Profile => ∫ t in Ioi (0 : ℝ), thetaWeight k t • flatAdjointSlice ν μ w t q := by
    filter_upwards [hU_nhds] with q hq
    have hq_pos : 0 < q.1 := by
      have : p.1 / 2 < q.1 := hq
      linarith
    simp only [causalAdjointRep, hq_pos, ↓reduceIte]
  obtain ⟨MOS, hMOS⟩ := hw.bdd_opS
  obtain ⟨MNL, hMNL⟩ := hw.bdd_nuSMul_laplaceQEta hν hσ hσH1
  obtain ⟨MQ1, hMQ1⟩ := hw.bdd_pdQ
  obtain ⟨ME1, hME1⟩ := hw.bdd_pdEta
  set C_p : ℝ := (2 / p.1) * (max MOS 0 + max MNL 0) + max MQ1 0 + max ME1 0
  set bd : ℝ → ℝ := fun t => C_p * Real.exp (-(μ.re + 1 / 2) * t)
  have hμ2 : 0 < μ.re + 1 / 2 := by linarith
  have hbd_int : Integrable bd (volume.restrict (Ioi (0 : ℝ))) :=
    (exp_neg_integrableOn_Ioi 0 hμ2).const_mul C_p
  have hF_meas : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable
      (fun t : ℝ => thetaWeight k t • flatAdjointSlice ν μ w t q)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Eventually.of_forall fun q => ?_
    exact ((continuous_thetaWeight k).stronglyMeasurable.smul
      (stronglyMeasurable_flatAdjointSlice ν μ hw.smooth.continuous.stronglyMeasurable q)).aestronglyMeasurable
  have hF_int : Integrable (fun t : ℝ => thetaWeight k t • flatAdjointSlice ν μ w t p)
      (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_thetaWeight_flatAdjointSlice ν hμ k hw.smooth.continuous hw.bdd_w p
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => thetaWeight k t • sliceFDeriv ν μ w t p)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((continuous_thetaWeight k).stronglyMeasurable.smul
      (stronglyMeasurable_sliceFDeriv ν μ hw.smooth p)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ q ∈ U,
      ‖thetaWeight k t • sliceFDeriv ν μ w t q‖ ≤ bd t := by
    refine Eventually.of_forall fun t q hq => ?_
    have hq_le : p.1 / 2 ≤ q.1 := le_of_lt hq
    rw [norm_smul]
    calc ‖thetaWeight k t‖ * ‖sliceFDeriv ν μ w t q‖
        ≤ 1 * ‖sliceFDeriv ν μ w t q‖ :=
          mul_le_mul_of_nonneg_right (norm_thetaWeight_le k t) (norm_nonneg _)
      _ = ‖sliceFDeriv ν μ w t q‖ := one_mul _
      _ ≤ (2 / p.1) * (‖flatAdjointSlice ν μ (opS w) t q‖ +
            ‖flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t q‖) +
          ‖flatAdjointSlice ν μ (pdQ w) t q‖ +
          ‖flatAdjointSlice ν μ (pdEta w) t q‖ := norm_sliceFDeriv_le ν μ w t hp hq_le
      _ ≤ (2 / p.1) * (max MOS 0 * Real.exp (-(μ.re + 1 / 2) * t) +
            max MNL 0 * Real.exp (-(μ.re + 1 / 2) * t)) +
          max MQ1 0 * Real.exp (-(μ.re + 1 / 2) * t) +
          max ME1 0 * Real.exp (-(μ.re + 1 / 2) * t) := by
            gcongr
            · exact norm_flatAdjointSlice_le ν μ hMOS t q
            · exact norm_flatAdjointSlice_le ν μ hMNL t q
            · exact norm_flatAdjointSlice_le ν μ hMQ1 t q
            · exact norm_flatAdjointSlice_le ν μ hME1 t q
      _ = bd t := by unfold bd C_p; ring
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ q ∈ U,
      HasFDerivAt (fun r : Profile => thetaWeight k t • flatAdjointSlice ν μ w t r)
        (thetaWeight k t • sliceFDeriv ν μ w t q) q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht q hq
    have hq_pos : 0 < q.1 := by
      have : p.1 / 2 < q.1 := hq
      linarith
    exact (hasFDerivAt_flatAdjointSlice hν hσ ht μ hw hq_pos).const_smul (thetaWeight k t)
  have hIntDiff := hasFDerivAt_integral_of_dominated_of_fderiv_le
    hU_nhds hF_meas hF_int hF'_meas hbound hbd_int hdiff
  refine (hIntDiff.congr_of_eventuallyEq hev_eq).congr_fderiv ?_
  have hI_opS : Integrable
      (fun t : ℝ => thetaWeight k t • flatAdjointSlice ν μ (opS w) t p)
      (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_thetaWeight_flatAdjointSlice ν hμ k
      (contDiff_opS hw.smooth).continuous hw.bdd_opS p
  have hI_lap : Integrable
      (fun t : ℝ => thetaWeight (k + 1) t •
        flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t p)
      (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_thetaWeight_flatAdjointSlice ν hμ (k + 1)
      (contDiff_nuSMul ν 1 (contDiff_laplaceQEta hw.smooth)).continuous
      (hw.bdd_nuSMul_laplaceQEta hν hσ hσH1) p
  have hI_Q : Integrable
      (fun t : ℝ => thetaWeight k t • flatAdjointSlice ν μ (pdQ w) t p)
      (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_thetaWeight_flatAdjointSlice ν hμ k
      (contDiff_pdQ hw.smooth).continuous hw.bdd_pdQ p
  have hI_Eta : Integrable
      (fun t : ℝ => thetaWeight k t • flatAdjointSlice ν μ (pdEta w) t p)
      (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_thetaWeight_flatAdjointSlice ν hμ k
      (contDiff_pdEta hw.smooth).continuous hw.bdd_pdEta p
  have hrew : (fun t : ℝ => thetaWeight k t • sliceFDeriv ν μ w t p) =
      fun t : ℝ =>
        (p.1⁻¹ • fstProfileCLM).smulRight
          (thetaWeight k t • flatAdjointSlice ν μ (opS w) t p +
            thetaWeight (k + 1) t • flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t p) +
        snd1ProfileCLM.smulRight (thetaWeight k t • flatAdjointSlice ν μ (pdQ w) t p) +
        snd2ProfileCLM.smulRight (thetaWeight k t • flatAdjointSlice ν μ (pdEta w) t p) := by
    funext t
    refine ContinuousLinearMap.ext fun dq => ?_
    simp only [sliceFDeriv, smul_apply, add_apply,
      ContinuousLinearMap.smulRight_apply, fstProfileCLM_apply, snd1ProfileCLM_apply,
      snd2ProfileCLM_apply, smul_add, smul_eq_mul, mul_comm p.1⁻¹ dq.1]
    repeat rw [smul_comm (thetaWeight k t) (dq.1 * p.1⁻¹)]
    rw [smul_comm (thetaWeight k t) dq.2.1,
      smul_comm (thetaWeight k t) dq.2.2,
      ← mul_smul (thetaWeight k t) (thetaWeight 1 t),
      thetaWeight_mul k 1 t]
  have hI_1 : Integrable
      (fun t : ℝ => (p.1⁻¹ • fstProfileCLM).smulRight
        (thetaWeight k t • flatAdjointSlice ν μ (opS w) t p +
          thetaWeight (k + 1) t • flatAdjointSlice ν μ (nuSMul ν 1 (laplaceQEta w)) t p))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (smulRightCLM (p.1⁻¹ • fstProfileCLM)).integrable_comp (integrable_add_fun hI_opS hI_lap)
  have hI_2 : Integrable
      (fun t : ℝ => snd1ProfileCLM.smulRight
        (thetaWeight k t • flatAdjointSlice ν μ (pdQ w) t p))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (smulRightCLM snd1ProfileCLM).integrable_comp hI_Q
  have hI_3 : Integrable
      (fun t : ℝ => snd2ProfileCLM.smulRight
        (thetaWeight k t • flatAdjointSlice ν μ (pdEta w) t p))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (smulRightCLM snd2ProfileCLM).integrable_comp hI_Eta
  rw [hrew, integral_add (integrable_add_fun hI_1 hI_2) hI_3, integral_add hI_1 hI_2,
    integral_smulRight (p.1⁻¹ • fstProfileCLM) (integrable_add_fun hI_opS hI_lap),
    integral_smulRight snd1ProfileCLM hI_Q,
    integral_smulRight snd2ProfileCLM hI_Eta,
    integral_add hI_opS hI_lap]
  simp only [causalAdjointFDeriv, causalAdjointRep, hp, ↓reduceIte]

/-! ### 5. Exact formulas for `pdQ`, `pdEta`, `pdS`, and `opS` on `causalAdjointRep` -/

theorem differentiableAt_causalAdjointRep {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (k : ℕ)
    {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w) {p : Profile} (hp : 0 < p.1) :
    DifferentiableAt ℝ (causalAdjointRep ν μ (thetaWeight k) w) p :=
  (hasFDerivAt_causalAdjointRep hν hσ hσH1 hμ k hw hp).differentiableAt

theorem pdQ_causalAdjointRep {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (k : ℕ)
    {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w) {p : Profile} (hp : 0 < p.1) :
    pdQ (causalAdjointRep ν μ (thetaWeight k) w) p =
      causalAdjointRep ν μ (thetaWeight k) (pdQ w) p := by
  rw [pdQ, (hasFDerivAt_causalAdjointRep hν hσ hσH1 hμ k hw hp).fderiv]
  simp [causalAdjointFDeriv]

theorem pdEta_causalAdjointRep {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (k : ℕ)
    {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w) {p : Profile} (hp : 0 < p.1) :
    pdEta (causalAdjointRep ν μ (thetaWeight k) w) p =
      causalAdjointRep ν μ (thetaWeight k) (pdEta w) p := by
  rw [pdEta, (hasFDerivAt_causalAdjointRep hν hσ hσH1 hμ k hw hp).fderiv]
  simp [causalAdjointFDeriv]

theorem pdS_causalAdjointRep {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (k : ℕ)
    {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w) {p : Profile} (hp : 0 < p.1) :
    pdS (causalAdjointRep ν μ (thetaWeight k) w) p =
      p.1⁻¹ • (causalAdjointRep ν μ (thetaWeight k) (opS w) p +
        causalAdjointRep ν μ (thetaWeight (k + 1)) (nuSMul ν 1 (laplaceQEta w)) p) := by
  rw [pdS, (hasFDerivAt_causalAdjointRep hν hσ hσH1 hμ k hw hp).fderiv]
  simp [causalAdjointFDeriv]

theorem opS_causalAdjointRep {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (k : ℕ)
    {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w) {p : Profile} (hp : 0 < p.1) :
    opS (causalAdjointRep ν μ (thetaWeight k) w) p =
      causalAdjointRep ν μ (thetaWeight k) (opS w) p +
        causalAdjointRep ν μ (thetaWeight (k + 1)) (nuSMul ν 1 (laplaceQEta w)) p := by
  rw [opS, pdS_causalAdjointRep hν hσ hσH1 hμ k hw hp, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

end FlatAdjointElemAux

end UnforcedLeray.Short.PartIIa
