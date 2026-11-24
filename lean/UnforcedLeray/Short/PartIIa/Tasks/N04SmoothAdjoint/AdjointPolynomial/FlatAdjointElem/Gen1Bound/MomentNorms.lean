import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen1Bound.CausalOperator

/-!
# Moment and Derivative Norm Bounds for Flat Leray Representatives (`MomentNorms`)

Connects `IsFlatLerayRep c σ H1 h` and `flatProjMomentNorm c h` to `ContDiff ℝ ∞`, `QPeriodic c`,
age-band support, global boundedness, and `L²(measureH c)` norm bounds for weighted derivatives of
`h` and `opS h`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0225
  UnforcedLeray.B0226

namespace FlatAdjointElemAux

/-! ### 1. Elementary profile multipliers and planar Laplacian -/

/-- Multiplication of a profile by `η = p.2.2`. -/
def etaMul (w : Profile → MeridC) : Profile → MeridC :=
  fun p => (p.2.2 : ℝ) • w p

@[simp]
theorem etaMul_zero_iter (w : Profile → MeridC) : etaMul^[0] w = w := rfl

theorem etaMul_one_iter (w : Profile → MeridC) : etaMul^[1] w = etaMul w := rfl

theorem etaMul_two_iter (w : Profile → MeridC) : etaMul^[2] w = etaMul (etaMul w) := rfl

theorem norm_etaMul_iter (j : ℕ) (w : Profile → MeridC) (p : Profile) :
    ‖(etaMul^[j] w) p‖ = |p.2.2| ^ j * ‖w p‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', etaMul, norm_smul, Real.norm_eq_abs, ih, pow_succ', mul_assoc]

/-- Planar Laplacian `(∂_q² + ∂_η²) w` on profiles. -/
def laplaceQEta (w : Profile → MeridC) : Profile → MeridC :=
  fun p => pdQ (pdQ w) p + pdEta (pdEta w) p

/-! ### 2. Smoothness, periodicity, and band-support preservation -/

theorem contDiff_pdS {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (pdS w) :=
  ((contDiff_infty_iff_fderiv.1 hw).2).clm_apply contDiff_const

theorem contDiff_pdQ {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (pdQ w) :=
  ((contDiff_infty_iff_fderiv.1 hw).2).clm_apply contDiff_const

theorem contDiff_pdEta {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (pdEta w) :=
  ((contDiff_infty_iff_fderiv.1 hw).2).clm_apply contDiff_const

theorem contDiff_opS {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (opS w) :=
  contDiff_fst.smul (contDiff_pdS hw)

theorem contDiff_opS_iter (a : ℕ) {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (opS^[a] w) := by
  induction a with
  | zero => exact hw
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    exact contDiff_opS ih

theorem contDiff_etaMul {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (etaMul w) :=
  (contDiff_snd.comp contDiff_snd).smul hw

theorem contDiff_etaMul_iter (j : ℕ) {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (etaMul^[j] w) := by
  induction j with
  | zero => exact hw
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact contDiff_etaMul ih

theorem contDiff_nuSMul (ν : ℝ) (l : ℕ) {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (nuSMul ν l w) := by
  have h1 : nuSMul ν l w = fun p => ((ν * p.1) ^ l : ℝ) • w p := by
    funext p
    simp only [nuSMul]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) ((ν * p.1) ^ l) (w p)).symm
  rw [h1]
  exact ((contDiff_const.mul contDiff_fst).pow l).smul hw

theorem contDiff_laplaceQEta {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (laplaceQEta w) :=
  (contDiff_pdQ (contDiff_pdQ hw)).add (contDiff_pdEta (contDiff_pdEta hw))

theorem periodic_fderiv_apply {c : ℝ} {w : Profile → MeridC} (hw : QPeriodic c w) (v : Profile) :
    QPeriodic c (fun p => fderiv ℝ w p v) := by
  intro p
  have hfun : (fun q : Profile => w (q + ((0 : ℝ), c, (0 : ℝ)))) = w := by
    funext q
    have hq : q + ((0 : ℝ), c, (0 : ℝ)) = (q.1, q.2.1 + c, q.2.2) := by
      ext <;> simp
    rw [hq]
    exact hw q
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := w) (x := p) ((0 : ℝ), c, (0 : ℝ))
  rw [hfun] at h
  have hp : p + ((0 : ℝ), c, (0 : ℝ)) = (p.1, p.2.1 + c, p.2.2) := by
    ext <;> simp
  rw [hp] at h
  exact congrArg (fun L : Profile →L[ℝ] MeridC => L v) h.symm

theorem periodic_pdS {c : ℝ} {w : Profile → MeridC} (hw : QPeriodic c w) :
    QPeriodic c (pdS w) := periodic_fderiv_apply hw (1, 0, 0)

theorem periodic_pdQ {c : ℝ} {w : Profile → MeridC} (hw : QPeriodic c w) :
    QPeriodic c (pdQ w) := periodic_fderiv_apply hw (0, 1, 0)

theorem periodic_pdEta {c : ℝ} {w : Profile → MeridC} (hw : QPeriodic c w) :
    QPeriodic c (pdEta w) := periodic_fderiv_apply hw (0, 0, 1)

theorem periodic_opS {c : ℝ} {w : Profile → MeridC} (hw : QPeriodic c w) :
    QPeriodic c (opS w) := by
  intro p
  simp only [opS, periodic_pdS hw p]

theorem periodic_opS_iter {c : ℝ} (a : ℕ) {w : Profile → MeridC} (hw : QPeriodic c w) :
    QPeriodic c (opS^[a] w) := by
  induction a with
  | zero => exact hw
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    exact periodic_opS ih

theorem periodic_etaMul {c : ℝ} {w : Profile → MeridC} (hw : QPeriodic c w) :
    QPeriodic c (etaMul w) := by
  intro p
  simp only [etaMul, hw p]

theorem periodic_etaMul_iter {c : ℝ} (j : ℕ) {w : Profile → MeridC} (hw : QPeriodic c w) :
    QPeriodic c (etaMul^[j] w) := by
  induction j with
  | zero => exact hw
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact periodic_etaMul ih

theorem periodic_nuSMul {c : ℝ} (ν : ℝ) (l : ℕ) {w : Profile → MeridC} (hw : QPeriodic c w) :
    QPeriodic c (nuSMul ν l w) := by
  intro p
  simp only [nuSMul, hw p]

theorem periodic_laplaceQEta {c : ℝ} {w : Profile → MeridC} (hw : QPeriodic c w) :
    QPeriodic c (laplaceQEta w) := by
  intro p
  simp only [laplaceQEta, periodic_pdQ (periodic_pdQ hw) p, periodic_pdEta (periodic_pdEta hw) p]

theorem support_s_fderiv_apply {σ H1 : ℝ} {w : Profile → MeridC}
    (hw : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) (v : Profile) :
    ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → fderiv ℝ w p v = 0 := by
  intro p hp
  have hopen : IsOpen {q : Profile | q.1 < σ ∨ H1 < q.1} :=
    (isOpen_lt continuous_fst continuous_const).union (isOpen_lt continuous_const continuous_fst)
  have hev : w =ᶠ[𝓝 p] fun _ => (0 : MeridC) := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact hw q hq
  rw [hev.fderiv_eq]
  simp

theorem support_s_pdS {σ H1 : ℝ} {w : Profile → MeridC}
    (hw : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) :
    ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → pdS w p = 0 :=
  support_s_fderiv_apply hw (1, 0, 0)

theorem support_s_pdQ {σ H1 : ℝ} {w : Profile → MeridC}
    (hw : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) :
    ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → pdQ w p = 0 :=
  support_s_fderiv_apply hw (0, 1, 0)

theorem support_s_pdEta {σ H1 : ℝ} {w : Profile → MeridC}
    (hw : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) :
    ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → pdEta w p = 0 :=
  support_s_fderiv_apply hw (0, 0, 1)

theorem support_s_opS {σ H1 : ℝ} {w : Profile → MeridC}
    (hw : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) :
    ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → opS w p = 0 := by
  intro p hp
  simp only [opS, support_s_pdS hw p hp, smul_zero]

theorem support_s_opS_iter {σ H1 : ℝ} (a : ℕ) {w : Profile → MeridC}
    (hw : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) :
    ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → (opS^[a] w) p = 0 := by
  induction a with
  | zero => exact hw
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    exact support_s_opS ih

theorem support_s_etaMul {σ H1 : ℝ} {w : Profile → MeridC}
    (hw : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) :
    ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → etaMul w p = 0 := by
  intro p hp
  simp only [etaMul, hw p hp, smul_zero]

theorem support_s_etaMul_iter {σ H1 : ℝ} (j : ℕ) {w : Profile → MeridC}
    (hw : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) :
    ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → (etaMul^[j] w) p = 0 := by
  induction j with
  | zero => exact hw
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact support_s_etaMul ih

theorem support_s_nuSMul {σ H1 : ℝ} (ν : ℝ) (l : ℕ) {w : Profile → MeridC}
    (hw : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) :
    ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → nuSMul ν l w p = 0 := by
  intro p hp
  simp only [nuSMul, hw p hp, smul_zero]

theorem support_s_laplaceQEta {σ H1 : ℝ} {w : Profile → MeridC}
    (hw : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) :
    ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → laplaceQEta w p = 0 := by
  intro p hp
  simp only [laplaceQEta, support_s_pdQ (support_s_pdQ hw) p hp,
    support_s_pdEta (support_s_pdEta hw) p hp, add_zero]

/-! ### 3. Commutation of differential operators with `opS`, `etaMul`, and `nuSMul` -/

theorem fderiv_apply_comm {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) (u v : Profile)
    (p : Profile) :
    fderiv ℝ (fun q => fderiv ℝ w q u) p v = fderiv ℝ (fun q => fderiv ℝ w q v) p u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ w) p :=
    ((contDiff_infty_iff_fderiv.1 hw).2).differentiable (by simp) p
  have h1 : HasFDerivAt (fun q => (ContinuousLinearMap.apply ℝ MeridC u) (fderiv ℝ w q))
      ((ContinuousLinearMap.apply ℝ MeridC u).comp (fderiv ℝ (fderiv ℝ w) p)) p :=
    (ContinuousLinearMap.apply ℝ MeridC u).hasFDerivAt.comp p hd.hasFDerivAt
  have h2 : HasFDerivAt (fun q => (ContinuousLinearMap.apply ℝ MeridC v) (fderiv ℝ w q))
      ((ContinuousLinearMap.apply ℝ MeridC v).comp (fderiv ℝ (fderiv ℝ w) p)) p :=
    (ContinuousLinearMap.apply ℝ MeridC v).hasFDerivAt.comp p hd.hasFDerivAt
  change fderiv ℝ (fun q => (ContinuousLinearMap.apply ℝ MeridC u) (fderiv ℝ w q)) p v =
    fderiv ℝ (fun q => (ContinuousLinearMap.apply ℝ MeridC v) (fderiv ℝ w q)) p u
  rw [h1.fderiv, h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  have hsymm := (hw.contDiffAt (x := p)).isSymmSndFDerivAt (by simp)
  exact hsymm.eq v u

theorem pdS_pdQ_comm {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) (p : Profile) :
    pdS (pdQ w) p = pdQ (pdS w) p :=
  fderiv_apply_comm hw (0, 1, 0) (1, 0, 0) p

theorem pdS_pdEta_comm {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) (p : Profile) :
    pdS (pdEta w) p = pdEta (pdS w) p :=
  fderiv_apply_comm hw (0, 0, 1) (1, 0, 0) p

theorem pdQ_pdEta_comm {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) (p : Profile) :
    pdQ (pdEta w) p = pdEta (pdQ w) p :=
  fderiv_apply_comm hw (0, 0, 1) (0, 1, 0) p

theorem opS_pdQ_comm {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    opS (pdQ w) = pdQ (opS w) := by
  funext p
  have hfst : HasFDerivAt (fun q : Profile => q.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hd : DifferentiableAt ℝ (pdS w) p := (contDiff_pdS hw).differentiable (by simp) p
  have hsmul := hfst.smul hd.hasFDerivAt
  change p.1 • pdS (pdQ w) p = fderiv ℝ ((fun q : Profile => q.1) • pdS w) p (0, 1, 0)
  rw [hsmul.fderiv, pdS_pdQ_comm hw p]
  simp [pdQ]

theorem opS_pdEta_comm {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    opS (pdEta w) = pdEta (opS w) := by
  funext p
  have hfst : HasFDerivAt (fun q : Profile => q.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hd : DifferentiableAt ℝ (pdS w) p := (contDiff_pdS hw).differentiable (by simp) p
  have hsmul := hfst.smul hd.hasFDerivAt
  change p.1 • pdS (pdEta w) p = fderiv ℝ ((fun q : Profile => q.1) • pdS w) p (0, 0, 1)
  rw [hsmul.fderiv, pdS_pdEta_comm hw p]
  simp [pdEta]

theorem opS_laplaceQEta_comm {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    opS (laplaceQEta w) = laplaceQEta (opS w) := by
  funext p
  have h1 : DifferentiableAt ℝ (pdQ (pdQ w)) p :=
    (contDiff_pdQ (contDiff_pdQ hw)).differentiable (by simp) p
  have h2 : DifferentiableAt ℝ (pdEta (pdEta w)) p :=
    (contDiff_pdEta (contDiff_pdEta hw)).differentiable (by simp) p
  change p.1 • fderiv ℝ (pdQ (pdQ w) + pdEta (pdEta w)) p (1, 0, 0) =
    pdQ (pdQ (opS w)) p + pdEta (pdEta (opS w)) p
  rw [(h1.hasFDerivAt.add h2.hasFDerivAt).fderiv, add_apply, smul_add]
  change opS (pdQ (pdQ w)) p + opS (pdEta (pdEta w)) p = _
  rw [opS_pdQ_comm (contDiff_pdQ hw), opS_pdQ_comm hw,
    opS_pdEta_comm (contDiff_pdEta hw), opS_pdEta_comm hw]

theorem opS_etaMul_comm {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    opS (etaMul w) = etaMul (opS w) := by
  funext p
  have heta : HasFDerivAt (fun q : Profile => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  have hd : DifferentiableAt ℝ w p := hw.differentiable (by simp) p
  have hsmul := heta.smul hd.hasFDerivAt
  change p.1 • fderiv ℝ ((fun q : Profile => q.2.2) • w) p (1, 0, 0) = p.2.2 • (p.1 • pdS w p)
  rw [hsmul.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', zero_smul, add_zero, smul_apply]
  rw [smul_comm]
  rfl

theorem pdQ_etaMul_comm {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    pdQ (etaMul w) = etaMul (pdQ w) := by
  funext p
  have heta : HasFDerivAt (fun q : Profile => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  have hd : DifferentiableAt ℝ w p := hw.differentiable (by simp) p
  have hsmul := heta.smul hd.hasFDerivAt
  change fderiv ℝ ((fun q : Profile => q.2.2) • w) p (0, 1, 0) = p.2.2 • pdQ w p
  rw [hsmul.fderiv]
  simp [pdQ]

theorem pdEta_etaMul_eq {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    pdEta (etaMul w) = fun p => w p + etaMul (pdEta w) p := by
  funext p
  have heta : HasFDerivAt (fun q : Profile => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  have hd : DifferentiableAt ℝ w p := hw.differentiable (by simp) p
  have hsmul := heta.smul hd.hasFDerivAt
  change fderiv ℝ ((fun q : Profile => q.2.2) • w) p (0, 0, 1) = w p + p.2.2 • pdEta w p
  rw [hsmul.fderiv]
  simp [pdEta, add_comm]

theorem opS_nuSMul_one_eq (ν : ℝ) {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w) :
    opS (nuSMul ν 1 w) = fun p => nuSMul ν 1 w p + nuSMul ν 1 (opS w) p := by
  funext p
  have hfun : nuSMul ν 1 w = (fun q : Profile => ν * q.1) • w :=
    funext (nuSMul_one_apply ν w)
  have hfst : HasFDerivAt (fun q : Profile => ν * q.1)
      (ν • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt).const_mul ν
  have hd : DifferentiableAt ℝ w p := hw.differentiable (by simp) p
  have hsmul := hfst.smul hd.hasFDerivAt
  change p.1 • fderiv ℝ (nuSMul ν 1 w) p (1, 0, 0) =
    nuSMul ν 1 w p + nuSMul ν 1 (opS w) p
  rw [hfun, hsmul.fderiv]
  simp only [nuSMul_one_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul, mul_one, opS, pdS]
  rw [smul_add, smul_smul, smul_smul]
  change (p.1 * (ν * p.1)) • (fderiv ℝ w p) (1, 0, 0) + (p.1 * ν) • w p =
    (ν * p.1) • w p + (ν * p.1) • p.1 • (fderiv ℝ w p) (1, 0, 0)
  rw [ ← mul_smul, mul_comm p.1 (ν * p.1), mul_comm p.1 ν]
  abel

/-! ### 4. Iterated Fréchet derivative bounds for `pdQ` and `pdEta` -/

theorem norm_iteratedFDeriv_fderiv_apply_le {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w)
    {v : Profile} (hv : ‖v‖ ≤ 1) (m : ℕ) (p : Profile) :
    ‖iteratedFDeriv ℝ m (fun q => fderiv ℝ w q v) p‖ ≤ ‖iteratedFDeriv ℝ (m + 1) w p‖ := by
  have hcda : ContDiffAt ℝ ∞ (fderiv ℝ w) p :=
    ((contDiff_infty_iff_fderiv.1 hw).2).contDiffAt
  have h1 := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ w)
    (c := v) (x := p) (N := ∞) (n := m) hcda (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h1
  calc ‖iteratedFDeriv ℝ m (fun q => fderiv ℝ w q v) p‖
      ≤ ‖v‖ * ‖iteratedFDeriv ℝ (m + 1) w p‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ (m + 1) w p‖ :=
        mul_le_mul_of_nonneg_right hv (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (m + 1) w p‖ := one_mul _

theorem norm_iteratedFDeriv_pdQ_le {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w)
    (m : ℕ) (p : Profile) :
    ‖iteratedFDeriv ℝ m (pdQ w) p‖ ≤ ‖iteratedFDeriv ℝ (m + 1) w p‖ := by
  refine norm_iteratedFDeriv_fderiv_apply_le hw ?_ m p
  simp [Prod.norm_def]

theorem norm_iteratedFDeriv_pdEta_le {w : Profile → MeridC} (hw : ContDiff ℝ ∞ w)
    (m : ℕ) (p : Profile) :
    ‖iteratedFDeriv ℝ m (pdEta w) p‖ ≤ ‖iteratedFDeriv ℝ (m + 1) w p‖ := by
  refine norm_iteratedFDeriv_fderiv_apply_le hw ?_ m p
  simp [Prod.norm_def]

/-! ### 5. Admissible source profiles `IsAdmSource` bounded by `flatProjMomentNorm` -/

/-- A profile `u : Profile → MeridC` controlled by derivatives of order `m < 5` of `opS^[a] h`
(`a < 2`) for a flat Leray representative `h`. -/
structure IsBaseDeriv {c σ H1 : ℝ} (h : Profile → MeridC) (a m : ℕ)
    (u : Profile → MeridC) : Prop where
  ha : a ∈ Finset.range 2
  hm : m ∈ Finset.range 5
  smooth : ContDiff ℝ ∞ u
  periodic : QPeriodic c u
  support_s : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → u p = 0
  norm_le : ∀ p : Profile, ‖u p‖ ≤ ‖iteratedFDeriv ℝ m (opS^[a] h) p‖

theorem isBaseDeriv_base {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 0 (opS^[a] h) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_opS_iter a hh.smooth
  periodic := periodic_opS_iter a hh.periodic
  support_s := support_s_opS_iter a hh.support_s
  norm_le p := (norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := opS^[a] h) (x := p)).symm.le

theorem isBaseDeriv_pdQ {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 1 (pdQ (opS^[a] h)) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdQ (contDiff_opS_iter a hh.smooth)
  periodic := periodic_pdQ (periodic_opS_iter a hh.periodic)
  support_s := support_s_pdQ (support_s_opS_iter a hh.support_s)
  norm_le p := by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact norm_iteratedFDeriv_pdQ_le (contDiff_opS_iter a hh.smooth) 0 p

theorem isBaseDeriv_pdEta {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 1 (pdEta (opS^[a] h)) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdEta (contDiff_opS_iter a hh.smooth)
  periodic := periodic_pdEta (periodic_opS_iter a hh.periodic)
  support_s := support_s_pdEta (support_s_opS_iter a hh.support_s)
  norm_le p := by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact norm_iteratedFDeriv_pdEta_le (contDiff_opS_iter a hh.smooth) 0 p

theorem isBaseDeriv_pdQ_pdQ {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 2 (pdQ (pdQ (opS^[a] h))) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdQ (contDiff_pdQ (contDiff_opS_iter a hh.smooth))
  periodic := periodic_pdQ (periodic_pdQ (periodic_opS_iter a hh.periodic))
  support_s := support_s_pdQ (support_s_pdQ (support_s_opS_iter a hh.support_s))
  norm_le p := by
    have h0 := contDiff_opS_iter a hh.smooth
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdQ_le (contDiff_pdQ h0) 0 p).trans
      (norm_iteratedFDeriv_pdQ_le h0 1 p)

theorem isBaseDeriv_pdEta_pdEta {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 2 (pdEta (pdEta (opS^[a] h))) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdEta (contDiff_pdEta (contDiff_opS_iter a hh.smooth))
  periodic := periodic_pdEta (periodic_pdEta (periodic_opS_iter a hh.periodic))
  support_s := support_s_pdEta (support_s_pdEta (support_s_opS_iter a hh.support_s))
  norm_le p := by
    have h0 := contDiff_opS_iter a hh.smooth
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdEta_le (contDiff_pdEta h0) 0 p).trans
      (norm_iteratedFDeriv_pdEta_le h0 1 p)

theorem isBaseDeriv_pdEta_pdQ {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 2 (pdEta (pdQ (opS^[a] h))) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdEta (contDiff_pdQ (contDiff_opS_iter a hh.smooth))
  periodic := periodic_pdEta (periodic_pdQ (periodic_opS_iter a hh.periodic))
  support_s := support_s_pdEta (support_s_pdQ (support_s_opS_iter a hh.support_s))
  norm_le p := by
    have h0 := contDiff_opS_iter a hh.smooth
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdEta_le (contDiff_pdQ h0) 0 p).trans
      (norm_iteratedFDeriv_pdQ_le h0 1 p)

theorem isBaseDeriv_pdQ3 {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 3 (pdQ (pdQ (pdQ (opS^[a] h)))) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdQ (contDiff_pdQ (contDiff_pdQ (contDiff_opS_iter a hh.smooth)))
  periodic := periodic_pdQ (periodic_pdQ (periodic_pdQ (periodic_opS_iter a hh.periodic)))
  support_s := support_s_pdQ (support_s_pdQ (support_s_pdQ (support_s_opS_iter a hh.support_s)))
  norm_le p := by
    have h0 := contDiff_opS_iter a hh.smooth
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdQ_le (contDiff_pdQ (contDiff_pdQ h0)) 0 p).trans
      ((norm_iteratedFDeriv_pdQ_le (contDiff_pdQ h0) 1 p).trans
        (norm_iteratedFDeriv_pdQ_le h0 2 p))

theorem isBaseDeriv_pdEta_pdEta_pdQ {c σ H1 : ℝ} {h : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 3 (pdEta (pdEta (pdQ (opS^[a] h)))) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdEta (contDiff_pdEta (contDiff_pdQ (contDiff_opS_iter a hh.smooth)))
  periodic := periodic_pdEta (periodic_pdEta (periodic_pdQ (periodic_opS_iter a hh.periodic)))
  support_s := support_s_pdEta (support_s_pdEta (support_s_pdQ (support_s_opS_iter a hh.support_s)))
  norm_le p := by
    have h0 := contDiff_opS_iter a hh.smooth
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdEta_le (contDiff_pdEta (contDiff_pdQ h0)) 0 p).trans
      ((norm_iteratedFDeriv_pdEta_le (contDiff_pdQ h0) 1 p).trans
        (norm_iteratedFDeriv_pdQ_le h0 2 p))

theorem isBaseDeriv_pdQ_pdQ_pdEta {c σ H1 : ℝ} {h : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 3 (pdQ (pdQ (pdEta (opS^[a] h)))) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdQ (contDiff_pdQ (contDiff_pdEta (contDiff_opS_iter a hh.smooth)))
  periodic := periodic_pdQ (periodic_pdQ (periodic_pdEta (periodic_opS_iter a hh.periodic)))
  support_s := support_s_pdQ (support_s_pdQ (support_s_pdEta (support_s_opS_iter a hh.support_s)))
  norm_le p := by
    have h0 := contDiff_opS_iter a hh.smooth
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdQ_le (contDiff_pdQ (contDiff_pdEta h0)) 0 p).trans
      ((norm_iteratedFDeriv_pdQ_le (contDiff_pdEta h0) 1 p).trans
        (norm_iteratedFDeriv_pdEta_le h0 2 p))

theorem isBaseDeriv_pdEta3 {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 3 (pdEta (pdEta (pdEta (opS^[a] h)))) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdEta (contDiff_pdEta (contDiff_pdEta (contDiff_opS_iter a hh.smooth)))
  periodic := periodic_pdEta (periodic_pdEta (periodic_pdEta (periodic_opS_iter a hh.periodic)))
  support_s := support_s_pdEta (support_s_pdEta (support_s_pdEta (support_s_opS_iter a hh.support_s)))
  norm_le p := by
    have h0 := contDiff_opS_iter a hh.smooth
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdEta_le (contDiff_pdEta (contDiff_pdEta h0)) 0 p).trans
      ((norm_iteratedFDeriv_pdEta_le (contDiff_pdEta h0) 1 p).trans
        (norm_iteratedFDeriv_pdEta_le h0 2 p))

theorem isBaseDeriv_pdQ4 {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 4 (pdQ (pdQ (pdQ (pdQ (opS^[a] h))))) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdQ (contDiff_pdQ (contDiff_pdQ (contDiff_pdQ (contDiff_opS_iter a hh.smooth))))
  periodic := periodic_pdQ (periodic_pdQ (periodic_pdQ (periodic_pdQ (periodic_opS_iter a hh.periodic))))
  support_s := support_s_pdQ (support_s_pdQ (support_s_pdQ (support_s_pdQ
    (support_s_opS_iter a hh.support_s))))
  norm_le p := by
    have h0 := contDiff_opS_iter a hh.smooth
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdQ_le (contDiff_pdQ (contDiff_pdQ (contDiff_pdQ h0))) 0 p).trans
      ((norm_iteratedFDeriv_pdQ_le (contDiff_pdQ (contDiff_pdQ h0)) 1 p).trans
        ((norm_iteratedFDeriv_pdQ_le (contDiff_pdQ h0) 2 p).trans
          (norm_iteratedFDeriv_pdQ_le h0 3 p)))

theorem isBaseDeriv_pdQ2_pdEta2 {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 4 (pdQ (pdQ (pdEta (pdEta (opS^[a] h))))) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdQ (contDiff_pdQ (contDiff_pdEta (contDiff_pdEta
    (contDiff_opS_iter a hh.smooth))))
  periodic := periodic_pdQ (periodic_pdQ (periodic_pdEta (periodic_pdEta
    (periodic_opS_iter a hh.periodic))))
  support_s := support_s_pdQ (support_s_pdQ (support_s_pdEta (support_s_pdEta
    (support_s_opS_iter a hh.support_s))))
  norm_le p := by
    have h0 := contDiff_opS_iter a hh.smooth
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdQ_le (contDiff_pdQ (contDiff_pdEta (contDiff_pdEta h0))) 0 p).trans
      ((norm_iteratedFDeriv_pdQ_le (contDiff_pdEta (contDiff_pdEta h0)) 1 p).trans
        ((norm_iteratedFDeriv_pdEta_le (contDiff_pdEta h0) 2 p).trans
          (norm_iteratedFDeriv_pdEta_le h0 3 p)))

theorem isBaseDeriv_pdEta2_pdQ2 {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 4 (pdEta (pdEta (pdQ (pdQ (opS^[a] h))))) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdEta (contDiff_pdEta (contDiff_pdQ (contDiff_pdQ
    (contDiff_opS_iter a hh.smooth))))
  periodic := periodic_pdEta (periodic_pdEta (periodic_pdQ (periodic_pdQ
    (periodic_opS_iter a hh.periodic))))
  support_s := support_s_pdEta (support_s_pdEta (support_s_pdQ (support_s_pdQ
    (support_s_opS_iter a hh.support_s))))
  norm_le p := by
    have h0 := contDiff_opS_iter a hh.smooth
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdEta_le (contDiff_pdEta (contDiff_pdQ (contDiff_pdQ h0))) 0 p).trans
      ((norm_iteratedFDeriv_pdEta_le (contDiff_pdQ (contDiff_pdQ h0)) 1 p).trans
        ((norm_iteratedFDeriv_pdQ_le (contDiff_pdQ h0) 2 p).trans
          (norm_iteratedFDeriv_pdQ_le h0 3 p)))

theorem isBaseDeriv_pdEta4 {c σ H1 : ℝ} {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (a : ℕ) (ha : a ∈ Finset.range 2) :
    IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a 4 (pdEta (pdEta (pdEta (pdEta (opS^[a] h))))) where
  ha := ha
  hm := Finset.mem_range.mpr (by omega)
  smooth := contDiff_pdEta (contDiff_pdEta (contDiff_pdEta (contDiff_pdEta
    (contDiff_opS_iter a hh.smooth))))
  periodic := periodic_pdEta (periodic_pdEta (periodic_pdEta (periodic_pdEta
    (periodic_opS_iter a hh.periodic))))
  support_s := support_s_pdEta (support_s_pdEta (support_s_pdEta (support_s_pdEta
    (support_s_opS_iter a hh.support_s))))
  norm_le p := by
    have h0 := contDiff_opS_iter a hh.smooth
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (norm_iteratedFDeriv_pdEta_le (contDiff_pdEta (contDiff_pdEta (contDiff_pdEta h0))) 0 p).trans
      ((norm_iteratedFDeriv_pdEta_le (contDiff_pdEta (contDiff_pdEta h0)) 1 p).trans
        ((norm_iteratedFDeriv_pdEta_le (contDiff_pdEta h0) 2 p).trans
          (norm_iteratedFDeriv_pdEta_le h0 3 p)))

/-! ### 6. Pointwise and `L²(measureH c)` bounds for `nuSMul ν l (etaMul^[j] u)` -/

theorem norm_nuSMul_le_of_support_s {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (l : ℕ) {w : Profile → MeridC}
    (hw_supp : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → w p = 0) (p : Profile) :
    ‖nuSMul ν l w p‖ ≤ (ν * H1) ^ l * ‖w p‖ := by
  by_cases hp : p.1 < σ ∨ H1 < p.1
  · rw [support_s_nuSMul ν l hw_supp p hp, hw_supp p hp, norm_zero, mul_zero]
  · rw [not_or, not_lt, not_lt] at hp
    have hp_pos : 0 < p.1 := hσ.trans_le hp.1
    have hνp : 0 ≤ ν * p.1 := (mul_pos hν hp_pos).le
    have hle : ν * p.1 ≤ ν * H1 := mul_le_mul_of_nonneg_left hp.2 hν.le
    rw [nuSMul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hνp l)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hνp hle l) (norm_nonneg _)

theorem norm_nuSMul_etaMul_le {c σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {h u : Profile → MeridC} {a m : ℕ}
    (hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m u)
    (j l : ℕ) (p : Profile) :
    ‖nuSMul ν l (etaMul^[j] u) p‖ ≤
      (ν * H1) ^ l * (|p.2.2| ^ j * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖) := by
  have hH1 : 0 < H1 := hσ.trans_le hσH1
  have h1 := norm_nuSMul_le_of_support_s hν hσ l (support_s_etaMul_iter j hu.support_s) p
  rw [norm_etaMul_iter] at h1
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left (hu.norm_le p) (by positivity)

theorem bounded_nuSMul_etaMul {c σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {h u : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) {a m : ℕ}
    (hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m u)
    {j : ℕ} (hj : j ∈ Finset.range 3) (l : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : Profile, ‖nuSMul ν l (etaMul^[j] u) p‖ ≤ B := by
  have hH1 : 0 < H1 := hσ.trans_le hσH1
  obtain ⟨B0, hB0⟩ := hh.bounded_moments a hu.ha j hj m hu.hm
  refine ⟨(ν * H1) ^ l * max B0 0, by positivity, fun p => ?_⟩
  refine (norm_nuSMul_etaMul_le hν hσ hσH1 hu j l p).trans ?_
  exact mul_le_mul_of_nonneg_left ((hB0 p).trans (le_max_left B0 0)) (by positivity)

theorem toReal_eLpNorm_two_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} {f : α → E} (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hm2 : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) μ := hf.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun _ => by positivity) hm2,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.toReal_pow]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat]
  norm_num

theorem memLp_norm_toLp_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [Lp.norm_toLp, toReal_eLpNorm_two_sq hf.aestronglyMeasurable]

theorem single_le_flatProjMomentNorm (c : ℝ) (h : Profile → MeridC)
    {a j m : ℕ} (ha : a ∈ Finset.range 2) (hj : j ∈ Finset.range 3) (hm : m ∈ Finset.range 5) :
    (∫ p, (|p.2.2| ^ j) ^ 2 *
      ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
      flatProjMomentNorm c h := by
  unfold flatProjMomentNorm
  have hnn : ∀ a' j' m' : ℕ, 0 ≤ (∫ p, (|p.2.2| ^ j') ^ 2 *
      ‖iteratedFDeriv ℝ m' (opS^[a'] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) :=
    fun a' j' m' => Real.rpow_nonneg (integral_nonneg fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _
  have h1 : (∫ p, (|p.2.2| ^ j) ^ 2 *
      ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
      ∑ m' ∈ Finset.range 5, (∫ p, (|p.2.2| ^ j) ^ 2 *
        ‖iteratedFDeriv ℝ m' (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) :=
    Finset.single_le_sum (fun m' _ => hnn a j m') hm
  have h2 : ∑ m' ∈ Finset.range 5, (∫ p, (|p.2.2| ^ j) ^ 2 *
      ‖iteratedFDeriv ℝ m' (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
      ∑ j' ∈ Finset.range 3, ∑ m' ∈ Finset.range 5, (∫ p, (|p.2.2| ^ j') ^ 2 *
        ‖iteratedFDeriv ℝ m' (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) :=
    Finset.single_le_sum (fun j' _ => Finset.sum_nonneg fun m' _ => hnn a j' m') hj
  have h3 : ∑ j' ∈ Finset.range 3, ∑ m' ∈ Finset.range 5, (∫ p, (|p.2.2| ^ j') ^ 2 *
      ‖iteratedFDeriv ℝ m' (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
      ∑ a' ∈ Finset.range 2, ∑ j' ∈ Finset.range 3, ∑ m' ∈ Finset.range 5,
        (∫ p, (|p.2.2| ^ j') ^ 2 *
          ‖iteratedFDeriv ℝ m' (opS^[a'] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) :=
    Finset.single_le_sum
      (fun a' _ => Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun m' _ => hnn a' j' m') ha
  exact h1.trans (h2.trans h3)

theorem memLp_nuSMul_etaMul {c σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {h u : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) {a m : ℕ}
    (hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m u)
    {j : ℕ} (hj : j ∈ Finset.range 3) (l : ℕ) :
    MemLp (nuSMul ν l (etaMul^[j] u)) 2 (measureH c) := by
  have hw_cont : Continuous (nuSMul ν l (etaMul^[j] u)) :=
    (contDiff_nuSMul ν l (contDiff_etaMul_iter j hu.smooth)).continuous
  rw [memLp_two_iff_integrable_sq_norm hw_cont.aestronglyMeasurable]
  have hint := (hh.integrable_moments a hu.ha j hj m hu.hm).const_mul (((ν * H1) ^ l) ^ 2)
  refine Integrable.mono' hint (hw_cont.norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hle := norm_nuSMul_etaMul_le hν hσ hσH1 hu j l p
  have hsq : ‖nuSMul ν l (etaMul^[j] u) p‖ ^ 2 ≤
      ((ν * H1) ^ l * (|p.2.2| ^ j * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  refine hsq.trans_eq ?_
  ring

theorem norm_toLp_nuSMul_etaMul_le {c σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {h u : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) {a m : ℕ}
    (hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m u)
    {j : ℕ} (hj : j ∈ Finset.range 3) (l : ℕ) :
    ‖(memLp_nuSMul_etaMul hν hσ hσH1 hh hu hj l).toLp (nuSMul ν l (etaMul^[j] u))‖ ≤
      (ν * H1) ^ l * flatProjMomentNorm c h := by
  have hH1 : 0 < H1 := hσ.trans_le hσH1
  set hm := memLp_nuSMul_etaMul hν hσ hσH1 hh hu hj l
  have hsq_eq := memLp_norm_toLp_sq hm
  have hint_w : Integrable (fun p => ‖nuSMul ν l (etaMul^[j] u) p‖ ^ 2) (measureH c) :=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hint_m := hh.integrable_moments a hu.ha j hj m hu.hm
  have hint_le : ∫ p, ‖nuSMul ν l (etaMul^[j] u) p‖ ^ 2 ∂(measureH c) ≤
      ((ν * H1) ^ l) ^ 2 *
        ∫ p, (|p.2.2| ^ j) ^ 2 * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2 ∂(measureH c) := by
    rw [← integral_const_mul]
    refine integral_mono_ae hint_w (hint_m.const_mul _) (Eventually.of_forall fun p => ?_)
    have hle := norm_nuSMul_etaMul_le hν hσ hσH1 hu j l p
    calc ‖nuSMul ν l (etaMul^[j] u) p‖ ^ 2
        ≤ ((ν * H1) ^ l * (|p.2.2| ^ j * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = ((ν * H1) ^ l) ^ 2 *
          ((|p.2.2| ^ j) ^ 2 * ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2) := by ring
  have h1 : ‖hm.toLp (nuSMul ν l (etaMul^[j] u))‖ =
      (‖hm.toLp (nuSMul ν l (etaMul^[j] u))‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  rw [h1, hsq_eq]
  have h2 : (∫ p, ‖nuSMul ν l (etaMul^[j] u) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
      (((ν * H1) ^ l) ^ 2 *
        ∫ p, (|p.2.2| ^ j) ^ 2 *
          ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by positivity)
  have h3 : (((ν * H1) ^ l) ^ 2 *
        ∫ p, (|p.2.2| ^ j) ^ 2 *
          ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) =
      (ν * H1) ^ l *
        (∫ p, (|p.2.2| ^ j) ^ 2 *
          ‖iteratedFDeriv ℝ m (opS^[a] h) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (sq_nonneg _)
      (integral_nonneg fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  rw [h3] at h2
  refine h2.trans ?_
  exact mul_le_mul_of_nonneg_left
    (single_le_flatProjMomentNorm c h hu.ha hj hu.hm) (by positivity)

/-- Combined `MemLp` for `causalAdjointRep ν μ (thetaWeight k) (nuSMul ν l (etaMul^[j] u))`. -/
theorem memLp_causal_baseDeriv {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h u : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) {a m : ℕ}
    (hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m u)
    {j : ℕ} (hj : j ∈ Finset.range 3) (k l : ℕ) :
    MemLp (causalAdjointRep ν μ (thetaWeight k) (nuSMul ν l (etaMul^[j] u))) 2 (measureH c) :=
  memLp_causalAdjointRep hc ν (hγs.trans_le hμγ) (continuous_thetaWeight k) (norm_thetaWeight_le k)
    (contDiff_nuSMul ν l (contDiff_etaMul_iter j hu.smooth)).continuous.stronglyMeasurable
    (periodic_nuSMul ν l (periodic_etaMul_iter j hu.periodic))
    (memLp_nuSMul_etaMul hν hσ hσH1 hh hu hj l)

/-- Combined `L²(measureH c)` norm bound for
`causalAdjointRep ν μ (thetaWeight k) (nuSMul ν l (etaMul^[j] u))`. -/
theorem norm_causal_baseDeriv_le {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h u : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) {a m : ℕ}
    (hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m u)
    {j : ℕ} (hj : j ∈ Finset.range 3) (k l : ℕ) :
    ‖(memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hu hj k l).toLp
      (causalAdjointRep ν μ (thetaWeight k) (nuSMul ν l (etaMul^[j] u)))‖ ≤
      γs⁻¹ * (ν * H1) ^ l * flatProjMomentNorm c h := by
  have h1 := norm_causalAdjointRep_le hc ν hγs hμγ (continuous_thetaWeight k)
    (norm_thetaWeight_le k)
    (contDiff_nuSMul ν l (contDiff_etaMul_iter j hu.smooth)).continuous.stronglyMeasurable
    (periodic_nuSMul ν l (periodic_etaMul_iter j hu.periodic))
    (memLp_nuSMul_etaMul hν hσ hσH1 hh hu hj l)
  have h2 := norm_toLp_nuSMul_etaMul_le hν hσ hσH1 hh hu hj l
  calc ‖(memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hu hj k l).toLp
        (causalAdjointRep ν μ (thetaWeight k) (nuSMul ν l (etaMul^[j] u)))‖
      ≤ γs⁻¹ * ‖(memLp_nuSMul_etaMul hν hσ hσH1 hh hu hj l).toLp (nuSMul ν l (etaMul^[j] u))‖ := h1
    _ ≤ γs⁻¹ * ((ν * H1) ^ l * flatProjMomentNorm c h) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hγs.le)
    _ = γs⁻¹ * (ν * H1) ^ l * flatProjMomentNorm c h := (mul_assoc _ _ _).symm

end FlatAdjointElemAux

end UnforcedLeray.Short.PartIIa
