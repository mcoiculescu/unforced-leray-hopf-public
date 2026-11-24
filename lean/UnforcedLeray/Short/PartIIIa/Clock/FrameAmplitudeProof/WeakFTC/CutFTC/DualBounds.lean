import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.TerminalMem
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelAdjoint
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi.Field
import UnforcedLeray.Short.PartIIIa.T21_2_WeakSmoothing

/-!
# Part III-a, task `PartIII-a:T21/c5/1/1` helper: periodicity, smoothness, `X_{-m,c}` bounds, and `kerAdj` transposition

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2918 and
2998-3000 (`eq:short-causal-moving-eq`, `eq:short-causal-ampl-moving`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutFTCDual

open ComplCouplingSub ComplCouplingHeat WeakFTCSub

/-! ## 1. Unconditional BUC train bounds from Part I -/

/-- Unconditional proof of `TrainWeightedJetPoly` from Part I overlap and tail theorems. -/
theorem trainWeightedJetPoly_all : TrainWeightedJetPoly := by
  have hHN : PartI.OverlapHighNormUniform := PartI.overlap_highnorm_uniform
  have hFD0 : PartI.OverlapFluctuationDecay := PartI.overlap_fluctuation_decay hHN
  have hMP : PartI.OverlapMeanPrimitive := PartI.overlap_mean_primitive
  have hMD : PartI.OverlapMeanDecay := PartI.overlap_mean_decay hHN hFD0 hMP
  have hOv : PartI.TrainOverlap := PartI.trainOverlap_proof hFD0 hMD
  have hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  have hfl : PartI.TrainFluctuationDecay := PartI.trainFluctuationDecay_proof hTails hFD0 hOv
  have hme : PartI.TrainMeanExpansion := PartI.trainMeanExpansion_proof hTails hfl hMP
  have hmeq : PartI.TrainMeanEquations := PartI.trainMeanEquations_proof
  exact trainWeightedJetPoly_of (fluctJetWeighted_of hfl)
    (meanJetWeighted_of (meanVecFormula_of hmeq) (meanStreamJetBound_of hme hmeq)) vcWeightedJet

/-- Unconditional time-local `LadTrainBdd` bounds for BUC trains (`LadTrainBddAll m`). -/
theorem ladTrainBddAll_unconditional (m : ℝ) : LadTrainBddAll m :=
  ladTrainBddAll m trainWeightedJetPoly_all

/-! ## 2. Periodicity of `perSum`, `physFrameLam`, and `normPhysFrameLam` -/

/-- Any periodization `perSum d f` is `d`-periodic in the first coordinate. -/
theorem perSum_periodic (d : ℝ) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    perSum d f (x.1 + d, x.2) = perSum d f x := by
  unfold perSum
  conv_rhs => rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  refine tsum_congr fun n => ?_
  congr 1
  ext
  · simp
    ring
  · rfl

/-- `physFrameLam0 κ ν r j` is `ν ^ (-2 : ℝ)`-periodic in `x.1`. -/
theorem physFrameLam0_periodic (κ : PlanarFrameKernels) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (j : Fin 2) (x : ℝ × ℝ) :
    physFrameLam0 κ ν r j (x.1 + ν ^ (-2 : ℝ), x.2) = physFrameLam0 κ ν r j x := by
  rw [physFrameLam0_eq_perSum_physAdj κ hν hr j (x.1 + ν ^ (-2 : ℝ), x.2),
    physFrameLam0_eq_perSum_physAdj κ hν hr j x]
  exact perSum_periodic (ν ^ (-2 : ℝ)) (physAdj (clockA ν r) (κ.lamP j)) x

/-- `physFrameLam κ ν r i` is `ν ^ (-2 : ℝ)`-periodic in `x.1`. -/
theorem physFrameLam_periodic (κ : PlanarFrameKernels) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (i : Fin 2) (x : ℝ × ℝ) :
    physFrameLam κ ν r i (x.1 + ν ^ (-2 : ℝ), x.2) = physFrameLam κ ν r i x := by
  rw [physFrameLam_eq_sum_perGram_inv κ ν r i (x.1 + ν ^ (-2 : ℝ), x.2),
    physFrameLam_eq_sum_perGram_inv κ ν r i x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [physFrameLam0_periodic κ hν hr j x]

/-- `normPhysFrameLam κ P ν t r i` is `ν ^ (-2 : ℝ)`-periodic in `x.1`. -/
theorem normPhysFrameLam_periodic (κ : PlanarFrameKernels) (P : PlanarData) {ν t r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (i : Fin 2) (x : ℝ × ℝ) :
    normPhysFrameLam κ P ν t r i (x.1 + ν ^ (-2 : ℝ), x.2) =
      normPhysFrameLam κ P ν t r i x := by
  unfold normPhysFrameLam
  rw [physFrameLam_periodic κ hν hr i x]

/-! ## 3. Smoothness of `(clockNC P ν t · i)⁻¹` and operator scaling on `normPhysFrameLam` -/

theorem contDiffOn_clockTheta {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (clockTheta ν) (Ici 0) := by
  have hA : ContDiff ℝ ∞ (fun r : ℝ => ν * clockA ν r) := by
    unfold clockA
    exact contDiff_const.mul (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hne : ∀ r ∈ Ici (0 : ℝ), ν * clockA ν r ≠ 0 := by
    intro r hr
    have ha : 1 ≤ clockA ν r := one_le_clockA hν.le hr
    exact (mul_pos hν (lt_of_lt_of_le zero_lt_one ha)).ne'
  unfold clockTheta
  exact hA.contDiffOn.inv hne

theorem contDiffOn_clockNC_inv (P : PlanarData) {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t)
    (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun r => (clockNC P ν t r i)⁻¹) (Ici 0) := by
  have hθt : 0 < clockTheta ν t := theta_pos hν ht
  have hθ : ContDiffOn ℝ ∞ (clockTheta ν) (Ici 0) := contDiffOn_clockTheta hν
  have hθ_ne : ∀ r ∈ Ici (0 : ℝ), clockTheta ν r ≠ 0 :=
    fun r hr => (theta_pos hν hr).ne'
  have hq : ContDiffOn ℝ ∞ (fun r => clockTheta ν t / clockTheta ν r) (Ici 0) :=
    contDiffOn_const.div hθ hθ_ne
  have hq_pos : ∀ r ∈ Ici (0 : ℝ), 0 < clockTheta ν t / clockTheta ν r :=
    fun r hr => div_pos hθt (theta_pos hν hr)
  have hq_ne : ∀ r ∈ Ici (0 : ℝ), clockTheta ν t / clockTheta ν r ≠ 0 :=
    fun r hr => (hq_pos r hr).ne'
  have hlog : ContDiffOn ℝ ∞ (fun r => Real.log (clockTheta ν t / clockTheta ν r)) (Ici 0) :=
    hq.log hq_ne
  have hrpow : ContDiffOn ℝ ∞
      (fun r => (clockTheta ν t / clockTheta ν r) ^ P.kappa.re) (Ici 0) := by
    have h1 : ContDiffOn ℝ ∞
        (fun r => Real.exp (Real.log (clockTheta ν t / clockTheta ν r) * P.kappa.re)) (Ici 0) :=
      Real.contDiff_exp.comp_contDiffOn (hlog.mul contDiffOn_const)
    refine h1.congr fun r hr => ?_
    exact Real.rpow_def_of_pos (hq_pos r hr) P.kappa.re
  have hexp : ContDiffOn ℝ ∞
      (fun r => Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν r))) (Ici 0) :=
    Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul (contDiffOn_const.sub hθ))
  have hN : ContDiffOn ℝ ∞ (clockN P ν t) (Ici 0) := hexp.mul hrpow
  have hPh : ContDiffOn ℝ ∞ (fun r => clockPhaseIm P ν t r i) (Ici 0) := by
    unfold clockPhaseIm
    exact contDiffOn_const.mul
      ((contDiffOn_const.mul (contDiffOn_const.sub hθ)).add (contDiffOn_const.mul hlog))
  have hNC : ContDiffOn ℝ ∞ (fun r => clockNC P ν t r i) (Ici 0) := by
    unfold clockNC
    have hN_cx : ContDiffOn ℝ ∞ (fun r => (clockN P ν t r : ℂ)) (Ici 0) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hN
    have hPh_cx : ContDiffOn ℝ ∞
        (fun r => ((clockPhaseIm P ν t r i : ℂ) * Complex.I)) (Ici 0) :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn hPh).mul contDiffOn_const
    exact hN_cx.mul (Complex.contDiff_exp.comp_contDiffOn hPh_cx)
  exact hNC.inv (fun r hr => FrameAmplSub.clockNC_ne_zero P hν ht hr i)

/-- Joint `C^∞` smoothness of `normPhysFrameLam κ P ν t · i` on `Ico t s' ×ˢ univ` from joint
smoothness of `physFrameLam κ ν · i`. -/
theorem contDiffOn_normPhysFrameLam (κ : PlanarFrameKernels) (P : PlanarData)
    {ν t s' : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (i : Fin 2)
    (hSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2)
      (Ico t s' ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => normPhysFrameLam κ P ν t p.1 i p.2)
      (Ico t s' ×ˢ univ) := by
  have hNC : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (clockNC P ν t p.1 i)⁻¹)
      (Ico t s' ×ˢ univ) :=
    (contDiffOn_clockNC_inv P hν ht i).comp contDiff_fst.contDiffOn
      (fun p hp => ht.trans hp.1.1)
  exact hNC.mul hSmooth

/-- Spatial partial derivative `pdCx k` pulls out a complex constant multiplier `c`. -/
theorem pdCx_const_mul (c : ℂ) (f : ℝ × ℝ → ℂ) (k : Fin 2) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f x) :
    pdCx k (fun y => c * f y) x = c * pdCx k f x := by
  have h1 := RateSplitAux.pdCx_mul k (differentiableAt_const c) hf
  have h0 : pdCx k (fun _ : ℝ × ℝ => c) x = 0 := by
    change fderiv ℝ (Function.const (ℝ × ℝ) c) x (B0579.dir k) = 0
    rw [fderiv_const]
    simp
  rw [h1, h0, zero_mul, zero_add]

/-- Spatial partial derivative `pdCx k` of `normPhysFrameLam`. -/
theorem pdCx_normPhysFrameLam (κ : PlanarFrameKernels) (P : PlanarData)
    (ν t r : ℝ) (i k : Fin 2) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (physFrameLam κ ν r i) x) :
    pdCx k (normPhysFrameLam κ P ν t r i) x =
      (clockNC P ν t r i)⁻¹ * pdCx k (physFrameLam κ ν r i) x :=
  pdCx_const_mul (clockNC P ν t r i)⁻¹ (physFrameLam κ ν r i) k x hf

/-- Complex Laplacian `ladLapCx` of `normPhysFrameLam`. -/
theorem ladLapCx_normPhysFrameLam (κ : PlanarFrameKernels) (P : PlanarData)
    (ν t r : ℝ) (i : Fin 2) (x : ℝ × ℝ)
    (hf : ContDiff ℝ ∞ (physFrameLam κ ν r i)) :
    ladLapCx (normPhysFrameLam κ P ν t r i) x =
      (clockNC P ν t r i)⁻¹ * ladLapCx (physFrameLam κ ν r i) x := by
  have hd0 : ∀ y, DifferentiableAt ℝ (physFrameLam κ ν r i) y :=
    fun y => (hf.differentiable (by simp)) y
  have h0 : pdCx 0 (normPhysFrameLam κ P ν t r i) =
      fun y => (clockNC P ν t r i)⁻¹ * pdCx 0 (physFrameLam κ ν r i) y :=
    funext fun y => pdCx_normPhysFrameLam κ P ν t r i 0 y (hd0 y)
  have h1 : pdCx 1 (normPhysFrameLam κ P ν t r i) =
      fun y => (clockNC P ν t r i)⁻¹ * pdCx 1 (physFrameLam κ ν r i) y :=
    funext fun y => pdCx_normPhysFrameLam κ P ν t r i 1 y (hd0 y)
  have hd0' : DifferentiableAt ℝ (pdCx 0 (physFrameLam κ ν r i)) x :=
    ((RateSplitAux.contDiff_pdCx hf 0).differentiable (by simp)) x
  have hd1' : DifferentiableAt ℝ (pdCx 1 (physFrameLam κ ν r i)) x :=
    ((RateSplitAux.contDiff_pdCx hf 1).differentiable (by simp)) x
  unfold ladLapCx
  rw [h0, h1, pdCx_const_mul _ _ 0 x hd0', pdCx_const_mul _ _ 1 x hd1', ← mul_add]

/-- Drift `ladTransport` of `normPhysFrameLam`. -/
theorem ladTransport_normPhysFrameLam (κ : PlanarFrameKernels) (P : PlanarData)
    {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (t r : ℝ) (i : Fin 2) (x : ℝ × ℝ)
    (hf : ContDiff ℝ ∞ (physFrameLam κ ν r i)) :
    ladTransport tr r (normPhysFrameLam κ P ν t r i) x =
      (clockNC P ν t r i)⁻¹ * ladTransport tr r (physFrameLam κ ν r i) x := by
  have hd : DifferentiableAt ℝ (physFrameLam κ ν r i) x := (hf.differentiable (by simp)) x
  unfold ladTransport
  rw [pdCx_normPhysFrameLam κ P ν t r i 0 x hd, pdCx_normPhysFrameLam κ P ν t r i 1 x hd]
  ring

/-- Pointwise decomposition of `ladChi` on `normPhysFrameLam`:
`ladChi tr (normPhysFrameLam κ P ν t · i) ρ x = normPhysLamDual κ P tr t ρ i x + kerAdj c (...) x`. -/
theorem ladChi_normPhysFrameLam_eq (κ : PlanarFrameKernels) (P : PlanarData)
    {ν t s' ρ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hρ : ρ ∈ Ioo t s') (i : Fin 2)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2)
      (Ico t s' ×ˢ univ)) (x : ℝ × ℝ) :
    ladChi tr (fun r' x' => normPhysFrameLam κ P ν t r' i x') ρ x =
      normPhysLamDual κ P tr t ρ i x +
        kerAdj (ν ^ (-2 : ℝ)) (fun k y => normPhysFrameLam κ P ν t ρ i y *
          (B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℂ)) x := by
  have hρ0 : 0 ≤ ρ := ht.trans hρ.1.le
  have hρ_Ico : ρ ∈ Ico t s' := ⟨hρ.1.le, hρ.2⟩
  have hslice : ContDiff ℝ ∞ (physFrameLam κ ν ρ i) :=
    RateSplitAux.contDiff_slice (φ := fun r' x' => physFrameLam κ ν r' i x') hρ_Ico hSmooth
  have hd_time : DifferentiableAt ℝ (fun r' => physFrameLam κ ν r' i x) ρ := by
    have hU : IsOpen (Ioo t s' ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
    have hsub : Ioo t s' ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ico t s' ×ˢ univ :=
      prod_mono Ioo_subset_Ico_self (subset_refl _)
    have hd : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2) (ρ, x) :=
      ((hSmooth.mono hsub).differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds ⟨hρ, mem_univ _⟩)
    have hl : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : ℝ × ℝ)) ρ :=
      (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
    exact (hd.hasFDerivAt.comp_hasDerivAt ρ hl).differentiableAt
  unfold ladChi normPhysLamDual physLamDual
  rw [WeakFTCSub.ladDt_normPhysFrameLam κ P hν ht hρ0 i x hd_time,
    ladLapCx_normPhysFrameLam κ P ν t ρ i x hslice,
    ladTransport_normPhysFrameLam κ P tr t ρ i x hslice,
    WeakFTCSub.kerAdj_normPhysFrameLam κ P tr t ρ i x]
  ring

/-! ## 4. Quantitative pullback bound for `physAdj` in `X_{-m,c}` -/

/-- For `a ≥ 1` and `m ≥ 0`, `a ≤ a ^ (3 / 2 : ℝ) * FlowMeas.wFactor a (-m) x`. -/
lemma le_rpow_three_halves_mul_wFactor {a m : ℝ} (ha : 1 ≤ a) (hm : 0 ≤ m) (x : ℝ × ℝ) :
    a ≤ a ^ (3 / 2 : ℝ) * FlowMeas.wFactor a (-m) x := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hjb_le : B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) ≤ B0579.jb x := by
    unfold B0579.jb
    rw [div_pow, div_pow, Real.sq_sqrt ha0.le]
    have hsq1 : x.1 ^ 2 / a ≤ x.1 ^ 2 := div_le_self (sq_nonneg x.1) ha
    have hsq2 : x.2 ^ 2 / a ≤ x.2 ^ 2 := div_le_self (sq_nonneg x.2) ha
    linarith
  have hdiv_pos : 0 < B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x :=
    div_pos (B0579.jb_pos _) (B0579.jb_pos _)
  have hdiv_le : B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x ≤ 1 :=
    (div_le_one (B0579.jb_pos x)).2 hjb_le
  have hrpow_ge : 1 ≤
      (B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x) ^ ((-m) / 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdiv_pos hdiv_le (by linarith)
  have ha_prod : a ^ (3 / 2 : ℝ) * a ^ (-(1 / 2 : ℝ)) = a := by
    rw [← Real.rpow_add ha0]
    have : (3 / 2 : ℝ) + -(1 / 2 : ℝ) = 1 := by ring
    rw [this, Real.rpow_one]
  unfold FlowMeas.wFactor
  calc a = a ^ (3 / 2 : ℝ) * a ^ (-(1 / 2 : ℝ)) * 1 := by rw [ha_prod, mul_one]
    _ ≤ a ^ (3 / 2 : ℝ) * a ^ (-(1 / 2 : ℝ)) *
          (B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x) ^ ((-m) / 2) :=
        mul_le_mul_of_nonneg_left hrpow_ge (by positivity)
    _ = a ^ (3 / 2 : ℝ) *
          (a ^ (-(1 / 2 : ℝ)) *
            (B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x) ^ ((-m) / 2)) := by
        ring

/-- Quantitative `X_{-m,c}` bound for `physAdj a G` (`a ≥ 1`, `c > 0`, `m ≥ 0`):
`MemLp (physAdj a G) 2 (B0579.cellMeasure c (-m))` and
`xNorm c (-m) (physAdj a G) ≤ ENNReal.ofReal (a ^ (3 / 2 : ℝ) * K)`. -/
theorem memLp_and_xNorm_physAdj_neg {c m a K : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (ha : 1 ≤ a)
    (_hK : 0 ≤ K) {G : ℝ × ℝ → ℂ}
    (hG : MemLp G 2 (B0579.cellMeasure (cellLen c a) (-m)))
    (hb : xNorm (cellLen c a) (-m) G ≤ ENNReal.ofReal K) :
    MemLp (physAdj a G) 2 (B0579.cellMeasure c (-m)) ∧
    xNorm c (-m) (physAdj a G) ≤ ENNReal.ofReal (a ^ (3 / 2 : ℝ) * K) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hmem : MemLp (physAdj a G) 2 (B0579.cellMeasure c (-m)) :=
    adjTerminalMem m hm c a hc ha G hG
  refine ⟨hmem, ?_⟩
  have hpt : ∀ x : ℝ × ℝ,
      ‖physAdj a G x‖ ≤
        ‖((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * FlowMeas.pullCell a (-m) G x‖ := by
    intro x
    have hw_nn : 0 ≤ FlowMeas.wFactor a (-m) x := FlowMeas.wFactor_nonneg ha0 x
    have hle := le_rpow_three_halves_mul_wFactor ha hm x
    unfold physAdj FlowMeas.pullCell
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0.le,
      Real.norm_of_nonneg (Real.rpow_nonneg ha0.le _), Real.norm_of_nonneg hw_nn, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  have hmono : xNorm c (-m) (physAdj a G) ≤
      xNorm c (-m) (fun x => ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * FlowMeas.pullCell a (-m) G x) :=
    eLpNorm_mono hpt
  have hsmul : xNorm c (-m)
      (fun x => ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * FlowMeas.pullCell a (-m) G x) =
      ENNReal.ofReal (a ^ (3 / 2 : ℝ)) * xNorm c (-m) (FlowMeas.pullCell a (-m) G) := by
    unfold xNorm
    have heq : (fun x => ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * FlowMeas.pullCell a (-m) G x) =
        ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) • FlowMeas.pullCell a (-m) G := rfl
    rw [heq, eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ha0.le _)]
  rw [hsmul, FlowMeas.xNorm_pullCell c (-m) a ha0 G] at hmono
  calc xNorm c (-m) (physAdj a G)
      ≤ ENNReal.ofReal (a ^ (3 / 2 : ℝ)) * xNorm (cellLen c a) (-m) G := hmono
    _ ≤ ENNReal.ofReal (a ^ (3 / 2 : ℝ)) * ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal (a ^ (3 / 2 : ℝ) * K) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg ha0.le _)).symm

/-! ## 5. Kernel adjoint `X_{-m,c}` bound and transposition against `IsLinearisedFlow` -/

/-- For `1 ≤ c`, `8 < m`, `0 ≤ ρ ≤ S`, `LadTrainBdd tr m S C`, and any `Φ ∈ X_{-m,c}`, the kernel
adjoint `kerAdj c (fun k y => Φ y * (pd k (Ec tr ρ) y : ℂ))` lies in `X_{-m,c}` and transposes
against any zero-circulation Biot-Savart pair `(w, u)` in `X_{m,c} × L²`:
`∫ x in B0579.cell c, w x * kerAdj c (...) x = ∫ x in B0579.cell c, ladForce tr u ρ x * Φ x`. -/
theorem kerAdj_memLp_and_transposition {ν c m S C K_Φ : ℝ} (hm : 8 < m) (hc : 1 ≤ c)
    (hC0 : 0 ≤ C) (hK_Φ : 0 ≤ K_Φ)
    {tr : UnforcedLeray.B0140.TrainSol ν c} (hBdd : LadTrainBdd tr m S C) :
    ∃ M_ker : ℝ, 0 ≤ M_ker ∧
      ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) S →
      ∀ {Φ : ℝ × ℝ → ℂ},
        MemLp Φ 2 (B0579.cellMeasure c (-m)) →
        xNorm c (-m) Φ ≤ ENNReal.ofReal K_Φ →
        let F : Fin 2 → ℝ × ℝ → ℂ :=
          fun k y => Φ y * ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)
        (MemLp (kerAdj c F) 2 (B0579.cellMeasure c (-m)) ∧
          xNorm c (-m) (kerAdj c F) ≤ ENNReal.ofReal M_ker) ∧
        (∀ (w : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Fin 2 → ℂ),
          MemLp w 2 (B0579.cellMeasure c m) →
          HasZeroCirculation c w →
          IsBiotSavart c w u →
          ∫ x in B0579.cell c, w x * kerAdj c F x =
            ∫ x in B0579.cell c, ladForce tr u ρ x * Φ x) := by
  have hm1 : 1 < m := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  set K_f : ℝ :=
    2 * (C + (eLpNorm (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2 volume).toReal + 1)
  have hK_f0 : 0 ≤ K_f := by
    have : 0 ≤ (eLpNorm (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2 volume).toReal :=
      ENNReal.toReal_nonneg
    positivity
  obtain ⟨CS, hCS0, hCS⟩ := kerAdjSplit_of kerNearFar
  obtain ⟨CW, hCW0, hCW⟩ := xNormSplitLe m hm1
  set M_ker : ℝ := (CS + CW * CS) * (2 * (K_f * K_Φ))
  have hM_ker0 : 0 ≤ M_ker := by positivity
  refine ⟨M_ker, hM_ker0, fun {ρ} hρS {Φ} hΦ hΦ_norm => ?_⟩
  intro F
  have hΦm : AEStronglyMeasurable Φ (volume.restrict (B0579.cell c)) :=
    hΦ.1.mono_ac (B0579.ac_cellMeasure c (-m))
  have hΦfin : xNorm c (-m) Φ < ⊤ := hΦ.2
  have hE : ∀ (j : Fin 2) (y : ℝ × ℝ), y ∈ B0579.cell c →
      B0579.jb y ^ ((m + 2) / 2) * |B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) y| ≤ C :=
    fun j y hy => (hBdd ρ hρS y hy).2 j
  have hF_bd : ∀ j : Fin 2,
      IntegrableOn (F j) (B0579.cell c) ∧
      MemLp (F j) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (F j) 1 (volume.restrict (B0579.cell c)) +
        eLpNorm (F j) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal (K_f * K_Φ) := by
    intro j
    obtain ⟨hi, hm2, hle⟩ := weightedFieldBound m C hC0 c j Φ
      (UnforcedLeray.B0238.Ec tr ρ) hΦm hΦfin (hE j)
    refine ⟨hi, hm2, ?_⟩
    calc eLpNorm (F j) 1 (volume.restrict (B0579.cell c)) +
          eLpNorm (F j) 2 (volume.restrict (B0579.cell c))
        ≤ ENNReal.ofReal K_f * xNorm c (-m) Φ := hle
      _ ≤ ENNReal.ofReal K_f * ENNReal.ofReal K_Φ := by gcongr
      _ = ENNReal.ofReal (K_f * K_Φ) := (ENNReal.ofReal_mul hK_f0).symm
  obtain ⟨a, b, hab, ha, haB, hb, hbB⟩ := hCS c hc F (fun j => ⟨(hF_bd j).1, (hF_bd j).2.1⟩)
  set μ := volume.restrict (B0579.cell c)
  have hL1_le : ∑ j : Fin 2, eLpNorm (F j) 1 μ ≤ ENNReal.ofReal (2 * (K_f * K_Φ)) := by
    rw [Fin.sum_univ_two, show (2 : ℝ) * (K_f * K_Φ) = K_f * K_Φ + K_f * K_Φ by ring,
      ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add (le_self_add.trans (hF_bd 0).2.2) (le_self_add.trans (hF_bd 1).2.2)
  have hL2_le : ∑ j : Fin 2, eLpNorm (F j) 2 μ ≤ ENNReal.ofReal (2 * (K_f * K_Φ)) := by
    rw [Fin.sum_univ_two, show (2 : ℝ) * (K_f * K_Φ) = K_f * K_Φ + K_f * K_Φ by ring,
      ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add (le_add_self.trans (hF_bd 0).2.2) (le_add_self.trans (hF_bd 1).2.2)
  have hx_ker : xNorm c (-m) (kerAdj c F) ≤ ENNReal.ofReal M_ker := by
    have h1 := (hCW c hc0 (kerAdj c F) a b _ hab ha.1 hb hbB).trans (add_le_add haB le_rfl)
    refine h1.trans ?_
    calc ENNReal.ofReal CS * ∑ j, eLpNorm (F j) 2 μ +
          ENNReal.ofReal CW * (ENNReal.ofReal CS * ∑ j, eLpNorm (F j) 1 μ)
        ≤ ENNReal.ofReal CS * ENNReal.ofReal (2 * (K_f * K_Φ)) +
            ENNReal.ofReal CW * (ENNReal.ofReal CS * ENNReal.ofReal (2 * (K_f * K_Φ))) := by
          gcongr
      _ = ENNReal.ofReal M_ker := by
          unfold M_ker
          rw [← ENNReal.ofReal_mul hCS0, ← ENNReal.ofReal_mul hCW0,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  have haesm_ker : AEStronglyMeasurable (kerAdj c F) (B0579.cellMeasure c (-m)) :=
    ((ha.1.add hb).congr hab.symm).mono_ac (B0579.cellMeasure_ac c (-m))
  have hmem_ker : MemLp (kerAdj c F) 2 (B0579.cellMeasure c (-m)) :=
    ⟨haesm_ker, lt_of_le_of_lt hx_ker ENNReal.ofReal_lt_top⟩
  refine ⟨⟨hmem_ker, hx_ker⟩, ?_⟩
  -- Transposition against any zero-circulation Biot-Savart pair `(w, u)`
  intro w u hw hz hbs
  have hNF : KerNearFar := kerNearFar
  have hFub : KerAdjFubini := kerAdjFubini_of hNF
  have hFar : KerVelFarField := kerVelFarField_of hNF
  have hD : KerVelDivFree := kerVelDivFree_of hFub (kerDivPointwise_of hNF)
  have hC : KerVelCurl := kerVelCurl_of hFub (kerCurlPointwise_of hNF)
  have htest_dual : ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
      B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
      ∫ y in B0579.cell c, kerAdj c F y * ((ψ y : ℝ) : ℂ) =
        ∫ y in B0579.cell c, Φ y *
          ((uψ y 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) y +
            uψ y 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ) := by
    intro ψ uψ hψ huψ
    obtain ⟨-, heq⟩ := hFub c hc F (fun j => (hF_bd j).1) ψ hψ
    rw [heq]
    have hE_vel : IsKernelBiotSavart c ψ (kerVel c ψ) :=
      ⟨hFar c hc ψ hψ, hD c hc ψ hψ, hC c hc ψ hψ⟩
    have hae := kernelBiotSavartUnique c hc0 ψ uψ (kerVel c ψ) huψ hE_vel
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp only [F, Fin.sum_univ_two, hy]
    push_cast
    ring
  -- Approximate `(w, u)` by cylinder tests via `ladTranspApprox`
  obtain ⟨a_n, b_n, ua_n, ub_n, hT, hXn, hVn⟩ := ladTranspApprox m hm c w u hc hw hz hbs
  have hAm : ∀ n, MemLp (fun x => ((a_n n x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
    fun n => ((hT n).1.memLp m).ofReal
  have hBm : ∀ n, MemLp (fun x => ((b_n n x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
    fun n => ((hT n).2.1.memLp m).ofReal
  have hAB : ∀ n, MemLp (fun x => ((a_n n x : ℝ) : ℂ) + Complex.I * ((b_n n x : ℝ) : ℂ)) 2
      (B0579.cellMeasure c m) := fun n => (hAm n).add ((hBm n).const_mul Complex.I)
  have hL := TranspLimitAux.pairing_tendsto
    (A := fun n x => ((a_n n x : ℝ) : ℂ) + Complex.I * ((b_n n x : ℝ) : ℂ))
    hAB hw hmem_ker hXn
  have hmeas : ∀ n (j : Fin 2),
      AEStronglyMeasurable (fun x => ua_n n x j) (volume.restrict (B0579.cell c)) ∧
      AEStronglyMeasurable (fun x => ub_n n x j) (volume.restrict (B0579.cell c)) :=
    fun n j => ⟨aesm_of_kernel (hT n).2.2.1 j, aesm_of_kernel (hT n).2.2.2 j⟩
  have hev : ∀ᶠ n in atTop, ∀ j : Fin 2, eLpNorm
      (fun x => ((ua_n n x j : ℝ) : ℂ) + Complex.I * ((ub_n n x j : ℝ) : ℂ) - u x j) 2
        (volume.restrict (B0579.cell c)) < 1 := by
    rw [Filter.eventually_all]
    intro j
    exact (hVn j).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hL2 : ∀ n, N ≤ n → ∀ j : Fin 2,
      MemLp (fun x => ua_n n x j) 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun x => ub_n n x j) 2 (volume.restrict (B0579.cell c)) :=
    fun n hn j => TranspLimitAux.memLp_of_dist (hbs.1 j) (hmeas n j).1 (hmeas n j).2
      ((hN n hn j).trans ENNReal.one_lt_top)
  set Fa : ℕ → ℝ × ℝ → ℂ := fun n => ladForce tr (fun x j => ((ua_n n x j : ℝ) : ℂ)) ρ
  set Fb : ℕ → ℝ × ℝ → ℂ := fun n => ladForce tr (fun x j => ((ub_n n x j : ℝ) : ℂ)) ρ
  have hFam : ∀ n, N ≤ n → MemLp (Fa n) 2 (B0579.cellMeasure c m) := fun n hn =>
    (ladForceMemX m ν c tr S C ρ hBdd hρS _ (fun j => (hL2 n hn j).1.ofReal)).1
  have hFbm : ∀ n, N ≤ n → MemLp (Fb n) 2 (B0579.cellMeasure c m) := fun n hn =>
    (ladForceMemX m ν c tr S C ρ hBdd hρS _ (fun j => (hL2 n hn j).2.ofReal)).1
  have hFm : MemLp (ladForce tr u ρ) 2 (B0579.cellMeasure c m) :=
    (ladForceMemX m ν c tr S C ρ hBdd hρS u hbs.1).1
  have hR0 : Tendsto (fun n => eLpNorm (fun x => (Fa (n + N) x + Complex.I * Fb (n + N) x) -
      ladForce tr u ρ x) 2 (B0579.cellMeasure c m)) atTop (𝓝 0) := by
    have hbd : ∀ n, eLpNorm (fun x => (Fa (n + N) x + Complex.I * Fb (n + N) x) -
        ladForce tr u ρ x) 2 (B0579.cellMeasure c m) ≤
        ENNReal.ofReal C * (eLpNorm (fun x => ((ua_n (n + N) x 0 : ℝ) : ℂ) +
          Complex.I * ((ub_n (n + N) x 0 : ℝ) : ℂ) - u x 0) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => ((ua_n (n + N) x 1 : ℝ) : ℂ) +
          Complex.I * ((ub_n (n + N) x 1 : ℝ) : ℂ) - u x 1) 2 (volume.restrict (B0579.cell c))) := by
      intro n
      have hn : N ≤ n + N := Nat.le_add_left N n
      have hDm : ∀ j : Fin 2, MemLp (fun x => ((ua_n (n + N) x j : ℝ) : ℂ) +
          Complex.I * ((ub_n (n + N) x j : ℝ) : ℂ) - u x j) 2 (volume.restrict (B0579.cell c)) :=
        fun j => TranspLimitAux.memLp_D (hL2 _ hn j).1 (hL2 _ hn j).2 (hbs.1 j)
      have := (ladForceMemX m ν c tr S C ρ hBdd hρS _ hDm).2
      refine le_of_eq_of_le ?_ this
      congr 1
      funext x
      simp only [Fa, Fb]
      unfold ladForce
      ring
    have hlim : Tendsto (fun n => ENNReal.ofReal C * (eLpNorm (fun x => ((ua_n (n + N) x 0 : ℝ) : ℂ) +
          Complex.I * ((ub_n (n + N) x 0 : ℝ) : ℂ) - u x 0) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => ((ua_n (n + N) x 1 : ℝ) : ℂ) +
          Complex.I * ((ub_n (n + N) x 1 : ℝ) : ℂ) - u x 1) 2 (volume.restrict (B0579.cell c))))
        atTop (𝓝 0) := by
      have h0 := (hVn 0).comp (tendsto_add_atTop_nat N)
      have h1 := (hVn 1).comp (tendsto_add_atTop_nat N)
      have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) (h0.add h1)
        (Or.inr ENNReal.ofReal_ne_top)
      rw [add_zero, mul_zero] at this
      exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbd
  have hR := TranspLimitAux.pairing_tendsto (A := fun n x => Fa (n + N) x + Complex.I * Fb (n + N) x)
    (w := ladForce tr u ρ) (χ := Φ)
    (fun n => ((hFam (n + N) (Nat.le_add_left N n)).add
      ((hFbm (n + N) (Nat.le_add_left N n)).const_mul Complex.I))) hFm hΦ hR0
  have hL' := hL.comp (tendsto_add_atTop_nat N)
  have heq : ∀ n, (∫ x in B0579.cell c,
      (((a_n (n + N) x : ℝ) : ℂ) + Complex.I * ((b_n (n + N) x : ℝ) : ℂ)) * kerAdj c F x) =
      ∫ x in B0579.cell c, (Fa (n + N) x + Complex.I * Fb (n + N) x) * Φ x := by
    intro n
    have hn : N ≤ n + N := Nat.le_add_left N n
    have i1 := (PairContAux.holder (hAm (n + N)) hmem_ker).1
    have i2 := (PairContAux.holder (hBm (n + N)) hmem_ker).1
    have j1 := (PairContAux.holder (hFam _ hn) hΦ).1
    have j2 := (PairContAux.holder (hFbm _ hn) hΦ).1
    have e1 : (fun x => (((a_n (n + N) x : ℝ) : ℂ) + Complex.I * ((b_n (n + N) x : ℝ) : ℂ)) *
        kerAdj c F x) = fun x => kerAdj c F x * ((a_n (n + N) x : ℝ) : ℂ) +
          Complex.I * (kerAdj c F x * ((b_n (n + N) x : ℝ) : ℂ)) := by
      funext x; ring
    have e2 : (fun x => (Fa (n + N) x + Complex.I * Fb (n + N) x) * Φ x) =
        fun x => Φ x * Fa (n + N) x + Complex.I * (Φ x * Fb (n + N) x) := by
      funext x; ring
    have i1' : Integrable (fun x => kerAdj c F x * ((a_n (n + N) x : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) := i1.congr (ae_of_all _ fun x => mul_comm _ _)
    have i2' : Integrable (fun x => kerAdj c F x * ((b_n (n + N) x : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) := i2.congr (ae_of_all _ fun x => mul_comm _ _)
    have j1' : Integrable (fun x => Φ x * Fa (n + N) x) (volume.restrict (B0579.cell c)) :=
      j1.congr (ae_of_all _ fun x => mul_comm _ _)
    have j2' : Integrable (fun x => Φ x * Fb (n + N) x) (volume.restrict (B0579.cell c)) :=
      j2.congr (ae_of_all _ fun x => mul_comm _ _)
    rw [e1, e2, integral_add i1' (i2'.const_mul _), integral_add j1' (j2'.const_mul _),
      integral_const_mul, integral_const_mul,
      htest_dual (a_n (n + N)) (ua_n (n + N)) (hT (n + N)).1 (hT (n + N)).2.2.1,
      htest_dual (b_n (n + N)) (ub_n (n + N)) (hT (n + N)).2.1 (hT (n + N)).2.2.2]
    simp only [Fa, Fb, ← TranspLimitAux.ladForce_real]
  exact tendsto_nhds_unique (hL'.congr heq) hR

/-! ## 6. Uniform `X_{-m,c}` bounds on `[t, s]` for `physFrameLam`, `physLamDual`, `normPhysFrameLam`, and `normPhysLamDual` -/

/-- Uniform `X_{-m,c}` membership and norm bounds for `physFrameLam κ ν r i` and
`physLamDual κ tr r i` from the moving-variable heat and Euler dual bounds. -/
theorem memLp_and_xNorm_physFrameLam_and_physLamDual (κ : PlanarFrameKernels) (lam : ℂ)
    {ν m s r C_h C_e M_G K₀ : ℝ} (hm : 8 < m) (hν : 0 < ν) (hr : 0 ≤ r) (hrs : r ≤ s)
    (hθ : 1 ≤ clockTheta ν r)
    (hC_h0 : 0 ≤ C_h) (hC_e0 : 0 ≤ C_e) (hM_G0 : 0 ≤ M_G) (hK₀ : 0 ≤ K₀)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} (i : Fin 2)
    (hLam0 : ∀ j : Fin 2,
      MemLp (perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)
        (perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) ≤ ENNReal.ofReal K₀)
    (hGinv : ∀ j : Fin 2,
      ‖(perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i j‖ ≤ M_G)
    (hHeat : MemLp (movLamDualHeat κ ν r i) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) (movLamDualHeat κ ν r i) ≤
        ENNReal.ofReal (C_h * (1 / clockTheta ν r)))
    (hEuler : MemLp (movLamDualEulerSub κ lam tr r i) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) (movLamDualEulerSub κ lam tr r i) ≤
        ENNReal.ofReal (C_e * (1 / clockTheta ν r))) :
    let c := ν ^ (-2 : ℝ)
    let K_lam := (clockA ν s) ^ (3 / 2 : ℝ) * (2 * M_G * K₀)
    let K_dual := (clockA ν s) ^ (3 / 2 : ℝ) *
      (C_h + C_e + ‖seedModeEigen lam i‖ * (2 * M_G * K₀))
    (MemLp (physFrameLam κ ν r i) 2 (B0579.cellMeasure c (-m)) ∧
      xNorm c (-m) (physFrameLam κ ν r i) ≤ ENNReal.ofReal K_lam) ∧
    (MemLp (physLamDual κ tr r i) 2 (B0579.cellMeasure c (-m)) ∧
      xNorm c (-m) (physLamDual κ tr r i) ≤ ENNReal.ofReal K_dual) := by
  intro c K_lam K_dual
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν _
  have hm0 : 0 ≤ m := by linarith
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have has : clockA ν r ≤ clockA ν s := clockA_mono hν.le hrs
  have has_rpow : (clockA ν r) ^ (3 / 2 : ℝ) ≤ (clockA ν s) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow ha0.le has (by norm_num)
  set d := cellLen c (clockA ν r)
  -- 1. Bound `perLam κ d i` in `X_{-m, d}`
  have hterm_lam : ∀ j : Fin 2,
      MemLp (fun y => (perGram κ d)⁻¹ i j * perLam0 κ d j y) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (fun y => (perGram κ d)⁻¹ i j * perLam0 κ d j y) ≤
        ENNReal.ofReal (M_G * K₀) := by
    intro j
    refine ⟨(hLam0 j).1.const_mul _, ?_⟩
    refine (xNorm_const_mul_le hK₀ (hLam0 j).2).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (hGinv j) hK₀
  have hperLam_eq : perLam κ d i =
      fun y => (perGram κ d)⁻¹ i 0 * perLam0 κ d 0 y + (perGram κ d)⁻¹ i 1 * perLam0 κ d 1 y := by
    funext y; unfold perLam; exact Fin.sum_univ_two _
  obtain ⟨hperLam_mem, hperLam_x⟩ :
      MemLp (perLam κ d i) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (perLam κ d i) ≤ ENNReal.ofReal (2 * M_G * K₀) := by
    rw [hperLam_eq]
    obtain ⟨hm01, hx01⟩ := memLp_and_xNorm_add_le (by positivity) (by positivity)
      (hterm_lam 0).1 (hterm_lam 1).1 (hterm_lam 0).2 (hterm_lam 1).2
    refine ⟨hm01, hx01.trans ?_⟩
    rw [show M_G * K₀ + M_G * K₀ = 2 * M_G * K₀ by ring]
  -- Pull back `perLam κ d i` to `physFrameLam κ ν r i`
  obtain ⟨hphysLam_mem, hphysLam_x⟩ :=
    memLp_and_xNorm_physAdj_neg hc0 hm0 ha1 (by positivity) hperLam_mem hperLam_x
  have hphysLam_x' : xNorm c (-m) (physFrameLam κ ν r i) ≤ ENNReal.ofReal K_lam := by
    refine hphysLam_x.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right has_rpow (by positivity)
  -- 2. Bound `movLamDual κ tr r i` and `movingPhi ν (physLamDual κ tr · i) r` in `X_{-m, d}`
  have hinvθ_le : 1 / clockTheta ν r ≤ 1 := by
    rw [one_div]
    exact inv_le_one_of_one_le₀ hθ
  have hHeat_x : xNorm d (-m) (movLamDualHeat κ ν r i) ≤ ENNReal.ofReal C_h := by
    refine hHeat.2.trans (ENNReal.ofReal_le_ofReal ?_)
    calc C_h * (1 / clockTheta ν r) ≤ C_h * 1 := mul_le_mul_of_nonneg_left hinvθ_le hC_h0
      _ = C_h := mul_one C_h
  have hEuler_x : xNorm d (-m) (movLamDualEulerSub κ lam tr r i) ≤ ENNReal.ofReal C_e := by
    refine hEuler.2.trans (ENNReal.ofReal_le_ofReal ?_)
    calc C_e * (1 / clockTheta ν r) ≤ C_e * 1 := mul_le_mul_of_nonneg_left hinvθ_le hC_e0
      _ = C_e := mul_one C_e
  obtain ⟨hSub_mem, hSub_x⟩ := memLp_and_xNorm_add_le hC_h0 hC_e0
    hHeat.1 hEuler.1 hHeat_x hEuler_x
  have hEig_mem : MemLp (fun y => seedModeEigen lam i * perLam κ d i y) 2
      (B0579.cellMeasure d (-m)) := hperLam_mem.const_mul _
  have hEig_x : xNorm d (-m) (fun y => seedModeEigen lam i * perLam κ d i y) ≤
      ENNReal.ofReal (‖seedModeEigen lam i‖ * (2 * M_G * K₀)) :=
    xNorm_const_mul_le (by positivity) hperLam_x
  have hmovDual_eq : movLamDual κ tr r i =
      fun y => (movLamDualHeat κ ν r i y + movLamDualEulerSub κ lam tr r i y) +
        seedModeEigen lam i * perLam κ d i y := by
    funext y
    have h1 := movLamDualSub_eq_add κ lam tr r i y
    unfold movLamDualSub at h1
    exact eq_add_of_sub_eq h1
  obtain ⟨hmovDual_mem, hmovDual_x⟩ :
      MemLp (movLamDual κ tr r i) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (movLamDual κ tr r i) ≤
        ENNReal.ofReal (C_h + C_e + ‖seedModeEigen lam i‖ * (2 * M_G * K₀)) := by
    rw [hmovDual_eq]
    exact memLp_and_xNorm_add_le (by positivity) (by positivity)
      hSub_mem hEig_mem hSub_x hEig_x
  have hmovPhi_eq : movingPhi ν (fun r' => physLamDual κ tr r' i) r =
      fun y => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * movLamDual κ tr r i y := by
    funext y
    unfold movLamDual
    rw [← mul_assoc]
    have ha_inv : (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add ha0]
      norm_num
    rw [ha_inv, one_mul]
  have hmovPhi_mem : MemLp (movingPhi ν (fun r' => physLamDual κ tr r' i) r) 2
      (B0579.cellMeasure d (-m)) := by
    rw [hmovPhi_eq]
    exact hmovDual_mem.const_mul _
  have hmovPhi_x : xNorm d (-m) (movingPhi ν (fun r' => physLamDual κ tr r' i) r) ≤
      ENNReal.ofReal (C_h + C_e + ‖seedModeEigen lam i‖ * (2 * M_G * K₀)) := by
    rw [hmovPhi_eq]
    refine (xNorm_const_mul_le (by positivity) hmovDual_x).trans (ENNReal.ofReal_le_ofReal ?_)
    have ha_le1 : ‖(((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ha0.le _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos ha1 (by norm_num)
    calc ‖(((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ)‖ *
          (C_h + C_e + ‖seedModeEigen lam i‖ * (2 * M_G * K₀))
        ≤ 1 * (C_h + C_e + ‖seedModeEigen lam i‖ * (2 * M_G * K₀)) :=
          mul_le_mul_of_nonneg_right ha_le1 (by positivity)
      _ = C_h + C_e + ‖seedModeEigen lam i‖ * (2 * M_G * K₀) := one_mul _
  -- Pull back `movingPhi ν (physLamDual κ tr · i) r` to `physLamDual κ tr r i`
  have hphysDual_eq : physAdj (clockA ν r) (movingPhi ν (fun r' => physLamDual κ tr r' i) r) =
      physLamDual κ tr r i :=
    funext fun x => FrameAmplSub.physAdj_movingPhi_pointwise ν r hν hr
      (fun r' => physLamDual κ tr r' i) x
  obtain ⟨hphysDual_mem, hphysDual_x⟩ :=
    memLp_and_xNorm_physAdj_neg hc0 hm0 ha1 (by positivity) hmovPhi_mem hmovPhi_x
  rw [hphysDual_eq] at hphysDual_mem hphysDual_x
  have hphysDual_x' : xNorm c (-m) (physLamDual κ tr r i) ≤ ENNReal.ofReal K_dual := by
    refine hphysDual_x.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right has_rpow (by positivity)
  exact ⟨⟨hphysLam_mem, hphysLam_x'⟩, ⟨hphysDual_mem, hphysDual_x'⟩⟩

/-- Uniform bound on `‖(clockNC P ν t r i)⁻¹‖` and `‖modeDiag P ν r i‖` on `[t, s]`. -/
theorem exists_clockNC_inv_and_modeDiag_bound (P : PlanarData) {ν t s : ℝ}
    (hν : 0 < ν) (ht : 0 ≤ t) :
    ∃ M_NC M_diag : ℝ, 0 ≤ M_NC ∧ 0 ≤ M_diag ∧
      ∀ r ∈ Icc t s, ∀ i : Fin 2,
        ‖(clockNC P ν t r i)⁻¹‖ ≤ M_NC ∧ ‖modeDiag P ν r i‖ ≤ M_diag := by
  have hsub : Icc t s ⊆ Ici 0 := fun r hr => ht.trans hr.1
  have hNC_cont : ∀ i : Fin 2, ContinuousOn (fun r => ‖(clockNC P ν t r i)⁻¹‖) (Icc t s) :=
    fun i => ((contDiffOn_clockNC_inv P hν ht i).continuousOn.mono hsub).norm
  obtain ⟨B₀, hB₀0, hB₀⟩ := RateBoundAux.bdd_of_cont (hNC_cont 0)
  obtain ⟨B₁, hB₁0, hB₁⟩ := RateBoundAux.bdd_of_cont (hNC_cont 1)
  have hθ_cont : ContinuousOn (clockTheta ν) (Icc t s) :=
    (contDiffOn_clockTheta hν).continuousOn.mono hsub
  have hθ_ne : ∀ r ∈ Icc t s, (clockTheta ν r : ℂ) ≠ 0 :=
    fun r hr => Complex.ofReal_ne_zero.2 (theta_pos hν (ht.trans hr.1)).ne'
  have hdiag_cont : ∀ i : Fin 2, ContinuousOn (fun r => ‖modeDiag P ν r i‖) (Icc t s) := by
    intro i
    unfold modeDiag
    exact (continuousOn_const.add
      (continuousOn_const.div (Complex.continuous_ofReal.comp_continuousOn hθ_cont) hθ_ne)).norm
  obtain ⟨D₀, hD₀0, hD₀⟩ := RateBoundAux.bdd_of_cont (hdiag_cont 0)
  obtain ⟨D₁, hD₁0, hD₁⟩ := RateBoundAux.bdd_of_cont (hdiag_cont 1)
  refine ⟨max B₀ B₁, max D₀ D₁, le_trans hB₀0 (le_max_left _ _),
    le_trans hD₀0 (le_max_left _ _), fun r hr i => ?_⟩
  fin_cases i
  · exact ⟨(hB₀ r hr).trans (le_max_left _ _), (hD₀ r hr).trans (le_max_left _ _)⟩
  · exact ⟨(hB₁ r hr).trans (le_max_right _ _), (hD₁ r hr).trans (le_max_right _ _)⟩

/-- `X_{-m,c}` membership and norm bounds for `normPhysFrameLam κ P ν t r i` and
`normPhysLamDual κ P tr t r i` from bounds on `physFrameLam` and `physLamDual`. -/
theorem memLp_and_xNorm_normPhysFrameLam_and_Dual (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m t r K_lam K_dual M_NC M_diag : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (hK_lam : 0 ≤ K_lam) (hK_dual : 0 ≤ K_dual) (hM_NC : 0 ≤ M_NC) (hM_diag : 0 ≤ M_diag)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} (i : Fin 2)
    (hNC : ‖(clockNC P ν t r i)⁻¹‖ ≤ M_NC) (hdiag : ‖modeDiag P ν r i‖ ≤ M_diag)
    (hLam : MemLp (physFrameLam κ ν r i) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
      xNorm (ν ^ (-2 : ℝ)) (-m) (physFrameLam κ ν r i) ≤ ENNReal.ofReal K_lam)
    (hDual : MemLp (physLamDual κ tr r i) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
      xNorm (ν ^ (-2 : ℝ)) (-m) (physLamDual κ tr r i) ≤ ENNReal.ofReal K_dual) :
    let c := ν ^ (-2 : ℝ)
    (MemLp (normPhysFrameLam κ P ν t r i) 2 (B0579.cellMeasure c (-m)) ∧
      xNorm c (-m) (normPhysFrameLam κ P ν t r i) ≤ ENNReal.ofReal (M_NC * K_lam)) ∧
    (MemLp (normPhysLamDual κ P tr t r i) 2 (B0579.cellMeasure c (-m)) ∧
      xNorm c (-m) (normPhysLamDual κ P tr t r i) ≤
        ENNReal.ofReal (M_NC * K_dual + M_diag * (M_NC * K_lam))) := by
  intro c
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hnorm_mem : MemLp (normPhysFrameLam κ P ν t r i) 2 (B0579.cellMeasure c (-m)) :=
    hLam.1.const_mul _
  have hnorm_x : xNorm c (-m) (normPhysFrameLam κ P ν t r i) ≤ ENNReal.ofReal (M_NC * K_lam) := by
    unfold normPhysFrameLam
    refine (xNorm_const_mul_le hK_lam hLam.2).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hNC hK_lam
  have hA_mem : MemLp (fun x => (clockNC P ν t r i)⁻¹ * physLamDual κ tr r i x) 2
      (B0579.cellMeasure c (-m)) := hDual.1.const_mul _
  have hA_x : xNorm c (-m) (fun x => (clockNC P ν t r i)⁻¹ * physLamDual κ tr r i x) ≤
      ENNReal.ofReal (M_NC * K_dual) := by
    refine (xNorm_const_mul_le hK_dual hDual.2).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hNC hK_dual
  have hB_mem : MemLp (fun x => -((((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * modeDiag P ν r i) *
      normPhysFrameLam κ P ν t r i x) 2 (B0579.cellMeasure c (-m)) :=
    hnorm_mem.const_mul _
  have hB_x : xNorm c (-m) (fun x => -((((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * modeDiag P ν r i) *
      normPhysFrameLam κ P ν t r i x) ≤ ENNReal.ofReal (M_diag * (M_NC * K_lam)) := by
    refine (xNorm_const_mul_le (by positivity) hnorm_x).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ha0.le _)]
    have ha_le1 : (clockA ν r) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ha1 (by norm_num)
    calc (clockA ν r) ^ (-2 : ℝ) * ‖modeDiag P ν r i‖ * (M_NC * K_lam)
        ≤ 1 * M_diag * (M_NC * K_lam) := by gcongr
      _ = M_diag * (M_NC * K_lam) := by ring
  have hdual_eq : normPhysLamDual κ P tr t r i =
      fun x => (clockNC P ν t r i)⁻¹ * physLamDual κ tr r i x +
        (-((((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * modeDiag P ν r i) *
          normPhysFrameLam κ P ν t r i x) := by
    funext x; unfold normPhysLamDual; ring
  rw [hdual_eq]
  exact ⟨⟨hnorm_mem, hnorm_x⟩,
    memLp_and_xNorm_add_le (by positivity) (by positivity) hA_mem hB_mem hA_x hB_x⟩

end CutFTCDual

end UnforcedLeray.Short.IIIa
