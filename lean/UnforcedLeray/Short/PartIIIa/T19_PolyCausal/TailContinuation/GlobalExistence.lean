import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.LateFluctVel
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.LateMeanVel
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartIIa.Sub.R01_1
import UnforcedLeray.Short.PartIIa.Tasks.R02.ProfileSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyStreamProfile.MeanStreamSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.SliceDerivContinuous
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.AgeDerivSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.EssSupPointwise

/-!
# Part III-a, task `PartIII-a:T19/3/3`: global causal existence around the BUC train

Source of record: `the November 2 reference manuscript` (SP), lines 3517-3537
(Steps P5-P6 of `prop:short-polynomial-causal`).

Proves `trainCausalExistence : UnforcedLeray.Short.IIIa.TrainCausalExistence`:
1. Combines `lateVel_of` (`LateFluctVel`, `LateMeanVel`) at `mZ = 0` on `s ≥ 1` with
   `IsBUCTrain.sup_bound` on `0 ≤ s ≤ 1` to obtain `‖(trainVel tr s x i : ℂ)‖ ≤ K_tr / (1 + s)`
   for all `s ≥ 0`.
2. Deduces that `flatMult tr` maps `𝓗` into `𝒯` boundedly, so the Picard sequence
   `(b_{n+1}, G_{n+1}) = S_0(F - flatMult tr b_n)` is well-defined via `freeCausalExistsUnique`.
3. Tests `weightedEnergyIdentity` with `w_0(s) * rampPsi δ B s` where
   `w_0(s) = gainG (-λ) 1 s = exp(-λ s / (1 + s))` (`λ = 8 K_tr² / ν`) to prove that the
   `w_0`-weighted slice energy `w0J` contracts by `1 / 2` at each Picard step.
4. Passes to the limit using `causalCompleteH`, `causalCompleteT`, `causalSliceAE`,
   `causalEnergyPerturb`, `causalSliceClauses`, `flatIntegrandBound`, `flatIntegrand_free_eq`,
   and `causalNullModification`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace GlobalExistenceAux

/-! ## 1. Unconditional late velocity and global `(1 + s)⁻¹` decay of `trainVel tr` -/

theorem lateVel_unconditional : LateVel := by
  have hHN : PartI.OverlapHighNormUniform := PartI.overlap_highnorm_uniform
  have hFD0 : PartI.OverlapFluctuationDecay := PartI.overlap_fluctuation_decay hHN
  have hMP : PartI.OverlapMeanPrimitive := PartI.overlap_mean_primitive
  have hMD : PartI.OverlapMeanDecay := PartI.overlap_mean_decay hHN hFD0 hMP
  have hOv : PartI.TrainOverlap := PartI.trainOverlap_proof hFD0 hMD
  have hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFD : PartI.TrainFluctuationDecay := PartI.trainFluctuationDecay_proof hTails hFD0 hOv
  have hME : PartI.TrainMeanExpansion := PartI.trainMeanExpansion_proof hTails hFD hMP
  have hS := PartI.trainStreamSmooth
  have hSm := PartIIa.meanStreamSmooth_of (PartIIa.lateProfileSmooth_of hS)
  have hP := PartIIa.meanStreamPointwise_of hME hSm
    (PartIIa.sliceDerivContinuous_of PartIIa.ageDerivSmooth) PartIIa.essSupPointwise
  exact lateVel_of (lateFluctVel_of hFD) (lateMeanVel_of PartI.trainMeanEquations_proof hP)

theorem transWeight_zero (p : ℝ × (ℝ × ℝ)) : transWeight 0 p = 1 := by
  unfold transWeight
  simp

/-- Uniform global `(1 + s)⁻¹` decay of `trainVel tr` for a BUC train `tr` at `c = ν⁻²`
(`0 < ν ≤ ν_v`). -/
theorem trainVel_global_inv_bound :
    ∃ ν_v : ℝ, 0 < ν_v ∧ ∀ ν ∈ Ioc 0 ν_v,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∃ K_tr : ℝ, 0 < K_tr ∧ ∀ s : ℝ, 0 ≤ s → ∀ x : ℝ × ℝ, ∀ i : Fin 2,
          ‖(trainVel tr s x i : ℂ)‖ ≤ K_tr / (1 + s) := by
  obtain ⟨C_v, k_v, ν_v, hCv, hνv, _, hLate⟩ := lateVel_unconditional 0 le_rfl
  refine ⟨ν_v, hνv, fun ν hν tr htr => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hc_eq : ν ^ (-2 : ℝ) = (ν ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hν0.le, Real.rpow_natCast]
  obtain ⟨M₀, hM₀⟩ := htr.sup_bound (by norm_num : (0 : ℝ) ≤ 1)
  set K_tr : ℝ := max (C_v * ν⁻¹ ^ k_v) (max (2 * max M₀ 0) 1)
  have hK_pos : 0 < K_tr := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨K_tr, hK_pos, fun s hs x i => ?_⟩
  have hs1 : 0 < 1 + s := by linarith
  rw [Complex.norm_real]
  unfold trainVel
  rw [ite_eq_left_iff.2 fun h => absurd hs h]
  have hcomp : ‖tr.v s x i‖ ≤ ‖tr.v s x‖ := PiLp.norm_apply_le (tr.v s x) i
  rcases le_or_gt s 1 with hs_le | hs_gt
  · have hb1 : ‖tr.v s x‖ ≤ max M₀ 0 := (hM₀ s ⟨hs, hs_le⟩ x).trans (le_max_left _ _)
    have hb2 : max M₀ 0 ≤ K_tr / (1 + s) := by
      rw [le_div_iff₀ hs1]
      have hK2 : 2 * max M₀ 0 ≤ K_tr := (le_max_left _ _).trans (le_max_right _ _)
      have hM0_nn : 0 ≤ max M₀ 0 := le_max_right _ _
      nlinarith
    exact (hcomp.trans hb1).trans hb2
  · have hb_late := hLate ν hν (ν ^ (-2 : ℝ)) hc_eq tr htr s hs_gt.le x.1 x.2
    rw [transWeight_zero, one_mul, Real.rpow_neg_one, ← div_eq_mul_inv] at hb_late
    have hK1 : C_v * ν⁻¹ ^ k_v ≤ K_tr := le_max_left _ _
    have hb2 : C_v * ν⁻¹ ^ k_v / (1 + s) ≤ K_tr / (1 + s) :=
      div_le_div_of_nonneg_right hK1 hs1.le
    exact (hcomp.trans hb_late).trans hb2

/-! ## 2. Pointwise, `𝒯`-norm, and `w0J`-weighted bounds for `flatMult tr` -/

theorem flatMult_symm {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) :
    flatMult tr u p i j = flatMult tr u p j i := by
  unfold flatMult
  ring

theorem tnorm2_flatMult_sq_le_of_bound {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) {p : ℝ × (ℝ × ℝ)} {M : ℝ} (_hM0 : 0 ≤ M)
    (hM : ∀ i : Fin 2, ‖(trainVel tr p.1 p.2 i : ℂ)‖ ≤ M) :
    tnorm2 (flatMult tr u p) ^ 2 ≤ 8 * M ^ 2 * vnorm2 (u p) ^ 2 := by
  have ht : tnorm2 (flatMult tr u p) ^ 2 =
      ∑ i : Fin 2, ∑ j : Fin 2, ‖flatMult tr u p i j‖ ^ 2 := by
    unfold tnorm2
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hv : vnorm2 (u p) ^ 2 = ∑ i : Fin 2, ‖u p i‖ ^ 2 := by
    unfold vnorm2
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [ht, hv]
  have hij : ∀ i j : Fin 2, ‖flatMult tr u p i j‖ ^ 2 ≤
      2 * M ^ 2 * ‖u p j‖ ^ 2 + 2 * M ^ 2 * ‖u p i‖ ^ 2 := by
    intro i j
    have h1 : ‖flatMult tr u p i j‖ ≤ M * ‖u p j‖ + ‖u p i‖ * M := by
      unfold flatMult
      calc ‖(trainVel tr p.1 p.2 i : ℂ) * u p j + u p i * (trainVel tr p.1 p.2 j : ℂ)‖
          ≤ ‖(trainVel tr p.1 p.2 i : ℂ) * u p j‖ + ‖u p i * (trainVel tr p.1 p.2 j : ℂ)‖ :=
            norm_add_le _ _
        _ = ‖(trainVel tr p.1 p.2 i : ℂ)‖ * ‖u p j‖ + ‖u p i‖ * ‖(trainVel tr p.1 p.2 j : ℂ)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ M * ‖u p j‖ + ‖u p i‖ * M :=
            add_le_add (mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _))
              (mul_le_mul_of_nonneg_left (hM j) (norm_nonneg _))
    have h2 : ‖flatMult tr u p i j‖ ^ 2 ≤ (M * ‖u p j‖ + ‖u p i‖ * M) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (M * ‖u p j‖ - ‖u p i‖ * M)]
  calc ∑ i : Fin 2, ∑ j : Fin 2, ‖flatMult tr u p i j‖ ^ 2
      ≤ ∑ i : Fin 2, ∑ j : Fin 2, (2 * M ^ 2 * ‖u p j‖ ^ 2 + 2 * M ^ 2 * ‖u p i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
    _ = 8 * M ^ 2 * ∑ i : Fin 2, ‖u p i‖ ^ 2 := by
        simp only [Fin.sum_univ_two]
        ring

theorem tnorm2_neg_eq (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (fun i j => -T i j) = tnorm2 T := by
  unfold tnorm2
  simp [norm_neg]

theorem gainConj_neg_ten (γ ν : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    gainConj γ ν (fun p i j => -T p i j) = fun p i j => -gainConj γ ν T p i j := by
  funext p i j
  simp [gainConj, smul_neg]

theorem gainConj_neg_flatMult {ν c : ℝ} (γ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    gainConj γ ν (fun p i j => -flatMult tr u p i j) =
      fun p i j => -flatMult tr (gainConj γ ν u) p i j := by
  rw [← gainConj_flatMult γ tr u, gainConj_neg_ten]

/-- For `s > 0`, `s * (K_tr / (1 + s)) ^ 2 ≤ K_tr ^ 2`. -/
theorem mul_div_one_add_sq_le {K_tr s : ℝ} (hs : 0 < s) :
    s * (K_tr / (1 + s)) ^ 2 ≤ K_tr ^ 2 := by
  have hs1 : 0 < 1 + s := by linarith
  rw [div_pow, mul_div_left_comm]
  have hle : s ≤ (1 + s) ^ 2 := by nlinarith [sq_nonneg s]
  calc K_tr ^ 2 * (s / (1 + s) ^ 2) ≤ K_tr ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (div_le_one_of_le₀ hle (by positivity)) (sq_nonneg _)
    _ = K_tr ^ 2 := mul_one _

/-- Raising the age exponent by one multiplies the density by `s`. -/
theorem lintegral_ageμ_succ {c : ℝ} (hc : 0 < c) (a : ℝ) {f : ℝ × (ℝ × ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ p, f p ∂ageμ c (a + 1) = ∫⁻ p, ENNReal.ofReal p.1 * f p ∂ageμ c a := by
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal p.1 * f p :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul hf
  rw [lintegral_ageμ hc _ hf, lintegral_ageμ hc _ hm]
  refine setLIntegral_congr_fun
    (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)) fun p hp => ?_
  have hs : 0 < p.1 := hp.1
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [Real.rpow_add hs, Real.rpow_one]
  ring

/-- Global `𝒯`-norm bound for `flatMult tr u`:
`tCalNorm c (gainConj γ ν (flatMult tr u)) ≤ ofReal (√8 K_tr) * hCalNorm c (gainConj γ ν u)`. -/
theorem tCalNorm_flatMult_le {ν c γ K_tr : ℝ} (hc : 0 < c) (hK : 0 < K_tr)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr_bd : ∀ s : ℝ, 0 ≤ s → ∀ x : ℝ × ℝ, ∀ i : Fin 2, ‖(trainVel tr s x i : ℂ)‖ ≤ K_tr / (1 + s))
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : ∀ i, Measurable fun p => u p i) :
    tCalNorm c (gainConj γ ν (flatMult tr u)) ≤
      ENNReal.ofReal (Real.sqrt 8 * K_tr) * hCalNorm c (gainConj γ ν u) := by
  apply le_of_sq_le_sq
  have h1 : (ENNReal.ofReal (Real.sqrt 8 * K_tr) * hCalNorm c (gainConj γ ν u)) ^ 2 =
      ENNReal.ofReal (8 * K_tr ^ 2) * hCalNorm c (gainConj γ ν u) ^ 2 := by
    rw [mul_pow, ← ENNReal.ofReal_pow (by positivity)]
    congr 2
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  rw [h1, normSq.2, normSq.1]
  have hexp : (-1 / 2 : ℝ) = -3 / 2 + 1 := by norm_num
  have hTm : Measurable fun p => ENNReal.ofReal (tnorm2 (gainConj γ ν (flatMult tr u) p) ^ 2) :=
    ((measurable_tnorm2 (measurable_gainConj_ten γ ν (measurable_flatMult tr hu))).pow_const 2).ennreal_ofReal
  rw [hexp, lintegral_ageμ_succ hc (-3 / 2) hTm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun p => ?_
  rcases le_or_gt p.1 0 with hp | hp
  · rw [ENNReal.ofReal_of_nonpos hp, zero_mul]
    exact zero_le
  · rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_mul (by positivity), gainConj_flatMult]
    apply ENNReal.ofReal_le_ofReal
    have hs1 : 0 < 1 + p.1 := by linarith
    have hpt := tnorm2_flatMult_sq_le_of_bound tr (gainConj γ ν u)
      (div_nonneg hK.le hs1.le) (htr_bd p.1 hp.le p.2)
    have hmul := mul_le_mul_of_nonneg_left hpt hp.le
    have hs_bd := mul_div_one_add_sq_le (K_tr := K_tr) hp
    nlinarith [sq_nonneg (vnorm2 (gainConj γ ν u p))]

theorem tCalNorm_neg_flatMult_le {ν c γ K_tr : ℝ} (hc : 0 < c) (hK : 0 < K_tr)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr_bd : ∀ s : ℝ, 0 ≤ s → ∀ x : ℝ × ℝ, ∀ i : Fin 2, ‖(trainVel tr s x i : ℂ)‖ ≤ K_tr / (1 + s))
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : ∀ i, Measurable fun p => u p i) :
    tCalNorm c (gainConj γ ν (fun p i j => -flatMult tr u p i j)) ≤
      ENNReal.ofReal (Real.sqrt 8 * K_tr) * hCalNorm c (gainConj γ ν u) := by
  have heq : tCalNorm c (gainConj γ ν (fun p i j => -flatMult tr u p i j)) =
      tCalNorm c (gainConj γ ν (flatMult tr u)) := by
    unfold tCalNorm
    refine eLpNorm_congr_ae (Eventually.of_forall fun p => ?_)
    dsimp only
    rw [gainConj_neg_ten, tnorm2_neg_eq]
  rw [heq]
  exact tCalNorm_flatMult_le hc hK tr htr_bd hu

/-- The `w_0`-weighted slice energy
`∫_{0}^∞ w_0(s) (1 + s)⁻² s⁻¹/² (∫_cell |g⁻¹ u(s, x)|² dx) ds`
where `w_0(s) = gainG (-lam) 1 s = exp(-lam s / (1 + s))`. -/
def w0J (c γ ν lam : ℝ) (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (0 : ℝ),
    ENNReal.ofReal (gainG (-lam) 1 s * (1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) *
      sliceSq c (fun p => vnorm2 (gainConj γ ν u p) ^ 2) s)

theorem gainG_neg_le_one {lam s : ℝ} (hlam : 0 ≤ lam) (hs : 0 ≤ s) :
    gainG (-lam) 1 s ≤ 1 := by
  unfold gainG
  apply Real.exp_le_one_iff.2
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith
  · linarith

theorem one_le_exp_mul_gainG_neg {lam s : ℝ} (hlam : 0 ≤ lam) (hs : 0 ≤ s) :
    1 ≤ Real.exp lam * gainG (-lam) 1 s := by
  unfold gainG
  rw [← Real.exp_add]
  apply Real.one_le_exp
  have hs1 : 0 < 1 + 1 * s := by linarith
  have heq : lam + -lam * s / (1 + 1 * s) = lam / (1 + 1 * s) := by
    field_simp
    ring
  rw [heq]
  positivity

theorem inv_one_add_sq_mul_rpow_le {s : ℝ} (hs : 0 < s) :
    (1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := by
  have hs1 : 0 < 1 + s := by linarith
  have h1 : (1 + s)⁻¹ ^ 2 ≤ s⁻¹ := by
    rw [inv_pow]
    exact inv_anti₀ hs (by nlinarith [sq_nonneg s])
  have h2 : s⁻¹ * s ^ (-1 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_neg_one s, ← Real.rpow_add hs]
    norm_num
  rw [← h2]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hs.le _)

/-- Upper bound `c⁻¹ * w0J c γ ν lam u ≤ hCalNorm c (gainConj γ ν u) ^ 2` for locally `L²` `u`. -/
theorem w0J_le_c_mul_hCalNorm_sq {c γ ν lam : ℝ} (hc : 0 < c) (hlam : 0 ≤ lam)
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : ∀ i, Measurable fun p => u p i)
    (huloc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (gainConj γ ν u p) ^ 2) < ⊤) :
    w0J c γ ν lam u ≤ ENNReal.ofReal c * hCalNorm c (gainConj γ ν u) ^ 2 := by
  have hum' := measurable_gainConj_vec (γ := γ) (ν := ν) hu
  let gU : ℝ × (ℝ × ℝ) → ℝ := fun p => vnorm2 (gainConj γ ν u p) ^ 2
  have hgUm : Measurable gU := measurable_vnorm2_sq hum'
  have hgU0 : ∀ p, 0 ≤ gU p := fun _ => sq_nonneg _
  have hAS := (ageSlice c (-3 / 2) gU hc hgUm hgU0 huloc).1
  rw [normSq.1, hAS, ← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]
  unfold w0J
  refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  apply ENNReal.ofReal_le_ofReal
  have hU0 : 0 ≤ sliceSq c gU s := sliceSq_nonneg hgU0 s
  have hw1 : gainG (-lam) 1 s ≤ 1 := gainG_neg_le_one hlam hs0.le
  have hr : (1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := inv_one_add_sq_mul_rpow_le hs0
  have hcomb : gainG (-lam) 1 s * (1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := by
    calc gainG (-lam) 1 s * (1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ)
        = gainG (-lam) 1 s * ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ)) := by ring
      _ ≤ 1 * s ^ (-3 / 2 : ℝ) :=
          mul_le_mul hw1 hr (by positivity) zero_le_one
      _ = s ^ (-3 / 2 : ℝ) := one_mul _
  exact mul_le_mul_of_nonneg_right hcomb hU0

/-- Upper bound on `tCalNorm c (gainConj γ ν (-flatMult tr u)) ^ 2` in terms of `w0J`. -/
theorem tCalNorm_neg_flatMult_sq_le_w0J {ν c γ lam K_tr : ℝ} (hc : 0 < c) (hlam : 0 ≤ lam)
    (hK : 0 < K_tr) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr_bd : ∀ s : ℝ, 0 ≤ s → ∀ x : ℝ × ℝ, ∀ i : Fin 2, ‖(trainVel tr s x i : ℂ)‖ ≤ K_tr / (1 + s))
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : ∀ i, Measurable fun p => u p i)
    (huloc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (gainConj γ ν u p) ^ 2) < ⊤) :
    tCalNorm c (gainConj γ ν (fun p i j => -flatMult tr u p i j)) ^ 2 ≤
      ENNReal.ofReal (c⁻¹ * 8 * K_tr ^ 2 * Real.exp lam) * w0J c γ ν lam u := by
  let Fd : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => -flatMult tr u p i j
  have hFdm : ∀ i j, Measurable fun p => Fd p i j :=
    fun i j => (measurable_flatMult tr hu i j).neg
  have hFdm' := measurable_gainConj_ten γ ν hFdm
  have hum' := measurable_gainConj_vec (γ := γ) (ν := ν) hu
  let gU : ℝ × (ℝ × ℝ) → ℝ := fun p => vnorm2 (gainConj γ ν u p) ^ 2
  let gQ : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν Fd p) ^ 2
  have hgUm : Measurable gU := measurable_vnorm2_sq hum'
  have hgQm : Measurable gQ := (measurable_tnorm2 hFdm').pow_const 2
  have hgU0 : ∀ p, 0 ≤ gU p := fun _ => sq_nonneg _
  have hgQ0 : ∀ p, 0 ≤ gQ p := fun _ => sq_nonneg _
  have hQloc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (gQ p) < ⊤ := by
    intro s₁ s₂ hs₁ hs₂
    have hmeas_set : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
      measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
    have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (gQ p) ≤
        ENNReal.ofReal (8 * K_tr ^ 2) *
          ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (gU p) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' hmeas_set fun p hp => ?_
      have hp0 : 0 < p.1 := lt_of_lt_of_le hs₁ hp.1.1
      have hs1 : 0 < 1 + p.1 := by linarith
      have h1 : K_tr / (1 + p.1) ≤ K_tr := div_le_self hK.le (by linarith)
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      dsimp [gQ, Fd]
      rw [gainConj_neg_flatMult, tnorm2_neg_eq]
      exact tnorm2_flatMult_sq_le_of_bound tr (gainConj γ ν u) hK.le
        fun i => (htr_bd p.1 hp0.le p.2 i).trans h1
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (huloc s₁ s₂ hs₁ hs₂))
  obtain ⟨hUm, _, hUslice⟩ := sliceLoc c gU hc hgUm hgU0 huloc
  obtain ⟨_, _, hQslice⟩ := sliceLoc c gQ hc hgQm hgQ0 hQloc
  have hAS := (ageSlice c (-1 / 2) gQ hc hgQm hgQ0 hQloc).1
  rw [normSq.2, hAS]
  have hconst : ENNReal.ofReal (c⁻¹ * 8 * K_tr ^ 2 * Real.exp lam) =
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (8 * K_tr ^ 2 * Real.exp lam) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
    congr 1; ring
  rw [hconst, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  unfold w0J
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hUslice, hQslice] with s hs hsU hsQ
  have hs0 : 0 < s := hs
  have hs1 : 0 < 1 + s := by linarith
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hQU : sliceSq c gQ s ≤ 8 * (K_tr / (1 + s)) ^ 2 * sliceSq c gU s := by
    show ∫ x in B0579.cell c, gQ (s, x) ≤ 8 * (K_tr / (1 + s)) ^ 2 * ∫ x in B0579.cell c, gU (s, x)
    rw [← integral_const_mul]
    refine integral_mono hsQ (hsU.const_mul _) fun x => ?_
    dsimp [gQ, Fd]
    rw [gainConj_neg_flatMult, tnorm2_neg_eq]
    exact tnorm2_flatMult_sq_le_of_bound tr (gainConj γ ν u) (div_nonneg hK.le hs1.le)
      (htr_bd s hs0.le x)
  have hw := one_le_exp_mul_gainG_neg hlam hs0.le
  have hU0 : 0 ≤ sliceSq c gU s := sliceSq_nonneg hgU0 s
  have hr0 : 0 ≤ s ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  calc s ^ (-1 / 2 : ℝ) * sliceSq c gQ s
      ≤ s ^ (-1 / 2 : ℝ) * (8 * (K_tr / (1 + s)) ^ 2 * sliceSq c gU s) :=
        mul_le_mul_of_nonneg_left hQU hr0
    _ = 8 * K_tr ^ 2 * 1 * ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * sliceSq c gU s) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ 8 * K_tr ^ 2 * (Real.exp lam * gainG (-lam) 1 s) *
          ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * sliceSq c gU s) := by
        have hpos : 0 ≤ (1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * sliceSq c gU s := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hw hpos]
    _ = 8 * K_tr ^ 2 * Real.exp lam *
          (gainG (-lam) 1 s * (1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * sliceSq c gU s) := by ring

/-! ## 3. The `w0Ramp` cutoff family and one-step contraction of `w0J` -/

/-- The ramp cutoff `rampPsi δ B` weighted by `w_0(s) = gainG (-lam) 1 s = exp(-lam s / (1 + s))`. -/
def w0Ramp (lam δ B s : ℝ) : ℝ :=
  gainG (-lam) 1 s * rampPsi δ B s

theorem rampPsi_contDiff (δ B : ℝ) : ContDiff ℝ 1 (rampPsi δ B) := by
  unfold rampPsi
  exact (smooth_sigma_contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)).mul
    (smooth_sigma_contDiff.comp (((contDiff_const (c := 2 * B)).sub contDiff_id).div_const B))

theorem rampPsi_deriv_le {K δ B : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K) (hδ : 0 < δ) (hB2 : 2 * δ < B) (s : ℝ) :
    deriv (rampPsi δ B) s ≤
      (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
  have hB : 0 < B := by linarith
  by_cases hs : s ∈ Icc δ (2 * δ)
  · simp only [indicator_of_mem hs, mul_one]
    rw [rampPsi_hasDerivAt δ B s hδ hB]
    have ha := abs_le.1 (hK ((s - δ) / δ))
    have hb := abs_le.1 (hK ((2 * B - s) / B))
    have hf0' : Real.smoothTransition ((s - δ) / δ) ≤ 1 := Real.smoothTransition.le_one _
    have hg1 : 0 ≤ Real.smoothTransition ((2 * B - s) / B) := Real.smoothTransition.nonneg _
    have hg1' : Real.smoothTransition ((2 * B - s) / B) ≤ 1 := Real.smoothTransition.le_one _
    have hf0n : 0 ≤ Real.smoothTransition ((s - δ) / δ) := Real.smoothTransition.nonneg _
    have hp : 0 ≤ 1 / δ := by positivity
    have hq : 0 ≤ 1 / B := by positivity
    have hqp : 1 / B ≤ 1 / δ := one_div_le_one_div_of_le hδ (by linarith [hs.1, hs.2])
    have ht : (0 - 1) / B = -(1 / B) := by ring
    rw [ht]
    have hgoal : (2 * K + 1) / δ = (2 * K + 1) * (1 / δ) := by ring
    rw [hgoal]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ha.2) hp) hg1,
      mul_nonneg (mul_nonneg hK0 hp) (sub_nonneg.2 hg1'),
      mul_nonneg (mul_nonneg hf0n hq)
        (by linarith [hb.1] : (0 : ℝ) ≤ K + deriv Real.smoothTransition ((2 * B - s) / B)),
      mul_nonneg (mul_nonneg hK0 hq) (sub_nonneg.2 hf0'),
      mul_nonneg hK0 (sub_nonneg.2 hqp), hp]
  · rw [indicator_of_notMem hs, mul_zero]
    have hsc : s < δ ∨ 2 * δ < s := by
      by_contra hc
      exact hs ⟨not_lt.1 (fun h => hc (Or.inl h)), not_lt.1 (fun h => hc (Or.inr h))⟩
    rcases hsc with h | h
    · have hev : rampPsi δ B =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds h] with y hy
        exact rampPsi_eq_zero_of_lt hδ hy
      rw [hev.deriv_eq]
      simp
    · have hev : rampPsi δ B =ᶠ[𝓝 s] fun y => Real.smoothTransition ((2 * B - y) / B) := by
        filter_upwards [Ioi_mem_nhds h] with y hy
        have hy' : 2 * δ < y := hy
        have h1 : 1 ≤ (y - δ) / δ := by
          rw [le_div_iff₀ hδ]
          linarith
        unfold rampPsi
        rw [Real.smoothTransition.one_of_one_le h1, one_mul]
      rw [hev.deriv_eq]
      have hin2 : HasDerivAt (fun y : ℝ => (2 * B - y) / B) ((0 - 1) / B) s :=
        ((hasDerivAt_const s (2 * B)).sub (hasDerivAt_id' s)).div_const B
      have hd : HasDerivAt (fun y => Real.smoothTransition ((2 * B - y) / B))
          (deriv Real.smoothTransition ((2 * B - s) / B) * ((0 - 1) / B)) s :=
        sigma_comp_hasDerivAt hin2
      rw [hd.deriv]
      have h1 := sigma_deriv_nonneg ((2 * B - s) / B)
      have h2 : (0 - 1) / B ≤ 0 := by
        rw [div_le_iff₀ hB]
        linarith
      nlinarith

theorem w0Ramp_eq_zero_of_not_mem {lam δ B s : ℝ} (hδ : 0 < δ) (hB : 0 < B)
    (hs : s ∉ Icc δ (2 * B)) : w0Ramp lam δ B s = 0 := by
  unfold w0Ramp
  rw [rampPsi_eq_zero_of_not_mem hδ hB hs, mul_zero]

theorem w0Ramp_tsupport_subset {lam δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) :
    tsupport (w0Ramp lam δ B) ⊆ Icc δ (2 * B) := by
  have hsupp : Function.support (w0Ramp lam δ B) ⊆ Icc δ (2 * B) := by
    intro s hs
    by_contra hs'
    exact hs (w0Ramp_eq_zero_of_not_mem hδ hB hs')
  exact closure_minimal hsupp isClosed_Icc

theorem w0Ramp_contDiff (lam : ℝ) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) :
    ContDiff ℝ 1 (w0Ramp lam δ B) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s ∈ tsupport (rampPsi δ B)
  · have hsupp : tsupport (rampPsi δ B) ⊆ Icc δ (2 * B) := by
      refine closure_minimal (fun x hx => ?_) isClosed_Icc
      by_contra hx'
      exact hx (rampPsi_eq_zero_of_not_mem hδ hB hx')
    have hs_pos : 0 < s := lt_of_lt_of_le hδ (hsupp hs).1
    have hden_ne : 1 + 1 * s ≠ 0 := by linarith
    have hnum : ContDiffAt ℝ 1 (fun x : ℝ => -lam * x) s := by fun_prop
    have hden : ContDiffAt ℝ 1 (fun x : ℝ => 1 + 1 * x) s := by fun_prop
    have hg : ContDiffAt ℝ 1 (gainG (-lam) 1) s := by
      unfold gainG
      exact (hnum.div hden hden_ne).exp
    exact hg.mul (rampPsi_contDiff δ B).contDiffAt
  · have h0 : rampPsi δ B =ᶠ[𝓝 s] 0 := notMem_tsupport_iff_eventuallyEq.1 hs
    have h1 : w0Ramp lam δ B =ᶠ[𝓝 s] 0 := by
      filter_upwards [h0] with t ht
      simp [w0Ramp, ht]
    exact contDiffAt_const.congr_of_eventuallyEq h1

theorem w0Ramp_nonneg (lam δ B s : ℝ) : 0 ≤ w0Ramp lam δ B s :=
  mul_nonneg (Real.exp_nonneg _) (rampPsi_nonneg δ B s)

theorem w0Ramp_le_gainG (lam δ B s : ℝ) : w0Ramp lam δ B s ≤ gainG (-lam) 1 s :=
  mul_le_of_le_one_right (Real.exp_nonneg _) (rampPsi_le_one δ B s)

theorem w0Ramp_eq_gainG_on {lam δ B s : ℝ} (hδ : 0 < δ) (hB : 0 < B) (hs : s ∈ Icc (2 * δ) B) :
    w0Ramp lam δ B s = gainG (-lam) 1 s := by
  unfold w0Ramp
  rw [rampPsi_one hδ hB hs, mul_one]

theorem w0Ramp_deriv_add (lam δ B : ℝ) {s : ℝ} (hs : 0 < s) :
    deriv (w0Ramp lam δ B) s + lam * (1 + s)⁻¹ ^ 2 * w0Ramp lam δ B s =
      gainG (-lam) 1 s * deriv (rampPsi δ B) s := by
  have hden_ne : 1 + 1 * s ≠ 0 := by linarith
  have h1 := hasDerivAt_gainG (-lam) 1 hden_ne
  have h2 : HasDerivAt (rampPsi δ B) (deriv (rampPsi δ B) s) s :=
    ((rampPsi_contDiff δ B).differentiable (by norm_num) s).hasDerivAt
  have hd : deriv (w0Ramp lam δ B) s =
      gainG (-lam) 1 s * (-lam / (1 + 1 * s) ^ 2) * rampPsi δ B s +
        gainG (-lam) 1 s * deriv (rampPsi δ B) s := by
    unfold w0Ramp
    exact (h1.mul h2).deriv
  rw [hd]
  unfold w0Ramp
  rw [div_eq_mul_inv, inv_pow, one_mul]
  ring

theorem w0Ramp_deriv_add_le {K lam δ B : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K) (hlam : 0 ≤ lam) (hδ : 0 < δ)
    (hB2 : 2 * δ < B) {s : ℝ} (hs0 : 0 < s) :
    deriv (w0Ramp lam δ B) s + lam * (1 + s)⁻¹ ^ 2 * w0Ramp lam δ B s ≤
      (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
  rw [w0Ramp_deriv_add lam δ B hs0]
  have hd := rampPsi_deriv_le hK0 hK hδ hB2 s
  have hg0 : 0 ≤ gainG (-lam) 1 s := Real.exp_nonneg _
  have hg1 : gainG (-lam) 1 s ≤ 1 := gainG_neg_le_one hlam hs0.le
  calc gainG (-lam) 1 s * deriv (rampPsi δ B) s
      ≤ gainG (-lam) 1 s * ((2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s) :=
        mul_le_mul_of_nonneg_left hd hg0
    _ ≤ (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
        by_cases hs : s ∈ Icc δ (2 * δ)
        · rw [indicator_of_mem hs, mul_one]
          exact mul_le_of_le_one_left (by positivity) hg1
        · rw [indicator_of_notMem hs, mul_zero, mul_zero]

theorem w0Ramp_rhs_bound {C lam δ : ℝ} {A ψ : ℝ → ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hA : ∀ s, 0 ≤ A s)
    (hb : ∀ s, 0 < s →
      deriv ψ s + lam * (1 + s)⁻¹ ^ 2 * ψ s ≤ C / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s)
    (hint : Integrable (fun s => (deriv ψ s + lam * (1 + s)⁻¹ ^ 2 * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
      (volume.restrict (Ioi (0 : ℝ)))) :
    ENNReal.ofReal (∫ s in Ioi (0 : ℝ),
        (deriv ψ s + lam * (1 + s)⁻¹ ^ 2 * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)) ≤
      ENNReal.ofReal (2 * C) * ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
  refine (ofReal_integral_le_lintegral' hint).trans ?_
  have hmeas : MeasurableSet (Ioo (0 : ℝ) (3 * δ)) := measurableSet_Ioo
  calc ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal ((deriv ψ s + lam * (1 + s)⁻¹ ^ 2 * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
      ≤ ∫⁻ s in Ioi (0 : ℝ), (Ioo (0 : ℝ) (3 * δ)).indicator
          (fun s => ENNReal.ofReal (2 * C) * ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) s := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        by_cases hmem : s ∈ Icc δ (2 * δ)
        · have hIoo : s ∈ Ioo (0 : ℝ) (3 * δ) := ⟨hs0, by linarith [hmem.2]⟩
          rw [Set.indicator_of_mem hIoo, ← ENNReal.ofReal_mul (by linarith)]
          apply ENNReal.ofReal_le_ofReal
          have hd := hb s hs0
          rw [Set.indicator_of_mem hmem] at hd
          have hr : s ^ (-1 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) * s := by
            rw [← Real.rpow_add_one hs0.ne']; norm_num
          have hr0 : 0 ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
          have hx : 0 ≤ s ^ (-3 / 2 : ℝ) * A s := mul_nonneg hr0 (hA s)
          have h1 : s ^ (-1 / 2 : ℝ) * A s ≤ 2 * δ * (s ^ (-3 / 2 : ℝ) * A s) := by
            rw [hr]
            nlinarith [mul_le_mul_of_nonneg_right hmem.2 hx]
          have hp : 0 ≤ s ^ (-1 / 2 : ℝ) * A s := mul_nonneg (Real.rpow_nonneg hs0.le _) (hA s)
          calc (deriv ψ s + lam * (1 + s)⁻¹ ^ 2 * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)
              ≤ C / δ * 1 * (s ^ (-1 / 2 : ℝ) * A s) := mul_le_mul_of_nonneg_right hd hp
            _ ≤ C / δ * 1 * (2 * δ * (s ^ (-3 / 2 : ℝ) * A s)) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 2 * C * (s ^ (-3 / 2 : ℝ) * A s) := by field_simp
        · have hd := hb s hs0
          rw [Set.indicator_of_notMem hmem, mul_zero] at hd
          have hp : 0 ≤ s ^ (-1 / 2 : ℝ) * A s := mul_nonneg (Real.rpow_nonneg hs0.le _) (hA s)
          have : (deriv ψ s + lam * (1 + s)⁻¹ ^ 2 * ψ s) * (s ^ (-1 / 2 : ℝ) * A s) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hd hp
          rw [ENNReal.ofReal_of_nonpos this]
          exact zero_le
    _ = ENNReal.ofReal (2 * C) * ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
        have hinter : Ioo (0 : ℝ) (3 * δ) ∩ Ioi 0 = Ioo 0 (3 * δ) :=
          Set.inter_eq_left.2 (fun x hx => hx.1)
        rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas, hinter,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- One-step contraction of `w0J`: if `(d, Gd)` solves the free causal equation with force
`Fd = -flatMult tr u`, and `lam = 8 * K_tr ^ 2 / ν`, then
`w0J c γ ν lam d ≤ ofReal (1 / 2) * w0J c γ ν lam u`. -/
theorem w0J_contraction_step {ν c γ K_tr : ℝ} {μ : ℂ} (hc : 0 < c) (hν : 0 < ν) (hγ : 0 ≤ γ)
    (hμ : 0 < μ.re) (hK : 0 < K_tr) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr_bd : ∀ s : ℝ, 0 ≤ s → ∀ x : ℝ × ℝ, ∀ i : Fin 2, ‖(trainVel tr s x i : ℂ)‖ ≤ K_tr / (1 + s))
    {u d : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {Gd : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hu : ∀ i, Measurable fun p => u p i)
    (huloc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (gainConj γ ν u p) ^ 2) < ⊤)
    (hsol : IsCausalEnergySolution c ν μ (fun _ _ _ => 0)
      (fun p i j => -flatMult tr u p i j) d Gd) :
    w0J c γ ν (8 * K_tr ^ 2 / ν) d ≤
      ENNReal.ofReal (1 / 2) * w0J c γ ν (8 * K_tr ^ 2 / ν) u := by
  set lam : ℝ := 8 * K_tr ^ 2 / ν
  have hlam : 0 < lam := by unfold lam; positivity
  let Fd : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => -flatMult tr u p i j
  have hdm : ∀ i, Measurable fun p => d p i := hsol.measurable
  have hGdm : ∀ i j, Measurable fun p => Gd p i j := hsol.gradMeasurable
  have hFdm : ∀ i j, Measurable fun p => Fd p i j :=
    fun i j => (measurable_flatMult tr hu i j).neg
  have hum' := measurable_gainConj_vec (γ := γ) (ν := ν) hu
  have hdm' := measurable_gainConj_vec (γ := γ) (ν := ν) hdm
  have hGdm' := measurable_gainConj_ten γ ν hGdm
  have hFdm' := measurable_gainConj_ten γ ν hFdm
  have hBG := gainLocBG c ν γ hγ hν d Gd hsol.energyLoc
  have hFloc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (Fd p) ^ 2) < ⊤) ∧
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (tnorm2 (gainConj γ ν Fd p) ^ 2) < ⊤) := by
    intro s₁ s₂ hs₁ hs₂
    have hmeas_set : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
      measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
    have h2 : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (tnorm2 (gainConj γ ν Fd p) ^ 2) < ⊤ := by
      have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (tnorm2 (gainConj γ ν Fd p) ^ 2) ≤
          ENNReal.ofReal (8 * K_tr ^ 2) *
            ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
              ENNReal.ofReal (vnorm2 (gainConj γ ν u p) ^ 2) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_mono' hmeas_set fun p hp => ?_
        have hp0 : 0 < p.1 := lt_of_lt_of_le hs₁ hp.1.1
        have h1 : K_tr / (1 + p.1) ≤ K_tr := div_le_self hK.le (by linarith)
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        dsimp [Fd]
        rw [gainConj_neg_flatMult, tnorm2_neg_eq]
        exact tnorm2_flatMult_sq_le_of_bound tr (gainConj γ ν u) hK.le
          fun i => (htr_bd p.1 hp0.le p.2 i).trans h1
      exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (huloc s₁ s₂ hs₁ hs₂))
    refine ⟨?_, h2⟩
    have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (Fd p) ^ 2) ≤
        ENNReal.ofReal (Real.exp (2 * (γ / ν))) *
          ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
            ENNReal.ofReal (tnorm2 (gainConj γ ν Fd p) ^ 2) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' hmeas_set fun p hp => ?_
      have hp0 : 0 < p.1 := lt_of_lt_of_le hs₁ hp.1.1
      rw [← ENNReal.ofReal_mul (by positivity), tnorm2_gainConj_sq]
      apply ENNReal.ofReal_le_ofReal
      have hg_le : gainG γ ν p.1 ≤ Real.exp (γ / ν) := by
        unfold gainG
        apply Real.exp_le_exp.2
        have hden : 0 < 1 + ν * p.1 := by positivity
        rw [div_le_div_iff₀ hden hν]
        nlinarith
      have h1 : 1 ≤ Real.exp (2 * (γ / ν)) * (gainG γ ν p.1)⁻¹ ^ 2 := by
        have hsq : (gainG γ ν p.1) ^ 2 ≤ Real.exp (2 * (γ / ν)) := by
          calc (gainG γ ν p.1) ^ 2 ≤ (Real.exp (γ / ν)) ^ 2 :=
                pow_le_pow_left₀ (Real.exp_nonneg _) hg_le 2
            _ = Real.exp (2 * (γ / ν)) := by rw [← Real.exp_nat_mul]; ring_nf
        have hgp : gainG γ ν p.1 ≠ 0 := by unfold gainG; exact (Real.exp_pos _).ne'
        calc (1 : ℝ) = (gainG γ ν p.1) ^ 2 * (gainG γ ν p.1)⁻¹ ^ 2 := by
              rw [← mul_pow, mul_inv_cancel₀ hgp, one_pow]
          _ ≤ Real.exp (2 * (γ / ν)) * (gainG γ ν p.1)⁻¹ ^ 2 :=
              mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      nlinarith [sq_nonneg (tnorm2 (Fd p))]
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2)
  let gU : ℝ × (ℝ × ℝ) → ℝ := fun p => vnorm2 (gainConj γ ν u p) ^ 2
  let gV : ℝ × (ℝ × ℝ) → ℝ := fun p => vnorm2 (gainConj γ ν d p) ^ 2
  let gN : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν Gd p) ^ 2
  let gQ : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν Fd p) ^ 2
  have hgUm : Measurable gU := measurable_vnorm2_sq hum'
  have hgVm : Measurable gV := measurable_vnorm2_sq hdm'
  have hgNm : Measurable gN := (measurable_tnorm2 hGdm').pow_const 2
  have hgQm : Measurable gQ := (measurable_tnorm2 hFdm').pow_const 2
  have hgU0 : ∀ p, 0 ≤ gU p := fun _ => sq_nonneg _
  have hgV0 : ∀ p, 0 ≤ gV p := fun _ => sq_nonneg _
  have hgN0 : ∀ p, 0 ≤ gN p := fun _ => sq_nonneg _
  have hgQ0 : ∀ p, 0 ≤ gQ p := fun _ => sq_nonneg _
  obtain ⟨hUm, hUi, hUslice⟩ := sliceLoc c gU hc hgUm hgU0 huloc
  obtain ⟨hVm, hVi, -⟩ := sliceLoc c gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
  obtain ⟨_, hNi, -⟩ := sliceLoc c gN hc hgNm hgN0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2
  obtain ⟨_, hQi, hQslice⟩ := sliceLoc c gQ hc hgQm hgQ0 fun s₁ s₂ h1 h2 => (hFloc s₁ s₂ h1 h2).2
  let U : ℝ → ℝ := sliceSq c gU
  let A : ℝ → ℝ := sliceSq c gV
  let N : ℝ → ℝ := sliceSq c gN
  let M_slice : ℝ → ℝ :=
    sliceSq c (fun p => tnorm2 (gainConj γ ν Fd p) * tnorm2 (gainConj γ ν Gd p))
  let Q : ℝ → ℝ := sliceSq c gQ
  have hnn : ∀ s, 0 ≤ A s ∧ 0 ≤ N s ∧ 0 ≤ M_slice s ∧ 0 ≤ Q s :=
    fun s => ⟨sliceSq_nonneg hgV0 s, sliceSq_nonneg hgN0 s,
      sliceSq_nonneg (fun p => mul_nonneg (tnorm2_nonneg _) (tnorm2_nonneg _)) s,
      sliceSq_nonneg hgQ0 s⟩
  have hU_nn : ∀ s, 0 ≤ U s := fun s => sliceSq_nonneg hgU0 s
  have hWEI := weightedEnergyIdentity c ν γ μ hc hν hγ Fd d Gd
    (fun s₁ s₂ h1 h2 => (hFloc s₁ s₂ h1 h2).1) hFdm hsol
  have hY := youngSlice c (gainConj γ ν Fd) (gainConj γ ν Gd) hc hFdm' hGdm'
    (fun s₁ s₂ h1 h2 => (hFloc s₁ s₂ h1 h2).2)
    (fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2) (2 * ν) (by linarith)
  -- Zero-entrance finiteness for A
  obtain ⟨δ0, hδ0, hfinA⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ s in Ioo 0 δ, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) < ⊤ := by
    obtain ⟨δ, hδ, hfin⟩ := hsol.zeroEntrance
    refine ⟨δ, hδ, ?_⟩
    obtain ⟨-, h2⟩ := ageSlice c (-3 / 2) gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
    have hle : ∫⁻ p, ENNReal.ofReal (gV p)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) ≤
        ∫⁻ p, ENNReal.ofReal (vnorm2 (d p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) := by
      refine lintegral_mono_ae ?_
      have hm : MeasurableSet (Ioo (0 : ℝ) δ ×ˢ (univ : Set (ℝ × ℝ))) :=
        measurableSet_Ioo.prod MeasurableSet.univ
      filter_upwards [ae_restrict_mem hm] with p hp
      have hp1 : 0 < p.1 := hp.1.1
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
        (vnorm2_smul_le (inv_nonneg.2 (Real.exp_pos _).le) (gainG_inv_le_one hγ hν hp1) _) 2
    have hlt := hle.trans_lt hfin
    rw [h2 δ] at hlt
    have hc' : ENNReal.ofReal c⁻¹ ≠ 0 := by simpa using inv_pos.2 hc
    rcases ENNReal.mul_lt_top_iff.1 hlt with h | h | h
    · exact h.2
    · exact absurd h hc'
    · simp [A, h]
  -- Pointwise a.e. slice bound Q(s) ≤ 8 K_tr² (1 + s)⁻² U(s)
  have hQU_ae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      Q s ≤ 8 * K_tr ^ 2 * (1 + s)⁻¹ ^ 2 * U s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hUslice, hQslice] with s hs hsU hsQ
    have hs0 : 0 < s := hs
    have hs1 : 0 < 1 + s := by linarith
    have hcoeff : 8 * K_tr ^ 2 * (1 + s)⁻¹ ^ 2 = 8 * (K_tr / (1 + s)) ^ 2 := by
      rw [div_eq_mul_inv]; ring
    rw [hcoeff]
    show ∫ x in B0579.cell c, gQ (s, x) ≤ 8 * (K_tr / (1 + s)) ^ 2 * ∫ x in B0579.cell c, gU (s, x)
    rw [← integral_const_mul]
    refine integral_mono hsQ (hsU.const_mul _) fun x => ?_
    dsimp [gQ, Fd]
    rw [gainConj_neg_flatMult, tnorm2_neg_eq]
    exact tnorm2_flatMult_sq_le_of_bound tr (gainConj γ ν u) (div_nonneg hK.le hs1.le)
      (htr_bd s hs0.le x)
  -- Sequence of cutoffs ψ_n = w0Ramp lam (1/(n+1)) (n+3)
  obtain ⟨Kσ, hKσ0, hKσ⟩ := sigma_deriv_bound
  set C_ramp : ℝ := 2 * Kσ + 1
  have hC_ramp : 0 < C_ramp := by unfold C_ramp; linarith
  set dn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  set Bn : ℕ → ℝ := fun n => (n : ℝ) + 3
  have hdn_pos : ∀ n, 0 < dn n := fun n => by unfold dn; positivity
  have hBn_gt : ∀ n, 2 * dn n < Bn n := fun n => by
    unfold dn Bn
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
    linarith
  have hdn_lim : Tendsto dn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- Per-n bound
  have hbound : ∀ n : ℕ,
      ENNReal.ofReal lam *
        (∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (w0Ramp lam (dn n) (Bn n) s *
            ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s))) ≤
      ENNReal.ofReal (2 * C_ramp) *
        (∫⁻ s in Ioo 0 (3 * dn n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
      ENNReal.ofReal (1 / 2 * lam) * w0J c γ ν lam u := by
    intro n
    have hδ := hdn_pos n
    have hB2 := hBn_gt n
    have hB0 : 0 < Bn n := by linarith
    have hδ2B : dn n < 2 * Bn n := by linarith
    set ψ : ℝ → ℝ := w0Ramp lam (dn n) (Bn n)
    have hc1 : ContDiff ℝ 1 ψ := w0Ramp_contDiff lam hδ hB0
    have hsupp : tsupport ψ ⊆ Icc (dn n) (2 * Bn n) := w0Ramp_tsupport_subset hδ hB0
    have hcs : HasCompactSupport ψ :=
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsupp
    have hts : tsupport ψ ⊆ Ioi 0 := hsupp.trans fun s hs => lt_of_lt_of_le hδ hs.1
    have hψ0 : ∀ s, 0 ≤ ψ s := w0Ramp_nonneg lam (dn n) (Bn n)
    obtain ⟨hint, hle⟩ := cutoff_young (k := 1 / 4) (ν := ν) (α := 1 / 2 + 2 * μ.re)
      (θ := 2 * ν) (A := A) (N := N) (M := M_slice) (Q := Q) (ψ := ψ) (a := dn n) (b := 2 * Bn n)
      (by linarith) le_rfl (by linarith) hnn
      (hVi (dn n) (2 * Bn n) hδ hδ2B) (hNi (dn n) (2 * Bn n) hδ hδ2B)
      (hQi (dn n) (2 * Bn n) hδ hδ2B) hY hc1 hδ hsupp hψ0 (hWEI ψ hc1 hcs hts hψ0)
    have hcut_nn : 0 ≤ ∫ s in Ioi (0 : ℝ), ψ s * cutG (1 / 4) ν (2 * ν) A N s := by
      refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
      have hs0 : 0 ≤ s := le_of_lt hs
      have hcut : cutG (1 / 4) ν (2 * ν) A N s = 1 / 2 * (s ^ (-3 / 2 : ℝ) * A s) := by
        unfold cutG; ring
      rw [hcut]
      exact mul_nonneg (hψ0 s) (mul_nonneg (by norm_num)
        (mul_nonneg (Real.rpow_nonneg hs0 _) (hnn s).1))
    have hA_inv : IntegrableOn (fun s => (1 + s)⁻¹ ^ 2 * (s ^ (-1 / 2 : ℝ) * A s))
        (Icc (dn n) (2 * Bn n)) := by
      refine IntegrableOn.continuousOn_mul ?_
        (intOn_rpow_mul hδ (hVi (dn n) (2 * Bn n) hδ hδ2B) _) isCompact_Icc
      intro s hs
      have hs1 : 1 + s ≠ 0 := by linarith [hδ, hs.1]
      exact (((continuousAt_const.add continuousAt_id).inv₀ hs1).pow 2).continuousWithinAt
    have iA_w : Integrable (fun s => ψ s * ((1 + s)⁻¹ ^ 2 * (s ^ (-1 / 2 : ℝ) * A s)))
        (volume.restrict (Ioi (0 : ℝ))) :=
      integrable_cutoff_mul hc1 hδ hsupp hA_inv
    have iQ12 : Integrable (fun s => ψ s * (s ^ (-1 / 2 : ℝ) * Q s))
        (volume.restrict (Ioi (0 : ℝ))) :=
      integrable_cutoff_mul hc1 hδ hsupp (intOn_rpow_mul hδ (hQi (dn n) (2 * Bn n) hδ hδ2B) _)
    have hDint : Integrable (fun s => deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s))
        (volume.restrict (Ioi (0 : ℝ))) :=
      integrable_contcutoff_mul (hc1.continuous_deriv le_rfl) hδ
        (tsupport_deriv_subset.trans hsupp) (intOn_rpow_mul hδ (hVi (dn n) (2 * Bn n) hδ hδ2B) _)
    have hcomb_int : Integrable
        (fun s => (deriv ψ s + lam * (1 + s)⁻¹ ^ 2 * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
        (volume.restrict (Ioi (0 : ℝ))) := by
      refine (hDint.add (iA_w.const_mul lam)).congr (Eventually.of_forall fun s => ?_)
      simp only [Pi.add_apply]; ring
    have hcomb_eq : (∫ s in Ioi (0 : ℝ), deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s)) +
          lam * (∫ s in Ioi (0 : ℝ), ψ s * ((1 + s)⁻¹ ^ 2 * (s ^ (-1 / 2 : ℝ) * A s))) =
        ∫ s in Ioi (0 : ℝ),
          (deriv ψ s + lam * (1 + s)⁻¹ ^ 2 * ψ s) * (s ^ (-1 / 2 : ℝ) * A s) := by
      rw [← integral_const_mul, ← integral_add hDint (iA_w.const_mul lam)]
      congr 1; funext s; ring
    have hle_lam : lam * (∫ s in Ioi (0 : ℝ), ψ s * ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s)) ≤
        (∫ s in Ioi (0 : ℝ),
          (deriv ψ s + lam * (1 + s)⁻¹ ^ 2 * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)) +
        (2 * ν)⁻¹ * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s) := by
      have heqA : (fun s => ψ s * ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s)) =
          fun s => ψ s * ((1 + s)⁻¹ ^ 2 * (s ^ (-1 / 2 : ℝ) * A s)) := by
        funext s; ring
      rw [heqA]
      linarith [hcut_nn, hle, hcomb_eq]
    have iA_w' : Integrable (fun s => ψ s * ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s))
        (volume.restrict (Ioi (0 : ℝ))) := by
      refine iA_w.congr (Eventually.of_forall fun s => ?_)
      ring
    have s_lhs : ENNReal.ofReal lam *
        (∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (ψ s * ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s))) =
        ENNReal.ofReal (lam * ∫ s in Ioi (0 : ℝ),
          ψ s * ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s)) := by
      rw [ENNReal.ofReal_mul hlam.le]
      congr 1
      refine (ofReal_integral_eq_lintegral_ofReal iA_w' ?_).symm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 ≤ s := le_of_lt hs
      exact mul_nonneg (hψ0 s) (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))
        (hnn s).1)
    have s_rhs1 := w0Ramp_rhs_bound hδ hC_ramp (fun s => (hnn s).1)
      (fun s hs0 => w0Ramp_deriv_add_le hKσ0 hKσ hlam.le hδ hB2 hs0) hcomb_int
    have s_rhs2 : ENNReal.ofReal ((2 * ν)⁻¹ * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s)) ≤
        ENNReal.ofReal (1 / 2 * lam) * w0J c γ ν lam u := by
      have hlam_eq : (2 * ν)⁻¹ * (8 * K_tr ^ 2) = 1 / 2 * lam := by
        unfold lam; field_simp
      rw [← hlam_eq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      refine (ofReal_integral_le_lintegral' iQ12).trans ?_
      unfold w0J
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hQU_ae] with s hs hsQU
      have hs0 : 0 < s := hs
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hψ_le : ψ s ≤ gainG (-lam) 1 s := w0Ramp_le_gainG lam (dn n) (Bn n) s
      have hr0 : 0 ≤ s ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
      have hUs : 0 ≤ U s := hU_nn s
      calc ψ s * (s ^ (-1 / 2 : ℝ) * Q s)
          ≤ ψ s * (s ^ (-1 / 2 : ℝ) * (8 * K_tr ^ 2 * (1 + s)⁻¹ ^ 2 * U s)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsQU hr0) (hψ0 s)
        _ ≤ gainG (-lam) 1 s * (s ^ (-1 / 2 : ℝ) * (8 * K_tr ^ 2 * (1 + s)⁻¹ ^ 2 * U s)) :=
            mul_le_mul_of_nonneg_right hψ_le (by positivity)
        _ = 8 * K_tr ^ 2 * (gainG (-lam) 1 s * (1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * U s) := by ring
    rw [s_lhs]
    exact (ENNReal.ofReal_le_ofReal hle_lam).trans (ENNReal.ofReal_add_le.trans (add_le_add s_rhs1 s_rhs2))
  -- Fatou on the LHS as n → ∞
  have hfat : w0J c γ ν lam d ≤
      liminf (fun n => ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (w0Ramp lam (dn n) (Bn n) s *
          ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s))) atTop := by
    have hmeasn : ∀ n, Measurable (fun s =>
        ENNReal.ofReal (w0Ramp lam (dn n) (Bn n) s *
          ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s))) := by
      intro n
      have h1 : Measurable (w0Ramp lam (dn n) (Bn n)) :=
        (w0Ramp_contDiff lam (hdn_pos n) (by linarith [hdn_pos n, hBn_gt n])).continuous.measurable
      have h2 : Measurable (fun s : ℝ => (1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s) := by fun_prop
      exact (h1.mul h2).ennreal_ofReal
    calc w0J c γ ν lam d
        = ∫⁻ s in Ioi (0 : ℝ),
            liminf (fun n => ENNReal.ofReal (w0Ramp lam (dn n) (Bn n) s *
              ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s))) atTop := by
          unfold w0J
          refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
          have hs0 : 0 < s := hs
          have e1 : ∀ᶠ n : ℕ in atTop, 2 * dn n < s :=
            (tendsto_order.1 (hdn_lim.const_mul 2)).2 s (by simpa using hs0)
          have e2 : ∀ᶠ n : ℕ in atTop, s ≤ (n : ℝ) :=
            tendsto_natCast_atTop_atTop.eventually_ge_atTop s
          have hev : ∀ᶠ n : ℕ in atTop,
              ENNReal.ofReal (w0Ramp lam (dn n) (Bn n) s *
                ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s)) =
              ENNReal.ofReal (gainG (-lam) 1 s * (1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s) := by
            filter_upwards [e1, e2] with n h1 h2
            have hB0 : 0 < Bn n := by linarith [hdn_pos n, hBn_gt n]
            have hmem : s ∈ Icc (2 * dn n) (Bn n) := ⟨h1.le, by unfold Bn; linarith⟩
            rw [w0Ramp_eq_gainG_on (hdn_pos n) hB0 hmem]
            ring_nf
          have hlim_pt : Tendsto (fun n => ENNReal.ofReal (w0Ramp lam (dn n) (Bn n) s *
              ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s))) atTop
              (𝓝 (ENNReal.ofReal (gainG (-lam) 1 s * (1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s))) :=
            tendsto_const_nhds.congr' (hev.mono fun n h => h.symm)
          exact hlim_pt.liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le hmeasn
  -- Zero-entrance limit as n → ∞
  have hE : Tendsto (fun n => ∫⁻ s in Ioo 0 (3 * dn n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s))
      atTop (𝓝 0) := by
    have hE0 : Tendsto (fun n => ∫⁻ s in Ioo 0 (3 * dn n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)
        ∂(volume.restrict (Ioo 0 δ0))) atTop (𝓝 0) := by
      refine tendsto_setLIntegral_zero (μ := volume.restrict (Ioo 0 δ0))
        (f := fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) hfinA.ne ?_
      have hup : Tendsto (fun n => ENNReal.ofReal (3 * dn n)) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal (hdn_lim.const_mul 3)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun _ => zero_le) (fun n => ?_)
      calc (volume.restrict (Ioo 0 δ0)) (Ioo 0 (3 * dn n)) ≤ volume (Ioo 0 (3 * dn n)) :=
            Measure.restrict_le_self _
        _ = ENNReal.ofReal (3 * dn n) := by simp
    have hev : ∀ᶠ n : ℕ in atTop, 3 * dn n < δ0 :=
      (tendsto_order.1 (hdn_lim.const_mul 3)).2 δ0 (by simpa using hδ0)
    refine hE0.congr' (hev.mono fun n hn => ?_)
    rw [Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.2 (Ioo_subset_Ioo le_rfl hn.le)]
  have hbound' : ∀ n : ℕ,
      (∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (w0Ramp lam (dn n) (Bn n) s *
          ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s))) ≤
      ENNReal.ofReal (lam⁻¹ * (2 * C_ramp)) *
        (∫⁻ s in Ioo 0 (3 * dn n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
      ENNReal.ofReal (1 / 2) * w0J c γ ν lam u := by
    intro n
    calc ∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (w0Ramp lam (dn n) (Bn n) s *
            ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s))
        = ENNReal.ofReal lam⁻¹ * (ENNReal.ofReal lam *
            ∫⁻ s in Ioi (0 : ℝ),
              ENNReal.ofReal (w0Ramp lam (dn n) (Bn n) s *
                ((1 + s)⁻¹ ^ 2 * s ^ (-1 / 2 : ℝ) * A s))) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le),
            inv_mul_cancel₀ hlam.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal lam⁻¹ *
            (ENNReal.ofReal (2 * C_ramp) *
              (∫⁻ s in Ioo 0 (3 * dn n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
            ENNReal.ofReal (1 / 2 * lam) * w0J c γ ν lam u) :=
          mul_le_mul_of_nonneg_left (hbound n) zero_le
      _ = ENNReal.ofReal (lam⁻¹ * (2 * C_ramp)) *
            (∫⁻ s in Ioo 0 (3 * dn n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
          ENNReal.ofReal (1 / 2) * w0J c γ ν lam u := by
          rw [mul_add, ← mul_assoc _ (ENNReal.ofReal (2 * C_ramp)),
            ← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le),
            ← mul_assoc _ (ENNReal.ofReal (1 / 2 * lam)),
            ← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le)]
          congr 3
          field_simp
  have hRHS_lim : Tendsto (fun n => ENNReal.ofReal (lam⁻¹ * (2 * C_ramp)) *
      (∫⁻ s in Ioo 0 (3 * dn n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
      ENNReal.ofReal (1 / 2) * w0J c γ ν lam u) atTop
      (𝓝 (ENNReal.ofReal (1 / 2) * w0J c γ ν lam u)) := by
    have := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (lam⁻¹ * (2 * C_ramp))) hE
      (Or.inr ENNReal.ofReal_ne_top)).add_const (ENNReal.ofReal (1 / 2) * w0J c γ ν lam u)
    simpa using this
  exact hfat.trans ((liminf_le_liminf (Eventually.of_forall hbound')).trans hRHS_lim.liminf_eq.le)

/-! ## 4. Geometric Cauchy series in `𝒯` and Picard iteration -/

theorem tCalNorm_sub_comm (c ν γ : ℝ) (X Y : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    tCalNorm c (gainConj γ ν (fun p i j => X p i j - Y p i j)) =
      tCalNorm c (gainConj γ ν (fun p i j => Y p i j - X p i j)) := by
  unfold tCalNorm
  refine eLpNorm_congr_ae (Eventually.of_forall fun p => ?_)
  have heq : gainConj γ ν (fun p i j => X p i j - Y p i j) p =
      fun i j => -gainConj γ ν (fun p i j => Y p i j - X p i j) p i j := by
    funext i j
    simp [gainConj, smul_sub, neg_sub]
  dsimp only
  rw [heq, tnorm2_neg_eq]

/-- Geometric telescoping bound in `𝒯`: if `‖g⁻¹(Fn (k + 1) - Fn k)‖_𝒯 ≤ K₀ * r ^ k` for all
`k ≥ 1` with `r < 1`, then for all `n, m ≥ 1`,
`‖g⁻¹(Fn n - Fn m)‖_𝒯 ≤ K₀ * (1 - r)⁻¹ * (r ^ n + r ^ m)`. -/
theorem tCalNorm_cauchy_of_geom {c ν γ : ℝ} {Fn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hFm : ∀ n i j, Measurable fun p => Fn n p i j)
    {K₀ r : ℝ≥0∞} (_hr : r < 1)
    (hstep : ∀ k : ℕ, 1 ≤ k →
      tCalNorm c (gainConj γ ν (fun p i j => Fn (k + 1) p i j - Fn k p i j)) ≤ K₀ * r ^ k) :
    ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - Fn m p i j)) ≤
        K₀ * (1 - r)⁻¹ * (r ^ n + r ^ m) := by
  have hadd : ∀ n d : ℕ, 1 ≤ n →
      tCalNorm c (gainConj γ ν (fun p i j => Fn (n + d) p i j - Fn n p i j)) ≤
        K₀ * r ^ n * ∑ i ∈ Finset.range d, r ^ i := by
    intro n d hn
    induction d with
    | zero =>
      simp only [Nat.add_zero, sub_self, Finset.range_zero, Finset.sum_empty, mul_zero, nonpos_iff_eq_zero]
      unfold tCalNorm
      have h0 : (fun p : ℝ × (ℝ × ℝ) => tnorm2 (gainConj γ ν (fun _ _ _ => (0 : ℂ)) p)) =
          (0 : ℝ × (ℝ × ℝ) → ℝ) := by
        funext p
        unfold tnorm2 gainConj
        simp
      rw [h0, eLpNorm_zero]
    | succ d ih =>
      have htri := tCalNormTriangle c ν γ (Fn (n + d + 1)) (Fn (n + d)) (Fn n)
        (hFm (n + d + 1)) (hFm (n + d)) (hFm n)
      rw [tCalNorm_sub_comm c ν γ (Fn n) (Fn (n + d))] at htri
      have h1 := hstep (n + d) (by omega)
      rw [pow_add, ← mul_assoc] at h1
      calc tCalNorm c (gainConj γ ν (fun p i j => Fn (n + (d + 1)) p i j - Fn n p i j))
          ≤ tCalNorm c (gainConj γ ν (fun p i j => Fn (n + d + 1) p i j - Fn (n + d) p i j)) +
              tCalNorm c (gainConj γ ν (fun p i j => Fn (n + d) p i j - Fn n p i j)) := htri
        _ ≤ K₀ * r ^ n * r ^ d + K₀ * r ^ n * ∑ i ∈ Finset.range d, r ^ i := add_le_add h1 ih
        _ = K₀ * r ^ n * ∑ i ∈ Finset.range (d + 1), r ^ i := by
            rw [Finset.sum_range_succ, mul_add, add_comm]
  have hsum_le : ∀ d : ℕ, ∑ i ∈ Finset.range d, r ^ i ≤ (1 - r)⁻¹ := by
    intro d
    rw [← ENNReal.tsum_geometric r]
    exact ENNReal.sum_le_tsum (Finset.range d)
  intro n m hn hm
  rcases le_total n m with hnm | hmn
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [tCalNorm_sub_comm c ν γ (Fn n) (Fn (n + d))]
    calc tCalNorm c (gainConj γ ν (fun p i j => Fn (n + d) p i j - Fn n p i j))
        ≤ K₀ * r ^ n * ∑ i ∈ Finset.range d, r ^ i := hadd n d hn
      _ ≤ K₀ * r ^ n * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left (hsum_le d) zero_le
      _ = K₀ * (1 - r)⁻¹ * r ^ n := by ring
      _ ≤ K₀ * (1 - r)⁻¹ * (r ^ n + r ^ (n + d)) := mul_le_mul_of_nonneg_left le_self_add zero_le
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    calc tCalNorm c (gainConj γ ν (fun p i j => Fn (m + d) p i j - Fn m p i j))
        ≤ K₀ * r ^ m * ∑ i ∈ Finset.range d, r ^ i := hadd m d hm
      _ ≤ K₀ * r ^ m * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left (hsum_le d) zero_le
      _ = K₀ * (1 - r)⁻¹ * r ^ m := by ring
      _ ≤ K₀ * (1 - r)⁻¹ * (r ^ (m + d) + r ^ m) := mul_le_mul_of_nonneg_left le_add_self zero_le

/-- One Picard step: given `u` measurable with `hCalNorm c (gainConj γ ν u) < ⊤`, the force
`F - flatMult tr u` is symmetric, measurable, and has finite `tCalNorm`, hence admits a free causal
energy solution `(b', G')` with `hCalNorm c (gainConj γ ν b') < ⊤` and
`tCalNorm c (gainConj γ ν G') < ⊤`. -/
theorem picard_step_exists {ν c γ K_tr A₀ A'₀ : ℝ} {μ : ℂ} (hc : 0 < c) (hK : 0 < K_tr)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr_bd : ∀ s : ℝ, 0 ≤ s → ∀ x : ℝ × ℝ, ∀ i : Fin 2, ‖(trainVel tr s x i : ℂ)‖ ≤ K_tr / (1 + s))
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hFsym : ∀ p i j, F p i j = F p j i)
    (hFm : ∀ i j, Measurable fun p => F p i j)
    (hFfin : tCalNorm c (gainConj γ ν F) < ⊤)
    (hFree : ∀ F' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
      (∀ p i j, F' p i j = F' p j i) → (∀ i j, Measurable fun p => F' p i j) →
      tCalNorm c (gainConj γ ν F') < ⊤ →
      ∃ b G, IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F' b G ∧
        hCalNorm c (gainConj γ ν b) ≤ ENNReal.ofReal A₀ * tCalNorm c (gainConj γ ν F') ∧
        tCalNorm c (gainConj γ ν G) ≤ ENNReal.ofReal A'₀ * tCalNorm c (gainConj γ ν F'))
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hu : ∀ i, Measurable fun p => u p i)
    (hufin : hCalNorm c (gainConj γ ν u) < ⊤) :
    (∀ p i j, (F p i j - flatMult tr u p i j) = (F p j i - flatMult tr u p j i)) ∧
    (∀ i j, Measurable fun p => F p i j - flatMult tr u p i j) ∧
    tCalNorm c (gainConj γ ν (fun p i j => F p i j - flatMult tr u p i j)) < ⊤ ∧
    ∃ b' G',
      IsCausalEnergySolution c ν μ (fun _ _ _ => 0)
        (fun p i j => F p i j - flatMult tr u p i j) b' G' ∧
      hCalNorm c (gainConj γ ν b') < ⊤ ∧
      tCalNorm c (gainConj γ ν G') < ⊤ := by
  have hsym' : ∀ p i j, F p i j - flatMult tr u p i j = F p j i - flatMult tr u p j i :=
    fun p i j => by rw [hFsym p i j, flatMult_symm tr u p i j]
  have hm' : ∀ i j, Measurable fun p => F p i j - flatMult tr u p i j :=
    fun i j => (hFm i j).sub (measurable_flatMult tr hu i j)
  have hfin' : tCalNorm c (gainConj γ ν (fun p i j => F p i j - flatMult tr u p i j)) < ⊤ := by
    have htri := tCalNormTriangle c ν γ F (fun _ _ _ => 0) (flatMult tr u)
      hFm (fun _ _ => measurable_const) (measurable_flatMult tr hu)
    simp only [sub_zero] at htri
    have hmult_lt : tCalNorm c (gainConj γ ν (flatMult tr u)) < ⊤ :=
      lt_of_le_of_lt (tCalNorm_flatMult_le hc hK tr htr_bd hu)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hufin)
    exact lt_of_le_of_lt htri (ENNReal.add_lt_top.2 ⟨hFfin, hmult_lt⟩)
  obtain ⟨b', G', hsol, hb', hG'⟩ := hFree _ hsym' hm' hfin'
  exact ⟨hsym', hm', hfin', b', G', hsol,
    lt_of_le_of_lt hb' (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin'),
    lt_of_le_of_lt hG' (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin')⟩

/-- Bundled state for the Picard recursion. -/
structure PicardState (c ν γ : ℝ) (μ : ℂ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) where
  b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ
  G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ
  b_prev : ℝ × (ℝ × ℝ) → Fin 2 → ℂ
  b_meas : ∀ i, Measurable fun p => b p i
  b_fin : hCalNorm c (gainConj γ ν b) < ⊤
  sol : IsCausalEnergySolution c ν μ (fun _ _ _ => 0)
    (fun p i j => F p i j - flatMult tr b_prev p i j) b G

end GlobalExistenceAux

open GlobalExistenceAux

/-! ## Main theorem: `trainCausalExistence` (`PartIII-a:T19/3/3`) -/

theorem trainCausalExistence : UnforcedLeray.Short.IIIa.TrainCausalExistence := by
  intro P hP K hK
  obtain ⟨ν_free, hν_free, hFreeSol⟩ := freeCausalExistsUnique P hP K hK
  obtain ⟨ν_eb, hν_eb, hFreeEB⟩ := freeCausalEnergyBound P hP K hK
  obtain ⟨ν_v, hν_v, hVelBd⟩ := trainVel_global_inv_bound
  refine ⟨min (min ν_free ν_eb) ν_v, lt_min (lt_min hν_free hν_eb) hν_v,
    fun ν hν tr htr μ hμ F hFsym hFm hFfin => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_f : ν ∈ Ioc 0 ν_free :=
    ⟨hν0, hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hν_eb' : ν ∈ Ioc 0 ν_eb :=
    ⟨hν0, hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hν_v' : ν ∈ Ioc 0 ν_v := ⟨hν0, hν.2.trans (min_le_right _ _)⟩
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν0 _
  let γ : ℝ := P.eigenvalue.re
  have hγ : 0 ≤ γ := hP.eigenpair.re_pos.le
  have hμre : 0 < μ.re := (hK.2 μ hμ).1
  set A₀ : ℝ := (2 * Real.sqrt ((⨅ μ' : K, μ'.1.re + 1 / 4) * ν))⁻¹
  set A'₀ : ℝ := ν⁻¹
  obtain ⟨K_tr, hK_tr, htr_bd⟩ := hVelBd ν hν_v' tr htr
  -- Free solver specialized to (ν, μ)
  have hFree : ∀ F' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
      (∀ p i j, F' p i j = F' p j i) → (∀ i j, Measurable fun p => F' p i j) →
      tCalNorm c (gainConj γ ν F') < ⊤ →
      ∃ b G, IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F' b G ∧
        hCalNorm c (gainConj γ ν b) ≤ ENNReal.ofReal A₀ * tCalNorm c (gainConj γ ν F') ∧
        tCalNorm c (gainConj γ ν G) ≤ ENNReal.ofReal A'₀ * tCalNorm c (gainConj γ ν F') := by
    intro F' hsym' hm' hfin'
    obtain ⟨b, G, hsol, hb_bd, hG_bd, _⟩ := hFreeSol ν hν_f μ hμ F' hsym' hm' hfin'
    exact ⟨b, G, hsol, hb_bd, hG_bd⟩
  have hFreeBd : ∀ F' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ,
      (∀ p i j, F' p i j = F' p j i) → (∀ i j, Measurable fun p => F' p i j) →
      tCalNorm c (gainConj γ ν F') < ⊤ →
      ∀ b G, IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F' b G →
        hCalNorm c (gainConj γ ν b) ≤ ENNReal.ofReal A₀ * tCalNorm c (gainConj γ ν F') ∧
        tCalNorm c (gainConj γ ν G) ≤ ENNReal.ofReal A'₀ * tCalNorm c (gainConj γ ν F') := by
    intro F' hsym' hm' hfin' b G hsol
    exact hFreeEB ν hν_eb' μ hμ F' hsym' hm' hfin' b G hsol
  -- Step 1: Construct the Picard sequence
  have h0_meas : ∀ i : Fin 2, Measurable fun _ : ℝ × (ℝ × ℝ) => (0 : ℂ) := fun _ => measurable_const
  have h0_fin : hCalNorm c (gainConj γ ν (fun _ _ => (0 : ℂ))) < ⊤ := by
    have h0 : hCalNorm c (gainConj γ ν (fun _ _ => (0 : ℂ))) = 0 := by
      unfold hCalNorm
      have heq : (fun p : ℝ × (ℝ × ℝ) => vnorm2 (gainConj γ ν (fun _ _ => (0 : ℂ)) p)) =
          (0 : ℝ × (ℝ × ℝ) → ℝ) := by
        funext p; unfold vnorm2 gainConj; simp
      rw [heq, eLpNorm_zero]
    rw [h0]; exact ENNReal.zero_lt_top
  obtain ⟨_, _, _, b₁, G₁, hsol₁, hb₁_fin, _⟩ :=
    picard_step_exists hc hK_tr tr htr_bd hFsym hFm hFfin hFree h0_meas h0_fin
  let S₀ : PicardState c ν γ μ tr F :=
    { b := b₁
      G := G₁
      b_prev := fun _ _ => 0
      b_meas := hsol₁.measurable
      b_fin := hb₁_fin
      sol := hsol₁ }
  let nextState : PicardState c ν γ μ tr F → PicardState c ν γ μ tr F := fun st =>
    let hstep := picard_step_exists hc hK_tr tr htr_bd hFsym hFm hFfin hFree st.b_meas st.b_fin
    { b := hstep.2.2.2.choose
      G := hstep.2.2.2.choose_spec.choose
      b_prev := st.b
      b_meas := hstep.2.2.2.choose_spec.choose_spec.1.measurable
      b_fin := hstep.2.2.2.choose_spec.choose_spec.2.1
      sol := hstep.2.2.2.choose_spec.choose_spec.1 }
  let seq : ℕ → PicardState c ν γ μ tr F := fun n => Nat.recOn n S₀ (fun _ st => nextState st)
  have hseq_succ : ∀ n, seq (n + 1) = nextState (seq n) := fun _ => rfl
  let bn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun n =>
    match n with
    | 0 => fun _ _ => 0
    | k + 1 => (seq k).b
  let Gn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun n =>
    match n with
    | 0 => fun _ _ _ => 0
    | k + 1 => (seq k).G
  let Fn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun n p i j =>
    F p i j - flatMult tr (bn n) p i j
  have hbn_prev : ∀ k : ℕ, (seq k).b_prev = bn k := by
    intro k
    cases k with
    | zero => rfl
    | succ k => rfl
  have hbn_meas : ∀ n i, Measurable fun p => bn n p i := by
    intro n i
    cases n with
    | zero => exact measurable_const
    | succ k => exact (seq k).b_meas i
  have hbn_fin : ∀ n, hCalNorm c (gainConj γ ν (bn n)) < ⊤ := by
    intro n
    cases n with
    | zero => exact h0_fin
    | succ k => exact (seq k).b_fin
  have hsol_n : ∀ n, IsCausalEnergySolution c ν μ (fun _ _ _ => 0) (Fn n) (bn (n + 1)) (Gn (n + 1)) := by
    intro n
    show IsCausalEnergySolution c ν μ (fun _ _ _ => 0)
      (fun p i j => F p i j - flatMult tr (bn n) p i j) (seq n).b (seq n).G
    rw [← hbn_prev n]
    exact (seq n).sol
  have hFn_sym : ∀ n p i j, Fn n p i j = Fn n p j i :=
    fun n p i j => by dsimp [Fn]; rw [hFsym p i j, flatMult_symm tr (bn n) p i j]
  have hFn_meas : ∀ n i j, Measurable fun p => Fn n p i j :=
    fun n i j => (hFm i j).sub (measurable_flatMult tr (hbn_meas n) i j)
  have hFn_fin : ∀ n, tCalNorm c (gainConj γ ν (Fn n)) < ⊤ :=
    fun n => (picard_step_exists hc hK_tr tr htr_bd hFsym hFm hFfin hFree (hbn_meas n) (hbn_fin n)).2.2.1
  -- Step 2: Difference solutions and geometric decay of w0J
  set lam : ℝ := 8 * K_tr ^ 2 / ν
  have hlam : 0 < lam := by unfold lam; positivity
  let diff_b : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun n p i => bn (n + 1) p i - bn n p i
  let diff_G : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun n p i j => Gn (n + 1) p i j - Gn n p i j
  have hdiff_meas : ∀ n i, Measurable fun p => diff_b n p i :=
    fun n i => (hbn_meas (n + 1) i).sub (hbn_meas n i)
  have hFn_sub_eq : ∀ k : ℕ, (fun p i j => Fn (k + 1) p i j - Fn k p i j) =
      fun p i j => -flatMult tr (diff_b k) p i j := by
    intro k
    funext p i j
    dsimp [Fn, diff_b, flatMult]
    ring
  have hdiff_sol : ∀ k : ℕ,
      IsCausalEnergySolution c ν μ (fun _ _ _ => 0)
        (fun p i j => -flatMult tr (diff_b k) p i j) (diff_b (k + 1)) (diff_G (k + 1)) := by
    intro k
    have hsub := causalSolSub c ν μ (fun _ _ _ => 0) (Fn (k + 1)) (Fn k)
      (bn (k + 2)) (bn (k + 1)) (Gn (k + 2)) (Gn (k + 1)) (hsol_n (k + 1)) (hsol_n k)
    rwa [hFn_sub_eq k] at hsub
  have hdiff_loc : ∀ k : ℕ, ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (gainConj γ ν (diff_b k) p) ^ 2) < ⊤ := by
    intro k s₁ s₂ hs₁ hs₂
    cases k with
    | zero =>
      have heq : diff_b 0 = bn 1 := by
        funext p i; dsimp [diff_b, bn]; exact sub_zero _
      rw [heq]
      exact (gainLocBG c ν γ hγ hν0 (bn 1) (Gn 1) (hsol_n 0).energyLoc s₁ s₂ hs₁ hs₂).1
    | succ k =>
      exact (gainLocBG c ν γ hγ hν0 (diff_b (k + 1)) (diff_G (k + 1))
        (hdiff_sol k).energyLoc s₁ s₂ hs₁ hs₂).1
  have hw0J_zero_lt : w0J c γ ν lam (diff_b 0) < ⊤ := by
    have heq : diff_b 0 = bn 1 := by
      funext p i; dsimp [diff_b, bn]; exact sub_zero _
    have hle := w0J_le_c_mul_hCalNorm_sq hc hlam.le (hdiff_meas 0) (hdiff_loc 0)
    refine lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    rw [heq, sq]
    exact ENNReal.mul_lt_top (hbn_fin 1) (hbn_fin 1)
  have hw0J_pow : ∀ k : ℕ,
      w0J c γ ν lam (diff_b k) ≤ ENNReal.ofReal (1 / 2) ^ k * w0J c γ ν lam (diff_b 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep := w0J_contraction_step hc hν0 hγ hμre hK_tr tr htr_bd
        (hdiff_meas k) (hdiff_loc k) (hdiff_sol k)
      calc w0J c γ ν lam (diff_b (k + 1))
          ≤ ENNReal.ofReal (1 / 2) * w0J c γ ν lam (diff_b k) := hstep
        _ ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (1 / 2) ^ k * w0J c γ ν lam (diff_b 0)) :=
            mul_le_mul_of_nonneg_left ih zero_le
        _ = ENNReal.ofReal (1 / 2) ^ (k + 1) * w0J c γ ν lam (diff_b 0) := by
            rw [pow_succ', mul_assoc]
  -- Step 3: Geometric step bound for Fn and Cauchy bounds for bn, Gn
  set r : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt 2)⁻¹)
  have hr_sq : r ^ 2 = ENNReal.ofReal (1 / 2) := by
    dsimp [r]
    rw [← ENNReal.ofReal_pow (by positivity), inv_pow, Real.sq_sqrt (by norm_num), one_div]
  have hr_lt : r < 1 := by
    dsimp [r]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_lt_ofReal_iff zero_lt_one |>.2
    rw [inv_lt_one₀ (by positivity)]
    exact Real.one_lt_sqrt_two
  set C_J : ℝ≥0∞ :=
    ENNReal.ofReal (Real.sqrt (c⁻¹ * 8 * K_tr ^ 2 * Real.exp lam)) *
      (w0J c γ ν lam (diff_b 0)) ^ (1 / 2 : ℝ)
  have hCJ_ne_top : C_J ≠ ⊤ := by
    dsimp [C_J]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) hw0J_zero_lt.ne).ne
  have hFn_step : ∀ k : ℕ, 1 ≤ k →
      tCalNorm c (gainConj γ ν (fun p i j => Fn (k + 1) p i j - Fn k p i j)) ≤ C_J * r ^ k := by
    intro k _hk
    apply le_of_sq_le_sq
    rw [hFn_sub_eq k]
    have h1 := tCalNorm_neg_flatMult_sq_le_w0J hc hlam.le hK_tr tr htr_bd (hdiff_meas k) (hdiff_loc k)
    have h2 := hw0J_pow k
    have hrpow2 : (w0J c γ ν lam (diff_b 0) ^ (1 / 2 : ℝ)) ^ 2 = w0J c γ ν lam (diff_b 0) := by
      rw [← ENNReal.rpow_natCast (w0J c γ ν lam (diff_b 0) ^ (1 / 2 : ℝ)) 2,
        ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
    have hpow_eq : (C_J * r ^ k) ^ 2 =
        ENNReal.ofReal (c⁻¹ * 8 * K_tr ^ 2 * Real.exp lam) *
          (ENNReal.ofReal (1 / 2) ^ k * w0J c γ ν lam (diff_b 0)) := by
      dsimp [C_J]
      rw [mul_pow, mul_pow, ← ENNReal.ofReal_pow (by positivity),
        Real.sq_sqrt (by positivity), hrpow2, ← pow_mul, mul_comm k 2, pow_mul, hr_sq]
      ring
    rw [hpow_eq]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 zero_le)
  have hFn_cauchy := tCalNorm_cauchy_of_geom hFn_meas hr_lt hFn_step
  set K_F : ℝ≥0∞ := C_J * (1 - r)⁻¹
  have hKF_ne_top : K_F ≠ ⊤ := by
    dsimp [K_F]
    refine ENNReal.mul_ne_top hCJ_ne_top (ENNReal.inv_ne_top.2 ?_)
    exact (tsub_pos_iff_lt.2 hr_lt).ne'
  let a_seq : ℕ → ℝ≥0∞ := fun n => r ^ n
  have ha_lim : Tendsto a_seq atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr_lt
  -- Shifted sequences bn' n = bn (n + 1), Gn' n = Gn (n + 1)
  let bn' : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun n => bn (n + 1)
  let Gn' : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun n => Gn (n + 1)
  have hbn'_meas : ∀ n i, Measurable fun p => bn' n p i := fun n i => hbn_meas (n + 1) i
  have hGn'_meas : ∀ n i j, Measurable fun p => Gn' n p i j :=
    fun n i j => (hsol_n n).gradMeasurable i j
  have hbd_nm : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      hCalNorm c (gainConj γ ν (fun p i => bn' n p i - bn' m p i)) ≤
        (ENNReal.ofReal A₀ * K_F) * (a_seq n + a_seq m) ∧
      tCalNorm c (gainConj γ ν (fun p i j => Gn' n p i j - Gn' m p i j)) ≤
        (ENNReal.ofReal A'₀ * K_F) * (a_seq n + a_seq m) := by
    intro n m hn hm
    have hF_nm := hFn_cauchy n m hn hm
    have hF_lt : tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - Fn m p i j)) < ⊤ := by
      refine lt_of_le_of_lt hF_nm (ENNReal.mul_lt_top hKF_ne_top.lt_top ?_)
      exact ENNReal.add_lt_top.2
        ⟨lt_of_le_of_lt (pow_le_one₀ zero_le hr_lt.le) ENNReal.one_lt_top,
         lt_of_le_of_lt (pow_le_one₀ zero_le hr_lt.le) ENNReal.one_lt_top⟩
    have hsub_sol := causalSolSub c ν μ (fun _ _ _ => 0) (Fn n) (Fn m)
      (bn' n) (bn' m) (Gn' n) (Gn' m) (hsol_n n) (hsol_n m)
    obtain ⟨hb_le, hG_le⟩ := hFreeBd (fun p i j => Fn n p i j - Fn m p i j)
      (fun p i j => by rw [hFn_sym n p i j, hFn_sym m p i j])
      (fun i j => (hFn_meas n i j).sub (hFn_meas m i j))
      hF_lt (fun p i => bn' n p i - bn' m p i) (fun p i j => Gn' n p i j - Gn' m p i j) hsub_sol
    refine ⟨?_, ?_⟩
    · calc hCalNorm c (gainConj γ ν (fun p i => bn' n p i - bn' m p i))
          ≤ ENNReal.ofReal A₀ * tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - Fn m p i j)) := hb_le
        _ ≤ ENNReal.ofReal A₀ * (K_F * (a_seq n + a_seq m)) := mul_le_mul_of_nonneg_left hF_nm zero_le
        _ = (ENNReal.ofReal A₀ * K_F) * (a_seq n + a_seq m) := by ring
    · calc tCalNorm c (gainConj γ ν (fun p i j => Gn' n p i j - Gn' m p i j))
          ≤ ENNReal.ofReal A'₀ * tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - Fn m p i j)) := hG_le
        _ ≤ ENNReal.ofReal A'₀ * (K_F * (a_seq n + a_seq m)) := mul_le_mul_of_nonneg_left hF_nm zero_le
        _ = (ENNReal.ofReal A'₀ * K_F) * (a_seq n + a_seq m) := by ring
  -- Step 4: Pass to the limit in H and T
  obtain ⟨b, hbm, hb'_lim⟩ := causalCompleteH c ν γ hc hν0 bn' hbn'_meas
    (ENNReal.ofReal A₀ * K_F) a_seq (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKF_ne_top) ha_lim
    ⟨1, fun n m hn hm => (hbd_nm n m hn hm).1⟩
  obtain ⟨G, hGm, hG'_lim⟩ := causalCompleteT c ν γ hc hν0 Gn' hGn'_meas
    (ENNReal.ofReal A'₀ * K_F) a_seq (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKF_ne_top) ha_lim
    ⟨1, fun n m hn hm => (hbd_nm n m hn hm).2⟩
  -- Unshifted bn also converges to b in hCalNorm
  have hb_lim : Tendsto (fun n => hCalNorm c (gainConj γ ν (fun p i => bn n p i - b p i)))
      atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).1 hb'_lim
  -- Define the limit force F_lim = F - flatMult tr b and show Fn n → F_lim in tCalNorm
  let F_lim : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => F p i j - flatMult tr b p i j
  have hFlim_meas : ∀ i j, Measurable fun p => F_lim p i j :=
    fun i j => (hFm i j).sub (measurable_flatMult tr hbm i j)
  have hFn_lim : Tendsto (fun n => tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - F_lim p i j)))
      atTop (𝓝 0) := by
    have hle : ∀ n, tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - F_lim p i j)) ≤
        ENNReal.ofReal (Real.sqrt 8 * K_tr) *
          hCalNorm c (gainConj γ ν (fun p i => bn n p i - b p i)) := by
      intro n
      have heq : (fun p i j => Fn n p i j - F_lim p i j) =
          fun p i j => -flatMult tr (fun q k => bn n q k - b q k) p i j := by
        funext p i j; dsimp [Fn, F_lim, flatMult]; ring
      rw [heq]
      exact tCalNorm_neg_flatMult_le hc hK_tr tr htr_bd fun i => (hbn_meas n i).sub (hbm i)
    have hup : Tendsto (fun n => ENNReal.ofReal (Real.sqrt 8 * K_tr) *
        hCalNorm c (gainConj γ ν (fun p i => bn n p i - b p i))) atTop (𝓝 0) := by
      have h0 := ENNReal.Tendsto.const_mul hb_lim
        (Or.inr (ENNReal.ofReal_ne_top (r := Real.sqrt 8 * K_tr)))
      simpa using h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun _ => zero_le) hle
  -- Extract slice convergence, energyLoc/zeroEntrance, divFree/weakGrad a.e., and weak identity
  obtain ⟨φ, _hφ, hae⟩ := causalSliceAE c ν γ hc hν0 bn' Gn' b G hbn'_meas hbm hGn'_meas hGm
    hb'_lim hG'_lim
  obtain ⟨N, hNb, hNG⟩ : ∃ N : ℕ,
      hCalNorm c (gainConj γ ν (fun p i => bn' N p i - b p i)) < ⊤ ∧
      tCalNorm c (gainConj γ ν (fun p i j => Gn' N p i j - G p i j)) < ⊤ :=
    ((hb'_lim.eventually (gt_mem_nhds ENNReal.zero_lt_top)).and
      (hG'_lim.eventually (gt_mem_nhds ENNReal.zero_lt_top))).exists
  obtain ⟨hEn, hZe⟩ := causalEnergyPerturb c ν γ hc hν0 (bn' N) b (Gn' N) G hbm hGm
    (hbn'_meas N) (hGn'_meas N) (hsol_n N).energyLoc (hsol_n N).zeroEntrance hNb hNG
  have hcl := causalSliceClauses c hc (fun n => bn' (φ n)) (fun n => Gn' (φ n)) b G
    (fun n => hbn'_meas _) hbm (fun n => hGn'_meas _) hGm
    (fun n => (hsol_n (φ n)).energyLoc) (fun n => (hsol_n (φ n)).divFree)
    (fun n => (hsol_n (φ n)).weakGrad) hae
  have hcl' := (ae_restrict_iff' measurableSet_Ioi).1 hcl
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - F_lim p i j)) < ⊤ :=
    eventually_atTop.1 (hFn_lim.eventually (gt_mem_nhds ENNReal.zero_lt_top))
  have hweak_free : ∀ Φ, IsFlatTest c Φ →
      IntegrableOn (flatIntegrand ν μ (fun _ _ _ => 0) F_lim b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν μ (fun _ _ _ => 0) F_lim b Φ p = 0 := by
    intro Φ hΦ
    obtain ⟨C, _hC0, hC⟩ := flatIntegrandBound c ν γ μ hc hν0 Φ hΦ
    have hD : ∀ n, N₀ ≤ n → hCalNorm c (gainConj γ ν (fun p i => bn' n p i - b p i)) < ⊤ →
        IntegrableOn (flatIntegrand ν μ (fun _ _ _ => 0) (fun p i j => Fn n p i j - F_lim p i j)
          (fun p i => bn' n p i - b p i) Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
        ENNReal.ofReal ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          flatIntegrand ν μ (fun _ _ _ => 0) (fun p i j => Fn n p i j - F_lim p i j)
            (fun p i => bn' n p i - b p i) Φ p‖ ≤
          ENNReal.ofReal C * (hCalNorm c (gainConj γ ν (fun p i => bn' n p i - b p i)) +
            tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - F_lim p i j))) := by
      intro n hn hbn'
      exact hC _ _ (fun i j => (hFn_meas n i j).sub (hFlim_meas i j))
        (fun i => (hbn'_meas n i).sub (hbm i)) (hN₀ n hn) hbn'
    have hDeq : ∀ n p, flatIntegrand ν μ (fun _ _ _ => 0) F_lim b Φ p =
        flatIntegrand ν μ (fun _ _ _ => 0) (Fn n) (bn' n) Φ p -
        flatIntegrand ν μ (fun _ _ _ => 0) (fun p i j => Fn n p i j - F_lim p i j)
          (fun p i => bn' n p i - b p i) Φ p := by
      intro n p
      rw [causalLin_flatIntegrand_sub ν μ (fun _ _ _ => 0) (Fn n) F_lim (bn' n) b Φ p]
      ring
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n, N₂ ≤ n → N₀ ≤ n ∧
        hCalNorm c (gainConj γ ν (fun p i => bn' n p i - b p i)) < ⊤ := by
      obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (hb'_lim.eventually (gt_mem_nhds ENNReal.zero_lt_top))
      exact ⟨max N₀ N₃, fun n hn => ⟨le_trans (le_max_left _ _) hn,
        hN₃ n (le_trans (le_max_right _ _) hn)⟩⟩
    have hfun : ∀ n, (fun p => flatIntegrand ν μ (fun _ _ _ => 0) F_lim b Φ p) = fun p =>
        flatIntegrand ν μ (fun _ _ _ => 0) (Fn n) (bn' n) Φ p -
        flatIntegrand ν μ (fun _ _ _ => 0) (fun p i j => Fn n p i j - F_lim p i j)
          (fun p i => bn' n p i - b p i) Φ p := fun n => funext (hDeq n)
    have hint : IntegrableOn (flatIntegrand ν μ (fun _ _ _ => 0) F_lim b Φ)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
      have h1 := (hsol_n N₂).integrable Φ hΦ
      have h2 := (hD N₂ (hN₂ N₂ le_rfl).1 (hN₂ N₂ le_rfl).2).1
      exact (Integrable.sub h1 h2).congr (Eventually.of_forall fun p => (hDeq N₂ p).symm)
    have hval : ∀ n, N₂ ≤ n →
        ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν μ (fun _ _ _ => 0) F_lim b Φ p =
        -∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          flatIntegrand ν μ (fun _ _ _ => 0) (fun p i j => Fn n p i j - F_lim p i j)
            (fun p i => bn' n p i - b p i) Φ p := by
      intro n hn
      have hn' := hN₂ n hn
      have h1 := (hsol_n n).integrable Φ hΦ
      have h2 := (hD n hn'.1 hn'.2).1
      rw [hfun n, integral_sub h1 h2, (hsol_n n).weak Φ hΦ, zero_sub]
    have hr_lim : Tendsto (fun n => ENNReal.ofReal C *
        (hCalNorm c (gainConj γ ν (fun p i => bn' n p i - b p i)) +
          tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - F_lim p i j)))) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (hb'_lim.add hFn_lim) (Or.inr (ENNReal.ofReal_ne_top (r := C)))
      simpa using this
    have hle : ENNReal.ofReal ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        flatIntegrand ν μ (fun _ _ _ => 0) F_lim b Φ p‖ ≤ 0 := by
      refine ge_of_tendsto hr_lim ?_
      rw [eventually_atTop]
      refine ⟨N₂, fun n hn => ?_⟩
      have hn' := hN₂ n hn
      rw [hval n hn, norm_neg]
      exact (hD n hn'.1 hn'.2).2
    refine ⟨hint, ?_⟩
    have h0 : ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        flatIntegrand ν μ (fun _ _ _ => 0) F_lim b Φ p‖ = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.1 (le_antisymm hle zero_le)) (norm_nonneg _)
    exact norm_eq_zero.1 h0
  -- Rewrite flatIntegrand from free with F_lim = F - flatMult tr b to trainVel tr with F
  have hflat_eq : ∀ Φ,
      flatIntegrand ν μ (fun _ _ _ => 0) F_lim b Φ =
        flatIntegrand ν μ (trainVel tr) F b Φ := by
    intro Φ
    have h1 := flatIntegrand_free_eq tr μ F (fun _ _ _ => 0) b Φ
    have h2 : (fun p i j => (F p i j - flatMult tr b p i j) + 0) = F_lim := by
      funext p i j; exact add_zero _
    have h3 : (fun p i j => F p i j + 0) = F := by
      funext p i j; exact add_zero _
    rw [h2, h3] at h1
    exact h1
  have hAE : IsCausalEnergySolutionAE c ν μ (trainVel tr) F b G :=
    { measurable := hbm
      gradMeasurable := hGm
      energyLoc := hEn
      zeroEntrance := hZe
      divFreeAE := hcl'.mono fun s hs h0 => (hs h0).1
      weakGradAE := hcl'.mono fun s hs h0 => (hs h0).2
      integrable := fun Φ hΦ => by rw [← hflat_eq Φ]; exact (hweak_free Φ hΦ).1
      weak := fun Φ hΦ => by rw [← hflat_eq Φ]; exact (hweak_free Φ hΦ).2 }
  exact causalNullModification c ν μ (trainVel tr) hc F b G hAE

end UnforcedLeray.Short.IIIa
