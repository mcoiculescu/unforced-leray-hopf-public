import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.TrainWeightedJetPoly
import UnforcedLeray.Short.PartI.Tasks.SeedUniqueness
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_2_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.RescaledTrain
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3.RescaleRHS
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Part III-a, task `PartIII-a:T21/c3/3/3`: linearised Euler eigenmode error (`ComplModeForceEulerError`, SP 2866-2888, 2991-2995)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2888
and 2991-2995 (`eq:short-causal-damped-complement`, `eq:short-causal-ampl-moving`).

## Mathematical structure and proved infrastructure in this file

1. **Unconditional Part I BUC train jet and rescaled bounds (`trainWeightedJetPoly_uncond`,
   `rescaledTrainBoundsBUC_uncond`)**:
   Assembles the Part I overlap, vorticity/stream tail, fluctuation decay, mean expansion, mean
   equation, and train comparison theorems to prove `TrainWeightedJetPoly` and
   `RescaledTrainBoundsBUC m` unconditionally.

2. **Planar seed eigenvalue uniqueness (`planar_eigenvalue_eq_seed`, `modeEigen_eq_seedModeEigen`,
   `movEulerRes_eq_seed`)**:
   Uses `DirectEulerSub.planar_eigenvalue_eq_seed` (`Short/PartI/Tasks/SeedUniqueness.lean`) to
   identify `P.eigenvalue = lam` and `modeEigen P j = seedModeEigen lam j` for any planar reference
   `P` (`IsPlanarReference P`) and Part I seed kernel `κ` (`IsSeedKernels κ`).

3. **Unconditional measurability of `movEulerRes` (`stronglyMeasurable_kerVelCx`,
   `continuous_movingTrainV`, `continuous_movingTrainGradE`, `aesm_movEulerRes`)**:
   Uses `Cyl.measurable_bsKernel`, `StronglyMeasurable.integral_prod_right'`, and smoothness of
   `perE κ d j`, `tr.u r`, and `B0238.Ec tr r` to prove unconditionally that
   `AEStronglyMeasurable (movEulerRes κ P tr r j) (B0579.cellMeasure d(r) m)` holds for all
   parameters.

4. **Unconditional `L^∞` bound for the periodic Biot-Savart velocity of `perE κ d j`
   (`kerVelCx_perE_bound`)**:
   Combines the near/far decomposition `kerNearFar` (`Sub/T21_2_1/Kernel/NearFar.lean`) with
   periodic translation invariance (`Cyl.lintegral_cell_comp_sub_left`) and the Gaussian cell bound
   `OscillatorForceSub.perSum_pointwise_of_gauss` to prove that `‖kerVelCx d (perE κ d j) y k‖ ≤ C_vel`
   uniformly in `d ≥ 1` and `y ∈ ℝ × ℝ`.

5. **Unconditional `O(d(r)⁻²) = O(ν³ / clockTheta ν r)` rescaled BUC train comparison in
   `X_{m, d(r)}` (`movingTrainV_sub_datum_bound`, `movingTrainGradE_sub_datum_bound`,
   `xNorm_movL_sub_movLGauss_le`)**:
   * Proves the exact scaling identities `movingTrainV_Vc_eq_datum` and
     `movingTrainGradE_Vc_eq_pd_curl_datum` connecting the rescaled periodized Gaussian train
     `Train.Vc ν c r` to `Train.datum d(r)`.
   * Proves `|movingTrainV tr r y k - Train.datum d(r) y k| ≤ C_V * (ν ^ 3 / clockTheta ν r)`
     uniformly on `ℝ × ℝ` from `PartI.trainComparison_proof` (`j = 0`).
   * Proves the weighted vorticity gradient comparison
     `B0579.jb y ^ k_w * |movingTrainGradE tr r y k - B0579.pd k (Cyl.curl (Train.datum d(r))) y| ≤ C_E * (ν ^ 3 / clockTheta ν r)`
     on `B0579.cell d(r)` by applying `vort_alg` (`Sub/T21_2_6/VortErrMoving.lean`) at order
     `j' = 1 + 4` with `t' = clockA ν r ^ 2 * Real.sqrt (clockA ν r) * d(r) ^ 2` together with
     `trainWeightedJetPoly_uncond`.
   * Combines these with `kerVelCx_perE_bound`, `xNorm_le_of_gauss`, and `xNorm_le_of_jb_pow` to
     bound `xNorm d(r) m (fun y => movL tr r (perE κ d(r) j) y - movLGauss d(r) (perE κ d(r) j) y)`
     by `ENNReal.ofReal (C_tr * ν ^ 3 / clockTheta ν r)` unconditionally.

6. **Unconditional `O(d⁻²)` Gaussian periodization tail on the centered cell
   (`perSum_tail_cell_bound`, `perE_sub_seed_e_cell_bound`, `pdCx_perE_sub_seed_e_cell_bound`)**:
   Proves that on `B0579.cell d` (`d ≥ 1`), the periodization tail `perSum d g x - g x` of any
   profile with `exp(-(y₁² + y₂²)/8)` decay satisfies
   `‖perSum d g x - g x‖ ≤ C_tail * (1 / d ^ 2) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16)`.

7. **Conditional assembly (`complModeForceEulerError_of`)**:
   Combines all of the above with the pure Gaussian-cylinder seed-eigenmode residual leaf
   `MovEulerGaussSubBound κ` to establish `ComplModeForceEulerError κ` with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Gaussian-cylinder moving linearised Euler operator and seed-eigenmode residual leaf -/

/-- Planar Biot-Savart velocity of a complex-valued profile `W : ℝ × ℝ → ℂ` at `y : ℝ × ℝ`,
component `i : Fin 2` (`UnforcedLeray.B0009.biotSavart`, SP 662-666). -/
def kerVelPlanarCx (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) (i : Fin 2) : ℂ :=
  UnforcedLeray.B0009.biotSavart (fun z => W (UnforcedLeray.B0009.toPlane z)) i (planeToC y)

/-- Planar linearised Euler operator along the unit Gaussian vortex `Train.v0` (with vorticity
`Train.omega0`) on `ℝ × ℝ` (SP 662-666, 2863-2868). -/
def movLPlanar (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  -(((UnforcedLeray.Train.v0 y 0 : ℝ) : ℂ) * pdCx 0 W y +
      ((UnforcedLeray.Train.v0 y 1 : ℝ) : ℂ) * pdCx 1 W y) -
    (kerVelPlanarCx W y 0 *
        ((B0579.pd 0 UnforcedLeray.Train.omega0 y : ℝ) : ℂ) +
      kerVelPlanarCx W y 1 *
        ((B0579.pd 1 UnforcedLeray.Train.omega0 y : ℝ) : ℂ))

/-- Moving linearised Euler operator along the periodized unit Gaussian vortex `Train.datum d`
on the cell of period `d` (SP 2863-2868). -/
def movLGauss (d : ℝ) (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  -(((UnforcedLeray.Train.datum d y 0 : ℝ) : ℂ) * pdCx 0 W y +
      ((UnforcedLeray.Train.datum d y 1 : ℝ) : ℂ) * pdCx 1 W y) -
    (kerVelCx d W y 0 *
        ((B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ) +
      kerVelCx d W y 1 *
        ((B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ))

/-- Gaussian-cylinder linearised Euler eigenmode defect on mode `j` at cell period `d`:
`movLGauss d (perE κ d j) y - seedModeEigen lam j * perE κ d j y` (SP 2866-2888). -/
def movEulerResGauss (κ : PlanarFrameKernels) (lam : ℂ) (d : ℝ) (j : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  movLGauss d (perE κ d j) y - seedModeEigen lam j * perE κ d j y

/-- **Leaf 1 (`SeedPlanarPointwiseEigen`, `PartIII-a:T21/c3/3/3/1`, SP 662-670, 2866-2870)**:
For any Part I seed triple `(lam, h, ℓ)` (`PartI.IsSeedXG lam (hh.toLp h) ℓ`) realizing `κ`,
the smooth planar eigenmodes `κ.e j` satisfy the classical pointwise planar linearised Euler
eigenvalue equation `movLPlanar (κ.e j) y = seedModeEigen lam j * κ.e j y` on `ℝ × ℝ`. -/
def SeedPlanarPointwiseEigen (κ : PlanarFrameKernels) : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h) ℓ →
    (∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y)) →
    (∀ y, κ.e 1 y = starRingEnd ℂ (PartI.seedPlanar h (planeToC y))) →
    ∀ (j : Fin 2) (y : ℝ × ℝ),
      movLPlanar (κ.e j) y = seedModeEigen lam j * κ.e j y

/-- **Leaf 2 (`MovEulerGaussTailBound`, `PartIII-a:T21/c3/3/3/2`, SP 2866-2888, 2991-2995)**:
The cylinder-to-planar Biot-Savart tail `kerVelCx d (perE κ d j) - kerVelPlanarCx (κ.e j) = O(d⁻²)`
and the Gaussian periodization tails `Train.datum d - Train.v0`, `perE κ d j - κ.e j`, and
`pdCx i (perE κ d j) - pdCx i (κ.e j)` on `B0579.cell d` bound
`(movLGauss d (perE κ d j) - movLPlanar (κ.e j)) - seedModeEigen lam j • (perE κ d j - κ.e j)`
in `X_{m, d}` by `C_G / d ^ 2` for `d ≥ D_G`. -/
def MovEulerGaussTailBound (κ : PlanarFrameKernels) : Prop :=
  ∀ (lam : ℂ) (m : ℝ), 8 < m →
    ∃ C_G D_G : ℝ, 0 ≤ C_G ∧ 1 ≤ D_G ∧
      ∀ d : ℝ, D_G ≤ d → ∀ j : Fin 2,
        xNorm d m (fun y =>
          (movLGauss d (perE κ d j) y - movLPlanar (κ.e j) y) -
            seedModeEigen lam j * (perE κ d j y - κ.e j y)) ≤
          ENNReal.ofReal (C_G / d ^ 2)

/-- **Analytical Leaf (`MovEulerGaussSubBound`, SP 2866-2888, 2991-2995)**:
For any Part I seed triple `(lam, h, ℓ)` (`PartI.IsSeedXG lam (hh.toLp h) ℓ`) realizing `κ`,
planar seed eigenmode cancellation `L_0 e_j = λ_j e_j`, the Gaussian periodization tail of `e_j` on
`B0579.cell d`, and the cylinder-to-planar Biot-Savart tail `K_d - K_∞ = O(d⁻²)` bound the pure
Gaussian-cylinder eigenmode residual `movEulerResGauss κ lam d j` in `X_{m, d}` by `C_G / d ^ 2`
for `d ≥ D_G`. -/
def MovEulerGaussSubBound (κ : PlanarFrameKernels) : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h) ℓ →
    (∀ y, κ.e 0 y = PartI.seedPlanar h (planeToC y)) →
    (∀ y, κ.e 1 y = starRingEnd ℂ (PartI.seedPlanar h (planeToC y))) →
    ∀ m : ℝ, 8 < m →
    ∃ C_G D_G : ℝ, 0 ≤ C_G ∧ 1 ≤ D_G ∧
      ∀ d : ℝ, D_G ≤ d → ∀ j : Fin 2,
        xNorm d m (movEulerResGauss κ lam d j) ≤ ENNReal.ofReal (C_G / d ^ 2)

/-- Assembly of `MovEulerGaussSubBound κ` from `SeedPlanarPointwiseEigen κ` and
`MovEulerGaussTailBound κ`. -/
theorem movEulerGaussSubBound_of (κ : PlanarFrameKernels)
    (hEig : SeedPlanarPointwiseEigen κ) (hTail : MovEulerGaussTailBound κ) :
    MovEulerGaussSubBound κ := by
  intro lam h hh ℓ hSeed he0 he1 m hm
  have heig := hEig lam h hh ℓ hSeed he0 he1
  obtain ⟨C_G, D_G, hCG, hDG, hbd⟩ := hTail lam m hm
  refine ⟨C_G, D_G, hCG, hDG, fun d hd j => ?_⟩
  have hfun : movEulerResGauss κ lam d j = fun y =>
      (movLGauss d (perE κ d j) y - movLPlanar (κ.e j) y) -
        seedModeEigen lam j * (perE κ d j y - κ.e j y) := by
    funext y
    unfold movEulerResGauss
    rw [heig j y]
    ring
  rw [hfun]
  exact hbd d hd j

namespace EulerErrorSub

open OscillatorForceSub ComplCouplingSub DirectEulerSub

/-! ## 1. Unconditional Part I train estimates -/

/-- Unconditional proof of `PartI.TrainOverlap` from the Part I overlap tasks. -/
theorem trainOverlap_uncond : PartI.TrainOverlap :=
  let hHN := PartI.overlap_highnorm_uniform
  let hFD := PartI.overlap_fluctuation_decay hHN
  PartI.trainOverlap_proof hFD (PartI.overlap_mean_decay hHN hFD PartI.overlap_mean_primitive)

/-- Unconditional proof of `PartI.TrainStreamVelocityPressureTails` from the Part I tasks. -/
theorem trainStreamTails_uncond : PartI.TrainStreamVelocityPressureTails :=
  let hOv := trainOverlap_uncond
  PartI.train_stream_velocity_pressure_tails hOv (PartI.train_vorticity_gaussian_tail hOv)

/-- Unconditional proof of `PartI.TrainFluctuationDecay` from the Part I tasks. -/
theorem trainFluctuationDecay_uncond : PartI.TrainFluctuationDecay :=
  PartI.trainFluctuationDecay_proof trainStreamTails_uncond
    (PartI.overlap_fluctuation_decay PartI.overlap_highnorm_uniform) trainOverlap_uncond

/-- Unconditional proof of `PartI.TrainMeanExpansion` from the Part I tasks. -/
theorem trainMeanExpansion_uncond : PartI.TrainMeanExpansion :=
  PartI.trainMeanExpansion_proof trainStreamTails_uncond
    trainFluctuationDecay_uncond PartI.overlap_mean_primitive

/-- Unconditional proof of `TrainWeightedJetPoly` (`Sub/T21_2_6/TrainWeightedJetPoly.lean`). -/
theorem trainWeightedJetPoly_uncond : TrainWeightedJetPoly :=
  trainWeightedJetPoly_of
    (fluctJetWeighted_of trainFluctuationDecay_uncond)
    (meanJetWeighted_of
      (meanVecFormula_of PartI.trainMeanEquations_proof)
      (meanStreamJetBound_of trainMeanExpansion_uncond PartI.trainMeanEquations_proof))
    vcWeightedJet

/-- Unconditional proof of `RescaledTrainBoundsBUC m` (`Clock/WeakSmoothing/RescaledTrain.lean`). -/
theorem rescaledTrainBoundsBUC_uncond (m : ℝ) : RescaledTrainBoundsBUC m :=
  rescaledTrainBounds m PartI.trainComparison_proof trainFluctuationDecay_uncond
    trainMeanExpansion_uncond PartI.trainMeanEquations_proof

/-! ## 2. Planar seed eigenvalue uniqueness and algebraic decomposition of `movEulerRes` -/

/-- For any planar reference `P` (`IsPlanarReference P`) and Part I seed triple `(lam, q, ℓ)`,
`modeEigen P j = seedModeEigen lam j`. -/
theorem modeEigen_eq_seedModeEigen (P : PlanarData) (hP : IsPlanarReference P)
    {lam : ℂ} {q : B0010.XG} {ℓ : B0010.XG →L[ℂ] ℂ} (hIS : PartI.IsSeedXG lam q ℓ)
    (j : Fin 2) :
    modeEigen P j = seedModeEigen lam j := by
  have hlam : P.eigenvalue = lam := planar_eigenvalue_eq_seed P hP hIS
  unfold modeEigen seedModeEigen
  rw [hlam]

/-- Decomposition of `movEulerRes κ P tr r j` into the BUC train comparison defect
`movL tr r (perE κ d j) - movLGauss d (perE κ d j)` plus the Gaussian-cylinder eigenmode residual
`movEulerResGauss κ lam d j`. -/
theorem movEulerRes_eq_trainDiff_add_gauss (κ : PlanarFrameKernels) (P : PlanarData)
    (hP : IsPlanarReference P) {lam : ℂ} {q : B0010.XG} {ℓ : B0010.XG →L[ℂ] ℂ}
    (hIS : PartI.IsSeedXG lam q ℓ) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (j : Fin 2) (y : ℝ × ℝ) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    movEulerRes κ P tr r j y =
      (movL tr r (perE κ d j) y - movLGauss d (perE κ d j) y) +
        movEulerResGauss κ lam d j y := by
  intro d
  unfold movEulerRes movEulerResGauss
  rw [modeEigen_eq_seedModeEigen P hP hIS j]
  ring

/-! ## 3. Unconditional measurability of `kerVelCx` and `movEulerRes` -/

/-- For every `d : ℝ` and `k : Fin 2`, `z ↦ kerD d z k` is measurable. -/
theorem measurable_kerD (d : ℝ) (k : Fin 2) : Measurable (fun z => kerD d z k) :=
  ((PiLp.continuous_apply 2 _ k).measurable).comp (UnforcedLeray.Cyl.measurable_bsKernel d)

/-- For any strongly measurable `W : ℝ × ℝ → ℂ`, `y ↦ kerVelCx d W y k` is strongly measurable. -/
theorem stronglyMeasurable_kerVelCx (d : ℝ) {W : ℝ × ℝ → ℂ} (hW : StronglyMeasurable W)
    (k : Fin 2) :
    StronglyMeasurable (fun y => kerVelCx d W y k) := by
  unfold kerVelCx
  have hk : StronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ((kerD d (p.1 - p.2) k : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_kerD d k).comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  have hprod : StronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      W p.2 * ((kerD d (p.1 - p.2) k : ℝ) : ℂ)) :=
    (hW.comp_measurable measurable_snd).mul hk
  exact hprod.integral_prod_right'

/-- Smoothness and continuity of `perE κ d j` and `pdCx k (perE κ d j)` for `0 < d`. -/
theorem contDiff_two_perE {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) {d : ℝ} (hd : 0 < d)
    (j : Fin 2) :
    ContDiff ℝ 2 (perE κ d j) := by
  have hsm_inf : ContDiff ℝ ∞ (κ.e j) := (seed_e_smooth_decay hκ).1 j
  have hsm2 : ContDiff ℝ 2 (κ.e j) := hsm_inf.of_le (by simp)
  obtain ⟨_, _, h0, h1, h2⟩ := seed_e_translate_bounds hκ j
  have hper_eq : perE κ d j = UnforcedLeray.Gaussian.periodize d (κ.e j) := by
    funext z
    exact perSum_eq_periodize d (κ.e j) z
  rw [hper_eq]
  exact UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (N := (2 : ℕ)) (by norm_num) hd.ne'
    hsm2 (UnforcedLeray.Gaussian.iteratedFDeriv_bounds_of h0 h1 h2)

theorem continuous_perE {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) {d : ℝ} (hd : 0 < d)
    (j : Fin 2) :
    Continuous (perE κ d j) :=
  (contDiff_two_perE hκ hd j).continuous

theorem continuous_pdCx_perE {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) {d : ℝ} (hd : 0 < d)
    (j k : Fin 2) :
    Continuous (pdCx k (perE κ d j)) := by
  unfold pdCx
  exact (((contDiff_two_perE hκ hd j).fderiv_right (m := (1 : ℕ)) (by norm_num)).clm_apply
    contDiff_const).continuous

/-- Continuity of `y ↦ movingTrainV tr r y k` for `r ≥ 0`. -/
theorem continuous_movingTrainV {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {r : ℝ} (hr : 0 ≤ r) (k : Fin 2) :
    Continuous (fun y : ℝ × ℝ => movingTrainV tr r y k) := by
  unfold movingTrainV
  have hsm : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr
  have hproj : Continuous (fun z : ℝ × ℝ => tr.v r z k) :=
    ((PiLp.continuous_apply 2 _ k).comp hsm.continuous)
  have hscale : Continuous (fun y : ℝ × ℝ =>
      (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) := by fun_prop
  exact continuous_const.mul (hproj.comp hscale)

/-- Continuity of `y ↦ movingTrainGradE tr r y k` for `r ≥ 0`. -/
theorem continuous_movingTrainGradE {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {r : ℝ} (hr : 0 ≤ r) (k : Fin 2) :
    Continuous (fun y : ℝ × ℝ => movingTrainGradE tr r y k) := by
  unfold movingTrainGradE B0579.pd
  have hsm : ContDiff ℝ ∞ (UnforcedLeray.B0238.Ec tr r) :=
    dcs_contDiff_curl (UnforcedLeray.B0238.contDiff_Vc tr hr)
  have hpd : Continuous (fun z : ℝ × ℝ =>
      fderiv ℝ (UnforcedLeray.B0238.Ec tr r) z (B0579.dir k)) :=
    ((hsm.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply contDiff_const).continuous
  have hscale : Continuous (fun y : ℝ × ℝ =>
      (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) := by fun_prop
  exact continuous_const.mul (hpd.comp hscale)

/-- Unconditional `AEStronglyMeasurable` for `movEulerRes κ P tr r j`. -/
theorem aesm_movEulerRes {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (P : PlanarData)
    {ν : ℝ} (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {r : ℝ} (hr : 0 ≤ r) (m : ℝ) (j : Fin 2) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    AEStronglyMeasurable (movEulerRes κ P tr r j) (B0579.cellMeasure d m) := by
  intro d
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have hd0 : 0 < d := div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha0)
  have hE_sm : StronglyMeasurable (perE κ d j) := (continuous_perE hκ hd0 j).stronglyMeasurable
  have hpd0_sm : StronglyMeasurable (pdCx 0 (perE κ d j)) :=
    (continuous_pdCx_perE hκ hd0 j 0).stronglyMeasurable
  have hpd1_sm : StronglyMeasurable (pdCx 1 (perE κ d j)) :=
    (continuous_pdCx_perE hκ hd0 j 1).stronglyMeasurable
  have hV0_sm : StronglyMeasurable (fun y => ((movingTrainV tr r y 0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_movingTrainV tr hr 0)).stronglyMeasurable
  have hV1_sm : StronglyMeasurable (fun y => ((movingTrainV tr r y 1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_movingTrainV tr hr 1)).stronglyMeasurable
  have hG0_sm : StronglyMeasurable (fun y => ((movingTrainGradE tr r y 0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_movingTrainGradE tr hr 0)).stronglyMeasurable
  have hG1_sm : StronglyMeasurable (fun y => ((movingTrainGradE tr r y 1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_movingTrainGradE tr hr 1)).stronglyMeasurable
  have hK0_sm : StronglyMeasurable (fun y => kerVelCx d (perE κ d j) y 0) :=
    stronglyMeasurable_kerVelCx d hE_sm 0
  have hK1_sm : StronglyMeasurable (fun y => kerVelCx d (perE κ d j) y 1) :=
    stronglyMeasurable_kerVelCx d hE_sm 1
  have hL_sm : StronglyMeasurable (movL tr r (perE κ d j)) := by
    unfold movL
    exact ((hV0_sm.mul hpd0_sm).add (hV1_sm.mul hpd1_sm)).neg.sub
      ((hK0_sm.mul hG0_sm).add (hK1_sm.mul hG1_sm))
  have hRes_sm : StronglyMeasurable (movEulerRes κ P tr r j) := by
    unfold movEulerRes
    exact hL_sm.sub (stronglyMeasurable_const.mul hE_sm)
  exact hRes_sm.aestronglyMeasurable

/-! ## 4. Unconditional `L^∞` bound for `kerVelCx d (perE κ d j)` -/

/-- Pointwise and cell-integral Gaussian bounds for `perE κ d j` and `pdCx k (perE κ d j)` on
`d ≥ 1`. -/
theorem perE_and_pdCx_gauss_bounds {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ M_E : ℝ, 0 ≤ M_E ∧
      ∀ d : ℝ, 1 ≤ d → ∀ j : Fin 2,
        (∀ x ∈ B0579.cell d, ‖perE κ d j x‖ ≤ M_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16)) ∧
        (∀ y : ℝ × ℝ, ‖perE κ d j y‖ ≤ M_E) ∧
        (∀ k : Fin 2, ∀ x ∈ B0579.cell d,
          ‖pdCx k (perE κ d j) x‖ ≤ M_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16)) := by
  have hdec0 := (seed_e_smooth_decay hκ).2 0
  have hdec1 := (seed_e_smooth_decay hκ).2 1
  obtain ⟨C00, hC00_pos, hC00⟩ := hdec0 0
  obtain ⟨C01, hC01_pos, hC01⟩ := hdec0 1
  obtain ⟨C10, hC10_pos, hC10⟩ := hdec1 0
  obtain ⟨C11, hC11_pos, hC11⟩ := hdec1 1
  set C := max (max C00 C01) (max C10 C11)
  have hC_pos : 0 ≤ C := le_trans hC00_pos (le_trans (le_max_left _ _) (le_max_left _ _))
  have he_bd : ∀ j : Fin 2, ∀ y : ℝ × ℝ,
      ‖κ.e j y‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    intro j y
    have hle : ‖κ.e j y‖ ≤ (1 + ‖y‖) * ‖iteratedFDeriv ℝ 0 (κ.e j) y‖ := by
      rw [norm_iteratedFDeriv_zero]
      nlinarith [norm_nonneg y, norm_nonneg (κ.e j y)]
    fin_cases j
    · refine hle.trans ((hC00 y).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le))
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    · refine hle.trans ((hC10 y).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le))
      exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hpd_bd : ∀ j k : Fin 2, ∀ y : ℝ × ℝ,
      ‖pdCx k (κ.e j) y‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    intro j k y
    have hdir : ‖B0579.dir k‖ ≤ 1 := by
      fin_cases k <;> simp [B0579.dir]
    have hle : ‖pdCx k (κ.e j) y‖ ≤ (1 + ‖y‖) * ‖iteratedFDeriv ℝ 1 (κ.e j) y‖ := by
      unfold pdCx
      rw [norm_iteratedFDeriv_one]
      have h1 := (fderiv ℝ (κ.e j) y).le_opNorm (B0579.dir k)
      have h2 : ‖fderiv ℝ (κ.e j) y‖ * ‖B0579.dir k‖ ≤ ‖fderiv ℝ (κ.e j) y‖ * 1 :=
        mul_le_mul_of_nonneg_left hdir (norm_nonneg _)
      nlinarith [norm_nonneg y, norm_nonneg (fderiv ℝ (κ.e j) y)]
    fin_cases j
    · refine hle.trans ((hC01 y).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le))
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    · refine hle.trans ((hC11 y).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le))
      exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨M0, hM0_pos, hM0⟩ := perSum_pointwise_of_gauss hC_pos (he_bd 0)
  obtain ⟨M1, hM1_pos, hM1⟩ := perSum_pointwise_of_gauss hC_pos (he_bd 1)
  obtain ⟨M00, hM00_pos, hM00⟩ := perSum_pointwise_of_gauss hC_pos (hpd_bd 0 0)
  obtain ⟨M01, hM01_pos, hM01⟩ := perSum_pointwise_of_gauss hC_pos (hpd_bd 0 1)
  obtain ⟨M10, hM10_pos, hM10⟩ := perSum_pointwise_of_gauss hC_pos (hpd_bd 1 0)
  obtain ⟨M11, hM11_pos, hM11⟩ := perSum_pointwise_of_gauss hC_pos (hpd_bd 1 1)
  set M := max (max M0 M1) (max (max M00 M01) (max M10 M11))
  have hM_pos : 0 ≤ M := le_trans hM0_pos (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨M, hM_pos, fun d hd j => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hcell_E : ∀ x ∈ B0579.cell d, ‖perE κ d j x‖ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
    intro x hx
    unfold perE
    fin_cases j
    · refine (hM0 d hd x hx).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    · refine (hM1 d hd x hx).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      exact le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨hcell_E, ?_, ?_⟩
  · intro y
    -- Periodicity of `perE κ d j` reduces any `y ∈ ℝ × ℝ` to `B0579.cell d`
    set y_mod : ℝ × ℝ := (toIcoMod hd0 (-(d / 2)) y.1, y.2)
    have hy_cell : y_mod ∈ B0579.cell d := by
      simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, y_mod]
      have hmem := toIcoMod_mem_Ico hd0 (-(d / 2)) y.1
      refine ⟨by linarith [hmem.1, neg_div d 2], by linarith [hmem.2, neg_div d 2]⟩
    have hy_per : perE κ d j y = perE κ d j y_mod := by
      unfold perE
      have hdiv : y.1 = y_mod.1 + (toIcoDiv hd0 (-(d / 2)) y.1 : ℝ) * d := by
        dsimp [y_mod]
        have h := toIcoMod_add_toIcoDiv_zsmul hd0 (-(d / 2)) y.1
        rw [zsmul_eq_mul] at h
        linarith
      have h1 := perSum_int_period d (κ.e j) (toIcoDiv hd0 (-(d / 2)) y.1) y_mod
      have hy_eq : (y_mod.1 + (toIcoDiv hd0 (-(d / 2)) y.1 : ℝ) * d, y_mod.2) = y := by
        ext
        · exact hdiv.symm
        · rfl
      rw [hy_eq] at h1
      exact h1
    rw [hy_per]
    have hexp_le1 : Real.exp (-(y_mod.1 ^ 2 + y_mod.2 ^ 2) / 16) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg y_mod.1, sq_nonneg y_mod.2]
    calc ‖perE κ d j y_mod‖
        ≤ M * Real.exp (-(y_mod.1 ^ 2 + y_mod.2 ^ 2) / 16) := hcell_E y_mod hy_cell
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left hexp_le1 hM_pos
      _ = M := mul_one M
  · intro k x hx
    -- `pdCx k (perE κ d j) x = perSum d (pdCx k (κ.e j)) x`
    have hsm_inf : ContDiff ℝ ∞ (κ.e j) := (seed_e_smooth_decay hκ).1 j
    have hsm2 : ContDiff ℝ 2 (κ.e j) := hsm_inf.of_le (by simp)
    obtain ⟨C_tr, _, h0, h1, _⟩ := seed_e_translate_bounds hκ j
    have h1' : ∀ z, ‖fderiv ℝ (κ.e j) z‖ ≤ C_tr * (1 + |z.1|) ^ (-(2 : ℝ)) := by
      intro z
      refine (le_mul_of_one_le_left (norm_nonneg _) ?_).trans (h1 z)
      linarith [norm_nonneg z]
    have hper_eq : perE κ d j =
        fun y => ∑' n : ℤ, κ.e j (y - UnforcedLeray.Gaussian.shiftVec d n) := by
      funext z
      unfold perE
      rw [perSum_eq_periodize, UnforcedLeray.Gaussian.periodize_eq]
    have hF := UnforcedLeray.Gaussian.hasFDerivAt_tsum_translates
      (hsm2.differentiable (by norm_num)) (by norm_num) hd0.ne' h0 h1' x
    have hfderiv_per : fderiv ℝ (perE κ d j) x =
        ∑' n : ℤ, fderiv ℝ (κ.e j) (x - UnforcedLeray.Gaussian.shiftVec d n) := by
      rw [hper_eq, hF.fderiv]
      simp_rw [fderiv_comp_sub]
    have hsumD : Summable (fun n : ℤ => fderiv ℝ (κ.e j) (x - UnforcedLeray.Gaussian.shiftVec d n)) :=
      Summable.of_norm_bounded
        ((UnforcedLeray.Gaussian.summable_translate (s := 2) (by norm_num) hd0.ne' x.1).mul_left C_tr)
        (fun n => by rw [UnforcedLeray.Gaussian.sub_shiftVec]; exact h1' _)
    have hev : (∑' n : ℤ, fderiv ℝ (κ.e j) (x - UnforcedLeray.Gaussian.shiftVec d n)) (B0579.dir k) =
        ∑' n : ℤ, fderiv ℝ (κ.e j) (x - UnforcedLeray.Gaussian.shiftVec d n) (B0579.dir k) :=
      (hsumD.hasSum.mapL (ContinuousLinearMap.apply ℝ ℂ (B0579.dir k))).tsum_eq.symm
    have hpd_eq : pdCx k (perE κ d j) x = perSum d (pdCx k (κ.e j)) x := by
      unfold pdCx perSum
      rw [hfderiv_per, hev, ← (Equiv.neg ℤ).tsum_eq]
      refine tsum_congr (fun n => ?_)
      change fderiv ℝ (κ.e j) (x - UnforcedLeray.Gaussian.shiftVec d (-n)) (B0579.dir k) =
        fderiv ℝ (κ.e j) (x.1 + (n : ℝ) * d, x.2) (B0579.dir k)
      congr 2
      ext <;> simp [UnforcedLeray.Gaussian.shiftVec, sub_eq_add_neg]
    rw [hpd_eq]
    fin_cases j <;> fin_cases k
    · refine (hM00 d hd x hx).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    · refine (hM01 d hd x hx).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    · refine (hM10 d hd x hx).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    · refine (hM11 d hd x hx).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

/-- Uniform `L¹(B0579.cell d)` bound for `perE κ d j` for `d ≥ 1`. -/
theorem lintegral_perE_cell_le {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ I_E : ℝ, 0 ≤ I_E ∧
      ∀ d : ℝ, 1 ≤ d → ∀ j : Fin 2,
        (∫⁻ z in B0579.cell d, ‖perE κ d j z‖ₑ) ≤ ENNReal.ofReal I_E := by
  obtain ⟨M_E, hME_pos, hME⟩ := perE_and_pdCx_gauss_bounds hκ
  set g : ℝ × ℝ → ℝ := fun z => M_E * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 16)
  have hg_int : Integrable g := by
    have h1 : Integrable (fun t : ℝ => Real.exp (-(1 / 16 : ℝ) * t ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num)
    have hprod := h1.mul_prod h1
    refine (hprod.const_mul M_E).congr (Eventually.of_forall fun z => ?_)
    dsimp [g]
    rw [← Real.exp_add]
    congr 2
    ring
  have hg_nn : ∀ z, 0 ≤ g z := fun z => mul_nonneg hME_pos (Real.exp_pos _).le
  refine ⟨∫ z, g z, integral_nonneg hg_nn, fun d hd j => ?_⟩
  have hcell_bd := (hME d hd j).1
  have hmeas_cell : MeasurableSet (B0579.cell d) := measurableSet_Ico.prod MeasurableSet.univ
  calc ∫⁻ z in B0579.cell d, ‖perE κ d j z‖ₑ
      ≤ ∫⁻ z in B0579.cell d, ENNReal.ofReal (g z) := by
        refine setLIntegral_mono' hmeas_cell (fun z hz => ?_)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hcell_bd z hz)
    _ ≤ ∫⁻ z, ENNReal.ofReal (g z) := setLIntegral_le_lintegral (B0579.cell d) _
    _ = ENNReal.ofReal (∫ z, g z) := (ofReal_integral_eq_lintegral_ofReal hg_int
        (Eventually.of_forall hg_nn)).symm

/-- **Unconditional `L^∞` bound for `kerVelCx d (perE κ d j)`**:
there exists `C_vel ≥ 0` such that for all `d ≥ 1`, `j, k : Fin 2`, and `y ∈ ℝ × ℝ`,
`‖kerVelCx d (perE κ d j) y k‖ ≤ C_vel`. -/
theorem kerVelCx_perE_bound {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ C_vel : ℝ, 0 ≤ C_vel ∧
      ∀ d : ℝ, 1 ≤ d → ∀ j k : Fin 2, ∀ y : ℝ × ℝ,
        ‖kerVelCx d (perE κ d j) y k‖ ≤ C_vel := by
  obtain ⟨C_NF, hCNF_pos, hNF⟩ := kerNearFar
  obtain ⟨M_E, hME_pos, hME⟩ := perE_and_pdCx_gauss_bounds hκ
  obtain ⟨I_E, hIE_pos, hIE⟩ := lintegral_perE_cell_le hκ
  refine ⟨C_NF * M_E + C_NF * I_E, by positivity, fun d hd j k y => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  obtain ⟨hK_meas, hK_per, _, hK_near, hK_far⟩ := hNF d hd
  obtain ⟨_, hE_sup, _⟩ := hME d hd j
  have hE_int := hIE d hd j
  have hcell_eq : B0579.cell d = UnforcedLeray.Cyl.cell d := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  set near : Set (ℝ × ℝ) := B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1
  set far : Set (ℝ × ℝ) := B0579.cell d \ Metric.ball (0 : ℝ × ℝ) 1
  have hmeas_cell : MeasurableSet (B0579.cell d) := measurableSet_Ico.prod MeasurableSet.univ
  have hmeas_ball : MeasurableSet (Metric.ball (0 : ℝ × ℝ) 1) := Metric.isOpen_ball.measurableSet
  have hmeas_near : MeasurableSet near := hmeas_cell.inter hmeas_ball
  have hmeas_far : MeasurableSet far := hmeas_cell.diff hmeas_ball
  -- Change variables `w = y - z` on `Cyl.cell d` using periodicity of `perE` and `kerD`
  have hG_per : UnforcedLeray.Cyl.IsPeriodic d
      (fun w : ℝ × ℝ => ‖perE κ d j (y - w)‖ₑ * ‖kerD d w k‖ₑ) := by
    intro w
    have hyw : y - (w.1 + d, w.2) = ((y - w).1 + ((-1 : ℤ) : ℝ) * d, (y - w).2) := by
      ext <;> simp; ring
    have hE_p : perE κ d j (y - (w.1 + d, w.2)) = perE κ d j (y - w) := by
      rw [hyw]
      exact perSum_int_period d (κ.e j) (-1) (y - w)
    dsimp only
    rw [hE_p, hK_per w k]
  have hconv_eq :
      (∫⁻ z in B0579.cell d, ‖perE κ d j z * ((kerD d (y - z) k : ℝ) : ℂ)‖ₑ) =
      (∫⁻ w in B0579.cell d, ‖perE κ d j (y - w)‖ₑ * ‖kerD d w k‖ₑ) := by
    have h1 : (fun z => ‖perE κ d j z * ((kerD d (y - z) k : ℝ) : ℂ)‖ₑ) =
        (fun z => ‖perE κ d j (y - (y - z))‖ₑ * ‖kerD d (y - z) k‖ₑ) := by
      funext z
      rw [enorm_mul, sub_sub_cancel]
      congr 1
      rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
    rw [hcell_eq, h1]
    exact UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 hG_per y
  -- Bound the near integral on `B0579.cell d ∩ ball 0 1`
  have hnear_le :
      (∫⁻ w in near, ‖perE κ d j (y - w)‖ₑ * ‖kerD d w k‖ₑ) ≤
        ENNReal.ofReal (C_NF * M_E) := by
    calc ∫⁻ w in near, ‖perE κ d j (y - w)‖ₑ * ‖kerD d w k‖ₑ
        ≤ ∫⁻ w in near, ENNReal.ofReal M_E * ‖kerD d w k‖ₑ := by
          refine setLIntegral_mono' hmeas_near (fun w _ => ?_)
          have hle : ‖perE κ d j (y - w)‖ₑ ≤ ENNReal.ofReal M_E := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hE_sup (y - w))
          gcongr
      _ = ENNReal.ofReal M_E * ∫⁻ w in near, ‖kerD d w k‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M_E * ∫⁻ w in near, ∑ j', ‖kerD d w j'‖ₑ := by
          gcongr with w
          exact Finset.single_le_sum (f := fun j' => ‖kerD d w j'‖ₑ)
            (fun _ _ => bot_le) (Finset.mem_univ k)
      _ ≤ ENNReal.ofReal M_E * ENNReal.ofReal C_NF := by
          gcongr
      _ = ENNReal.ofReal (C_NF * M_E) := by
          rw [← ENNReal.ofReal_mul hME_pos, mul_comm]
  -- Bound the far integral on `B0579.cell d \ ball 0 1`
  have hfar_le :
      (∫⁻ w in far, ‖perE κ d j (y - w)‖ₑ * ‖kerD d w k‖ₑ) ≤
        ENNReal.ofReal (C_NF * I_E) := by
    have hE_per : UnforcedLeray.Cyl.IsPeriodic d (fun z : ℝ × ℝ => ‖perE κ d j z‖ₑ) := by
      intro z
      dsimp only
      have h := perSum_int_period d (κ.e j) 1 z
      simp only [Int.cast_one, one_mul] at h
      rw [show perE κ d j (z.1 + d, z.2) = perSum d (κ.e j) (z.1 + d, z.2) from rfl, h]
      rfl
    have hshift_E : (∫⁻ w in B0579.cell d, ‖perE κ d j (y - w)‖ₑ) =
        (∫⁻ z in B0579.cell d, ‖perE κ d j z‖ₑ) := by
      rw [hcell_eq]
      exact UnforcedLeray.Cyl.lintegral_cell_comp_sub_left hd0 hE_per y
    calc ∫⁻ w in far, ‖perE κ d j (y - w)‖ₑ * ‖kerD d w k‖ₑ
        ≤ ∫⁻ w in far, ‖perE κ d j (y - w)‖ₑ * ENNReal.ofReal C_NF := by
          refine setLIntegral_mono' hmeas_far (fun w hw => ?_)
          have hle : ‖kerD d w k‖ₑ ≤ ENNReal.ofReal C_NF := by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (hK_far w hw.1 hw.2 k)
          gcongr
      _ ≤ ∫⁻ w in B0579.cell d, ‖perE κ d j (y - w)‖ₑ * ENNReal.ofReal C_NF :=
          lintegral_mono_set sdiff_subset
      _ = (∫⁻ w in B0579.cell d, ‖perE κ d j (y - w)‖ₑ) * ENNReal.ofReal C_NF :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = (∫⁻ z in B0579.cell d, ‖perE κ d j z‖ₑ) * ENNReal.ofReal C_NF := by
          rw [hshift_E]
      _ ≤ ENNReal.ofReal I_E * ENNReal.ofReal C_NF := by
          gcongr
      _ = ENNReal.ofReal (C_NF * I_E) := by
          rw [← ENNReal.ofReal_mul hIE_pos, mul_comm]
  -- Combine near and far bounds
  have htot_le :
      ‖kerVelCx d (perE κ d j) y k‖ₑ ≤ ENNReal.ofReal (C_NF * M_E + C_NF * I_E) := by
    unfold kerVelCx
    calc ‖∫ z in B0579.cell d, perE κ d j z * ((kerD d (y - z) k : ℝ) : ℂ)‖ₑ
        ≤ ∫⁻ z in B0579.cell d, ‖perE κ d j z * ((kerD d (y - z) k : ℝ) : ℂ)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ w in B0579.cell d, ‖perE κ d j (y - w)‖ₑ * ‖kerD d w k‖ₑ := hconv_eq
      _ = (∫⁻ w in near, ‖perE κ d j (y - w)‖ₑ * ‖kerD d w k‖ₑ) +
            (∫⁻ w in far, ‖perE κ d j (y - w)‖ₑ * ‖kerD d w k‖ₑ) := by
          rw [← lintegral_inter_add_sdiff _ (B0579.cell d) hmeas_ball]
      _ ≤ ENNReal.ofReal (C_NF * M_E) + ENNReal.ofReal (C_NF * I_E) :=
          add_le_add hnear_le hfar_le
      _ = ENNReal.ofReal (C_NF * M_E + C_NF * I_E) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [← ofReal_norm] at htot_le
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htot_le

/-! ## 5. Unconditional `O(ν³ / clockTheta ν r)` rescaled BUC train comparison in `X_{m, d(r)}` -/

/-- Exact scaling of the periodized Gaussian vortex velocity `Train.Vc`:
`clockA ν r ^ (3 / 2 : ℝ) * Train.Vc ν c r (√a y₁, √a y₂) k = Train.datum (cellLen c (clockA ν r)) y k`. -/
theorem movingTrainV_Vc_eq_datum {ν c r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (y : ℝ × ℝ) (k : Fin 2) :
    clockA ν r ^ (3 / 2 : ℝ) *
        UnforcedLeray.Train.Vc ν c r
          (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) k =
      UnforcedLeray.Train.datum (cellLen c (clockA ν r)) y k := by
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have hsq : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha0
  have hA : clockA ν r = Real.sqrt (clockA ν r) ^ 2 := (Real.sq_sqrt ha0.le).symm
  have hr2 : Real.sqrt (clockA ν r) ^ 2 = UnforcedLeray.Train.width ν r := by
    rw [← hA]; rfl
  have hVc := UnforcedLeray.Short.Spine.vcReg_Vc_scale ν c r (Real.sqrt (clockA ν r)) hr2
    (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)
  have hlx : (Real.sqrt (clockA ν r))⁻¹ •
      (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) = y := by
    ext <;> dsimp <;> field_simp [hsq.ne']
  have hpow : clockA ν r ^ (3 / 2 : ℝ) * (Real.sqrt (clockA ν r))⁻¹ ^ 3 = 1 := by
    have h1 : clockA ν r ^ (3 / 2 : ℝ) = Real.sqrt (clockA ν r) ^ 3 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
      norm_num
    rw [h1, inv_pow, mul_inv_cancel₀ (pow_ne_zero 3 hsq.ne')]
  have hVc_k := congrArg (fun v : UnforcedLeray.Cyl.Vec2 => v k) hVc
  simp only [PiLp.smul_apply, smul_eq_mul, hlx] at hVc_k
  rw [hVc_k, ← mul_assoc, hpow, one_mul]
  rfl

/-- Exact scaling of the periodized Gaussian vorticity gradient `∇(curl (Train.Vc))`:
`clockA ν r ^ (5 / 2 : ℝ) * B0579.pd k (Cyl.curl (Train.Vc ν c r)) (√a y₁, √a y₂) =
  B0579.pd k (Cyl.curl (Train.datum (cellLen c (clockA ν r)))) y`. -/
theorem movingTrainGradE_Vc_eq_pd_curl_datum {ν c r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (y : ℝ × ℝ) (k : Fin 2) :
    clockA ν r ^ ((5 : ℝ) / 2) *
        B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c r))
          (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) =
      B0579.pd k (UnforcedLeray.Cyl.curl
        (UnforcedLeray.Train.datum (cellLen c (clockA ν r)))) y := by
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have hsq : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha0
  have hA : clockA ν r = Real.sqrt (clockA ν r) ^ 2 := (Real.sq_sqrt ha0.le).symm
  have hr2 : Real.sqrt (clockA ν r) ^ 2 = UnforcedLeray.Train.width ν r := by
    rw [← hA]; rfl
  have hVc : UnforcedLeray.Train.Vc ν c r =
      fun z => (Real.sqrt (clockA ν r))⁻¹ ^ 3 •
        UnforcedLeray.Train.datum (cellLen c (clockA ν r))
          ((Real.sqrt (clockA ν r))⁻¹ • z) :=
    funext (UnforcedLeray.Short.Spine.vcReg_Vc_scale ν c r (Real.sqrt (clockA ν r)) hr2)
  have hcurl : UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c r) =
      fun z => ((clockA ν r)⁻¹ ^ 2) *
        UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum (cellLen c (clockA ν r)))
          ((Real.sqrt (clockA ν r))⁻¹ * z.1, (Real.sqrt (clockA ν r))⁻¹ * z.2) := by
    have hpow4 : (Real.sqrt (clockA ν r))⁻¹ ^ 3 * (Real.sqrt (clockA ν r))⁻¹ =
        (clockA ν r)⁻¹ ^ 2 := by
      have h1 : (Real.sqrt (clockA ν r)) ^ 2 = clockA ν r := Real.sq_sqrt ha0.le
      calc (Real.sqrt (clockA ν r))⁻¹ ^ 3 * (Real.sqrt (clockA ν r))⁻¹
          = ((Real.sqrt (clockA ν r)) ^ 2)⁻¹ ^ 2 := by ring
        _ = (clockA ν r)⁻¹ ^ 2 := by rw [h1]
    rw [hVc, dcs_curl_smul_comp]
    funext z
    change (Real.sqrt (clockA ν r))⁻¹ ^ 3 * (Real.sqrt (clockA ν r))⁻¹ *
        UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum (cellLen c (clockA ν r)))
          ((Real.sqrt (clockA ν r))⁻¹ * z.1, (Real.sqrt (clockA ν r))⁻¹ * z.2) = _
    rw [hpow4]
  -- Apply `E0.rescaleRHS_pd` to `G = Cyl.curl (Train.datum d)`
  set G := UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum (cellLen c (clockA ν r)))
  have hG_eq : G = fun y' => clockA ν r ^ 2 *
      UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c r)
        (Real.sqrt (clockA ν r) * y'.1, Real.sqrt (clockA ν r) * y'.2) := by
    funext y'
    rw [hcurl]
    dsimp only
    have hx1 : (Real.sqrt (clockA ν r))⁻¹ * (Real.sqrt (clockA ν r) * y'.1) = y'.1 := by
      field_simp [hsq.ne']
    have hx2 : (Real.sqrt (clockA ν r))⁻¹ * (Real.sqrt (clockA ν r) * y'.2) = y'.2 := by
      field_simp [hsq.ne']
    rw [hx1, hx2, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 ha0.ne'), one_mul]
  have hpd_scale := E0.rescaleRHS_pd
    (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c r))
    (Real.sqrt (clockA ν r)) (clockA ν r ^ 2) hsq (pow_ne_zero 2 ha0.ne') k y
  have hpd_G : B0579.pd k G y =
      clockA ν r ^ 2 * Real.sqrt (clockA ν r) *
        B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c r))
          (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) := by
    rw [hG_eq, hpd_scale, ← mul_assoc]
  rw [hpd_G]
  congr 1
  have hpow : clockA ν r ^ ((5 : ℝ) / 2) = clockA ν r ^ 2 * Real.sqrt (clockA ν r) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (clockA ν r) 2, ← Real.rpow_add ha0]
    norm_num
  exact hpow

/-- Unconditional `O(ν³ / clockTheta ν r)` bound for the rescaled velocity error
`movingTrainV tr r y k - Train.datum d(r) y k` on `ℝ × ℝ`. -/
theorem movingTrainV_sub_datum_bound :
    ∃ C_V ν_V : ℝ, 0 ≤ C_V ∧ 0 < ν_V ∧
      ∀ ν ∈ Ioc 0 ν_V,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          PartI.IsBUCTrain tr →
          ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r →
          ∀ y : ℝ × ℝ, ∀ k : Fin 2,
            let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
            |movingTrainV tr r y k - UnforcedLeray.Train.datum d y k| ≤
              C_V * ν ^ 3 / clockTheta ν r := by
  obtain ⟨C0, β0, N0, hC0, hβ0, hN0, hbd⟩ := PartI.trainComparison_proof 2 (by norm_num) 0
  refine ⟨2 * C0 / β0 ^ 2, min 1 N0, by positivity, lt_min zero_lt_one hN0,
    fun ν hν tr hbuc r hr hθ y k => ?_⟩
  intro d
  have hν_pos : 0 < ν := hν.1
  have hν_le1 : ν ≤ 1 := hν.2.trans (min_le_left _ _)
  have hν_N0 : ν ≤ N0 := hν.2.trans (min_le_right _ _)
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν_pos.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hd_ge1 : 1 ≤ d := one_le_cellLen_of_theta hν_pos hν_le1 hr hθ
  have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd_ge1
  have hac : clockA ν r ≤ (ν ^ (-2 : ℝ)) ^ 2 := by
    obtain ⟨_, ha_le, _, _⟩ := vort_clock hν_pos hν_le1 hr hθ
    have hcsq : (ν ^ (-2 : ℝ)) ^ 2 = (ν⁻¹) ^ 4 := by
      rw [Real.rpow_neg hν_pos.le, Real.rpow_two]; ring
    rw [hcsq]
    have hx1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν_pos).mpr hν_le1
    calc clockA ν r ≤ ν⁻¹ := ha_le
      _ = (ν⁻¹) ^ 1 := (pow_one _).symm
      _ ≤ (ν⁻¹) ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  have hbj := (hbd ν hν_pos hν_N0 tr hbuc r hr hac).2
  set z : ℝ × ℝ := (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)
  have hM : 0 ≤ C0 * ν⁻¹ * clockA ν r ^ (-((5 + ((0 : ℕ) : ℝ)) / 2)) *
      Real.exp (-(β0 * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0.le (inv_nonneg.2 hν_pos.le))
      (Real.rpow_nonneg ha0.le _)) (Real.exp_nonneg _)
  have hpt := UnforcedLeray.B0277.norm_le_of_supNormD_le hM hbj z
  rw [norm_iteratedFDeriv_zero, Nat.cast_zero] at hpt
  have hcomp_le : |tr.v r z k - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r z k| ≤
      ‖tr.v r z - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r z‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (tr.v r z - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r z) k
  have hdiff_eq : movingTrainV tr r y k - UnforcedLeray.Train.datum d y k =
      clockA ν r ^ (3 / 2 : ℝ) *
        (tr.v r z k - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r z k) := by
    rw [mul_sub, movingTrainV_Vc_eq_datum hν_pos hr y k]
    rfl
  have hd_sq : (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r = d ^ 2 := by
    dsimp [d, cellLen]
    rw [div_pow, Real.sq_sqrt ha0.le]
  -- Bound `exp(-β0 * d^2) ≤ 2 / (β0^2 * d^4)` via `t^2 / 2 ≤ exp t`
  have hexp_d4 : Real.exp (-(β0 * d ^ 2)) ≤ 2 / (β0 ^ 2 * d ^ 4) := by
    have ht : 0 < β0 * d ^ 2 := by positivity
    have h2 : (β0 * d ^ 2) ^ 2 / 2 ≤ Real.exp (β0 * d ^ 2) := by
      have hfac := Real.pow_div_factorial_le_exp (β0 * d ^ 2) ht.le 2
      have hfac2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num
      rwa [hfac2] at hfac
    rw [Real.exp_neg, ← one_div]
    have hpos_sq : 0 < (β0 * d ^ 2) ^ 2 / 2 := by positivity
    have hinv := one_div_le_one_div_of_le hpos_sq h2
    calc 1 / Real.exp (β0 * d ^ 2)
        ≤ 1 / ((β0 * d ^ 2) ^ 2 / 2) := hinv
      _ = 2 / (β0 ^ 2 * d ^ 4) := by ring
  -- Notice `clockTheta ν r ≤ d ^ 2` since `1 / d^2 = ν^3 / clockTheta ν r` and `ν^3 ≤ 1`
  have hd2_inv : 1 / d ^ 2 = ν ^ 3 / clockTheta ν r :=
    inv_cellLen_sq_eq_nu_cube_div_theta hν_pos hr
  have hθ_pos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ
  have hθ_le_d2 : clockTheta ν r ≤ d ^ 2 := by
    have hν3_le1 : ν ^ 3 ≤ 1 := pow_le_one₀ hν_pos.le hν_le1
    have h1 : clockTheta ν r * (1 / d ^ 2) = ν ^ 3 := by
      rw [hd2_inv, mul_div_cancel₀ _ hθ_pos.ne']
    have h2 : clockTheta ν r * (1 / d ^ 2) ≤ 1 := h1.le.trans hν3_le1
    rwa [mul_one_div, div_le_one (by positivity)] at h2
  have ha_pow : clockA ν r ^ (3 / 2 : ℝ) * (ν⁻¹ * clockA ν r ^ (-((5 + (0 : ℝ)) / 2))) =
      clockTheta ν r := by
    have h1 : clockA ν r ^ (3 / 2 : ℝ) * clockA ν r ^ (-((5 + (0 : ℝ)) / 2)) =
        (clockA ν r)⁻¹ := by
      rw [← Real.rpow_add ha0, ← Real.rpow_neg_one]
      congr 1; norm_num
    unfold clockTheta
    rw [mul_inv]
    linear_combination ν⁻¹ * h1
  have hd_sq' : β0 * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r = β0 * d ^ 2 := by
    rw [mul_div_assoc, hd_sq]
  rw [hdiff_eq, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
  calc clockA ν r ^ (3 / 2 : ℝ) * |tr.v r z k - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r z k|
      ≤ clockA ν r ^ (3 / 2 : ℝ) *
          (C0 * ν⁻¹ * clockA ν r ^ (-((5 + (0 : ℝ)) / 2)) *
            Real.exp (-(β0 * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν r))) :=
        mul_le_mul_of_nonneg_left (hcomp_le.trans hpt) (Real.rpow_nonneg ha0.le _)
    _ = C0 * clockTheta ν r * Real.exp (-(β0 * d ^ 2)) := by
        rw [hd_sq']
        linear_combination C0 * Real.exp (-(β0 * d ^ 2)) * ha_pow
    _ ≤ C0 * d ^ 2 * (2 / (β0 ^ 2 * d ^ 4)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hθ_le_d2 hC0.le) hexp_d4
          (Real.exp_pos _).le (by positivity)
    _ = (2 * C0 / β0 ^ 2) * (1 / d ^ 2) := by
        field_simp [hβ0.ne', hd_pos.ne']
    _ = (2 * C0 / β0 ^ 2) * ν ^ 3 / clockTheta ν r := by
        rw [hd2_inv]
        ring

/-- Unconditional `O(ν³ / clockTheta ν r)` weighted bound on `B0579.cell d(r)` for the rescaled
vorticity gradient error `movingTrainGradE tr r y k - B0579.pd k (Cyl.curl (Train.datum d(r))) y`. -/
theorem movingTrainGradE_sub_datum_bound (k_w : ℕ) :
    ∃ C_E ν_E : ℝ, 0 ≤ C_E ∧ 0 < ν_E ∧
      ∀ ν ∈ Ioc 0 ν_E,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          PartI.IsBUCTrain tr →
          ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r →
          ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)), ∀ k : Fin 2,
            let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
            B0579.jb y ^ k_w *
              |movingTrainGradE tr r y k -
                B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y| ≤
              C_E * ν ^ 3 / clockTheta ν r := by
  -- Use `vort_alg` at derivative order `j = 1` with `j' = 5` (`t' = a^(5/2) * d^2 ≤ x^(2 + 5)`)
  obtain ⟨Cm, bm, νm, hCm, hbm, hνm, hcm⟩ := PartI.trainComparison_proof 2 (by norm_num) 2
  obtain ⟨Cp, Np, νp, hνp, hpl⟩ := trainWeightedJetPoly_uncond (2 * k_w) 2
  obtain ⟨G, hG⟩ := vcWeightedJet (2 * k_w) 2
  set Qw : ℝ := |Cp| * 2 ^ Np + |G|
  set Mx : ℕ := 3 * Np + 2 * k_w
  set Kx : ℝ := 4 * 2 ^ (2 * k_w) * Qw * |Cm|
  set Ne : ℕ := 8 * k_w + Mx + 1 + (4 + 2 * 5)
  have hQw0 : 0 ≤ Qw := by positivity
  have hKf0 : 0 ≤ Kx * (Ne.factorial : ℝ) / bm ^ Ne := by
    dsimp [Kx]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hQw0) (abs_nonneg _))
      (Nat.cast_nonneg _)) (pow_nonneg hbm.le _)
  refine ⟨1 + Kx * (Ne.factorial : ℝ) / bm ^ Ne, min (min νm νp) 1, by linarith,
    lt_min (lt_min hνm hνp) one_pos, fun ν hν tr hbuc r hr hθ y hy k => ?_⟩
  intro d
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := le_trans hν.2 (min_le_right _ _)
  have hνm' : ν ≤ νm := le_trans hν.2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hνp' : ν ∈ Ioc 0 νp :=
    ⟨hν0, le_trans hν.2 (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  set c : ℝ := vortC ν
  set a : ℝ := clockA ν r
  set x : ℝ := ν⁻¹
  set z0 : ℝ × ℝ := (Real.sqrt a * y.1, Real.sqrt a * y.2)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν0 _
  have hc_eq : c = x ^ 2 := vort_c_eq hν0
  obtain ⟨ha1, ha2, hr2, hx1⟩ := vort_clock hν0 hν1 hr hθ
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hx0 : 0 ≤ x := le_trans zero_le_one hx1
  have hac2 : a ≤ c ^ 2 := by
    have hc2 : c ^ 2 = x ^ 4 := by rw [hc_eq]; ring
    have hxle : x ^ 1 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
    rw [pow_one] at hxle
    rw [hc2]
    exact le_trans ha2 hxle
  have hd_ge1 : 1 ≤ d := one_le_cellLen_of_theta hν0 hν1 hr hθ
  have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd_ge1
  set u : ℝ × ℝ → UnforcedLeray.Cyl.Vec2 :=
    fun z => tr.v r z - UnforcedLeray.Train.Vc ν c r z
  have hf_smooth : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr
  have hg_smooth : ContDiff ℝ ∞ (UnforcedLeray.Train.Vc ν c r) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc_pos ha0
  have hu_sm : ContDiff ℝ ∞ u := hf_smooth.sub hg_smooth
  set D : ℝ := ‖iteratedFDeriv ℝ 1 (UnforcedLeray.Cyl.curl u) z0‖
  set F : ℝ := ‖iteratedFDeriv ℝ 2 u z0‖
  set F1 : ℝ := ‖iteratedFDeriv ℝ 2 (tr.v r) z0‖
  set F2 : ℝ := ‖iteratedFDeriv ℝ 2 (UnforcedLeray.Train.Vc ν c r) z0‖
  have hD_le : D ≤ 2 * F := curlJetBound u hu_sm 1 z0
  have hF_tri : F ≤ F1 + F2 := by
    have hA' : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (tr.v r) :=
      hf_smooth.of_le (by simp)
    have hB' : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (UnforcedLeray.Train.Vc ν c r) :=
      hg_smooth.of_le (by simp)
    have hfn : iteratedFDeriv ℝ 2 u z0 =
        iteratedFDeriv ℝ 2 (tr.v r) z0 -
          iteratedFDeriv ℝ 2 (UnforcedLeray.Train.Vc ν c r) z0 :=
      iteratedFDeriv_sub_apply hA'.contDiffAt hB'.contDiffAt
    dsimp only [F, F1, F2]
    rw [hfn]
    exact norm_sub_le _ _
  -- Unweighted Gaussian-small sup bound for `F`
  have hF_sup : F ≤ |Cm| * x * Real.exp (-(bm * x)) := by
    have h := (hcm ν hν0 hνm' tr hbuc r hr hac2).2
    have hM0 : 0 ≤ Cm * x * a ^ (-((5 + ((2 : ℕ) : ℝ)) / 2)) * Real.exp (-(bm * c ^ 2 / a)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCm.le hx0) (Real.rpow_nonneg ha0.le _))
        (Real.exp_nonneg _)
    have hpt := UnforcedLeray.B0277.norm_le_of_supNormD_le hM0 h z0
    exact le_trans hpt (vort_E 2 hx1 ha1 ha2 hc_eq hbm)
  -- Polynomial weighted bound for `(1 + z0.2^2)^(2*k_w) * F`
  have hW1 : (1 + z0.2 ^ 2) ^ (2 * k_w) * F1 ≤ |Cp| * 2 ^ Np * x ^ Mx :=
    vort_T1 hx1 hr hr2 rfl (hpl ν hνp' tr hbuc r hr z0)
  have hq1 : (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (mul_pos (Real.rpow_pos_of_pos ha0 _) (pow_pos (Real.sqrt_pos.2 ha0) 2))]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow ha1 (by norm_num))
      (one_le_pow₀ ((Real.one_le_sqrt).mpr ha1))
  have hq0 : 0 ≤ (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ 2)⁻¹ :=
    inv_nonneg.2 (mul_nonneg (Real.rpow_nonneg ha0.le _) (pow_nonneg (Real.sqrt_nonneg _) 2))
  have hW2 : (1 + z0.2 ^ 2) ^ (2 * k_w) * F2 ≤ |G| * x ^ Mx :=
    vort_T2 hx1 ha1 ha2 (by omega) (sq_nonneg _) hq0 hq1 (norm_nonneg _)
      (hG ν c r hν0 hc_pos hr hac2 z0)
  have hW : (1 + z0.2 ^ 2) ^ (2 * k_w) * F ≤ Qw * x ^ Mx := by
    have hpos : 0 ≤ (1 + z0.2 ^ 2) ^ (2 * k_w) := pow_nonneg (by positivity) _
    calc (1 + z0.2 ^ 2) ^ (2 * k_w) * F
        ≤ (1 + z0.2 ^ 2) ^ (2 * k_w) * (F1 + F2) := mul_le_mul_of_nonneg_left hF_tri hpos
      _ = (1 + z0.2 ^ 2) ^ (2 * k_w) * F1 + (1 + z0.2 ^ 2) ^ (2 * k_w) * F2 := mul_add _ _ _
      _ ≤ |Cp| * 2 ^ Np * x ^ Mx + |G| * x ^ Mx := add_le_add hW1 hW2
      _ = Qw * x ^ Mx := by dsimp [Qw]; ring
  have hcell : -(c / Real.sqrt a / 2) ≤ y.1 ∧ y.1 < c / Real.sqrt a / 2 := hy.1
  have hjb_le : B0579.jb y ≤ (1 + c ^ 2) * (1 + z0.2 ^ 2) := by
    unfold B0579.jb
    exact vort_hjb ha1 rfl hcell
  -- Choose `t' = a ^ 2 * Real.sqrt a ^ 1 * d ^ 2` and verify `t' ≤ x ^ (2 + 5)`
  set t' : ℝ := (a ^ 2 * Real.sqrt a ^ 1) * d ^ 2
  have ht'_pos : 0 < t' := by positivity
  have ht'_le : t' ≤ x ^ (2 + 5) := by
    have hsa0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    have hsa1 : 1 ≤ Real.sqrt a := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt ha1
    have hsa_le : Real.sqrt a ≤ a :=
      calc Real.sqrt a ≤ Real.sqrt a * Real.sqrt a := le_mul_of_one_le_left hsa0 hsa1
        _ = a := Real.mul_self_sqrt ha0.le
    have hsq_le : Real.sqrt a ≤ x := hsa_le.trans ha2
    have ha_le : a ^ 2 * Real.sqrt a ^ 1 ≤ x ^ 3 := by
      rw [pow_one]
      calc a ^ 2 * Real.sqrt a ≤ x ^ 2 * x :=
            mul_le_mul (pow_le_pow_left₀ ha0.le ha2 2) hsq_le (Real.sqrt_nonneg _) (by positivity)
        _ = x ^ 3 := by ring
    have hd2_le : d ^ 2 ≤ x ^ 4 := by
      have hd2_eq : d ^ 2 = c ^ 2 / a := by
        dsimp [d, cellLen, c, vortC, a]
        rw [div_pow, Real.sq_sqrt ha0.le]
      have hc2_x4 : c ^ 2 = x ^ 4 := by rw [hc_eq]; ring
      rw [hd2_eq, hc2_x4]
      exact div_le_self (by positivity) ha1
    calc t' = (a ^ 2 * Real.sqrt a ^ 1) * d ^ 2 := rfl
      _ ≤ x ^ 3 * x ^ 4 := mul_le_mul ha_le hd2_le (by positivity) (by positivity)
      _ = x ^ (2 + 5) := by ring
  have halg := vort_alg expPolyAbsorb k_w 5 Mx Ne rfl hx1 hc_eq
    (by unfold B0579.jb; positivity) (norm_nonneg _) (norm_nonneg _)
    hjb_le (sq_nonneg _) hD_le hQw0 (abs_nonneg Cm) hbm hW hF_sup ht'_pos ht'_le
  -- Connect `|movingTrainGradE tr r y k - pd k (curl (datum d)) y|` to `a^(5/2) * D`
  have hgrad_le_D :
      |movingTrainGradE tr r y k -
          B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y| ≤
        (a ^ 2 * Real.sqrt a ^ 1) * D := by
    have hEc : UnforcedLeray.B0238.Ec tr r =
        fun z => UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c r) z +
          UnforcedLeray.Cyl.curl u z := by
      have hv : tr.v r = fun z => UnforcedLeray.Train.Vc ν c r z + u z := by
        funext z; dsimp [u]; abel
      show UnforcedLeray.Cyl.curl (tr.v r) = _
      conv_lhs => rw [hv]
      exact curl_add_vort hg_smooth hu_sm
    have hsub_curl : UnforcedLeray.Cyl.curl u =
        UnforcedLeray.B0238.Ec tr r -
          UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c r) := by
      funext z
      have h := congrFun hEc z
      change UnforcedLeray.Cyl.curl u z =
        UnforcedLeray.B0238.Ec tr r z - UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c r) z
      linarith
    have hpd_u : B0579.pd k (UnforcedLeray.Cyl.curl u) z0 =
        B0579.pd k (UnforcedLeray.B0238.Ec tr r) z0 -
          B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c r)) z0 := by
      unfold B0579.pd
      rw [hsub_curl]
      have hd1 : DifferentiableAt ℝ (UnforcedLeray.B0238.Ec tr r) z0 :=
        ((curl_contDiff_vort hf_smooth).differentiable (by simp)).differentiableAt
      have hd2 : DifferentiableAt ℝ (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν c r)) z0 :=
        ((curl_contDiff_vort hg_smooth).differentiable (by simp)).differentiableAt
      rw [fderiv_sub hd1 hd2, sub_apply]
    have hpow : a ^ ((5 : ℝ) / 2) = a ^ 2 * Real.sqrt a ^ 1 := by
      rw [pow_one, Real.sqrt_eq_rpow, ← Real.rpow_natCast a 2, ← Real.rpow_add ha0]
      norm_num
    have hdiff_eq : movingTrainGradE tr r y k -
        B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y =
        (a ^ 2 * Real.sqrt a ^ 1) * B0579.pd k (UnforcedLeray.Cyl.curl u) z0 := by
      rw [← hpow, hpd_u, mul_sub, movingTrainGradE_Vc_eq_pd_curl_datum hν0 hr y k]
      rfl
    have hpd_le_D : |B0579.pd k (UnforcedLeray.Cyl.curl u) z0| ≤ D := by
      dsimp [D]
      unfold B0579.pd
      rw [norm_iteratedFDeriv_one, ← Real.norm_eq_abs]
      have hdir : ‖B0579.dir k‖ ≤ 1 := by fin_cases k <;> simp [B0579.dir]
      calc ‖fderiv ℝ (UnforcedLeray.Cyl.curl u) z0 (B0579.dir k)‖
          ≤ ‖fderiv ℝ (UnforcedLeray.Cyl.curl u) z0‖ * ‖B0579.dir k‖ :=
            (fderiv ℝ (UnforcedLeray.Cyl.curl u) z0).le_opNorm _
        _ ≤ ‖fderiv ℝ (UnforcedLeray.Cyl.curl u) z0‖ * 1 :=
            mul_le_mul_of_nonneg_left hdir (norm_nonneg _)
        _ = ‖fderiv ℝ (UnforcedLeray.Cyl.curl u) z0‖ := mul_one _
    rw [hdiff_eq, abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hpd_le_D (by positivity)
  have hd2_inv : 1 / d ^ 2 = ν ^ 3 / clockTheta ν r :=
    inv_cellLen_sq_eq_nu_cube_div_theta hν0 hr
  have hjb_nn : 0 ≤ B0579.jb y ^ k_w := pow_nonneg (by unfold B0579.jb; positivity) _
  calc B0579.jb y ^ k_w *
        |movingTrainGradE tr r y k -
          B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y|
      ≤ B0579.jb y ^ k_w * ((a ^ 2 * Real.sqrt a ^ 1) * D) :=
        mul_le_mul_of_nonneg_left hgrad_le_D hjb_nn
    _ = (a ^ 2 * Real.sqrt a ^ 1) * (B0579.jb y ^ k_w * D) := by ring
    _ ≤ (a ^ 2 * Real.sqrt a ^ 1) *
          ((1 + Kx * (Ne.factorial : ℝ) / bm ^ Ne) * t'⁻¹) :=
        mul_le_mul_of_nonneg_left halg (by positivity)
    _ = (1 + Kx * (Ne.factorial : ℝ) / bm ^ Ne) * (1 / d ^ 2) := by
        dsimp [t']
        field_simp [ha0.ne', (Real.sqrt_pos.2 ha0).ne', hd_pos.ne']
    _ = (1 + Kx * (Ne.factorial : ℝ) / bm ^ Ne) * ν ^ 3 / clockTheta ν r := by
        rw [hd2_inv]
        ring

/-- Polynomial decay in `B0579.jb` bounds the `X_{m, d}` norm uniformly in `d`:
if `m ≥ 0` and `k_w = Nat.ceil m + 2`, then `B0579.jb x ^ k_w * ‖f x‖ ≤ M` on `B0579.cell d`
implies `xNorm d m f ≤ ENNReal.ofReal (M * K_p)`. -/
theorem xNorm_le_of_jb_pow {m : ℝ} (_hm : 0 ≤ m) :
    let k_w : ℕ := Nat.ceil m + 2
    ∃ K_p : ℝ, 0 ≤ K_p ∧
      ∀ (d M : ℝ) (f : ℝ × ℝ → ℂ), 0 ≤ M →
        (∀ x ∈ B0579.cell d, B0579.jb x ^ k_w * ‖f x‖ ≤ M) →
          xNorm d m f ≤ ENNReal.ofReal (M * K_p) := by
  intro k_w
  set J : ℝ × ℝ → ℝ := fun x => (1 + x.1 ^ 2)⁻¹ * (1 + x.2 ^ 2)⁻¹
  have hJ_int : Integrable J := integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq
  have hJ_nn : ∀ x, 0 ≤ J x := fun x => by dsimp [J]; positivity
  set I : ℝ := ∫ x, J x
  have hI_nn : 0 ≤ I := integral_nonneg hJ_nn
  refine ⟨Real.sqrt I, Real.sqrt_nonneg _, fun d M f hM hf => ?_⟩
  unfold xNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hjb_inv_le : ∀ x : ℝ × ℝ, (B0579.jb x) ^ (-(2 : ℝ)) ≤ J x := by
    intro x
    have hjb_pos : 0 < B0579.jb x := B0579.jb_pos x
    rw [Real.rpow_neg hjb_pos.le, Real.rpow_two]
    dsimp [J]
    rw [← mul_inv]
    refine inv_anti₀ (by positivity) ?_
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2, mul_nonneg (sq_nonneg x.1) (sq_nonneg x.2)]
  have hm_le : m - 2 * (k_w : ℝ) ≤ -2 := by
    have hc : m ≤ (Nat.ceil m : ℝ) := Nat.le_ceil m
    dsimp [k_w]
    push_cast
    linarith
  -- Integrate `‖f x‖ₑ ^ 2` against `B0579.cellMeasure d m` using `B0579.cellMeasure_ac`
  set G : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (M ^ 2 * (B0579.jb x) ^ (-2 * (k_w : ℝ)))
    with hG
  have hGm : Measurable G := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold B0579.jb
    refine Measurable.const_mul ?_ (M ^ 2)
    exact (Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))).measurable
  have hae : ∀ᵐ x ∂(B0579.cellMeasure d m), ‖f x‖ₑ ^ (2 : ℝ) ≤ G x := by
    refine B0579.cellMeasure_ac d m ?_
    refine (ae_restrict_iff' (measurableSet_Ico.prod MeasurableSet.univ)).2
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : x ∈ B0579.cell d := hx
    have hjb_pos : 0 < B0579.jb x := B0579.jb_pos x
    have hfx : ‖f x‖ ≤ M * (B0579.jb x) ^ (-(k_w : ℝ)) := by
      rw [Real.rpow_neg hjb_pos.le, Real.rpow_natCast, ← div_eq_mul_inv,
        le_div_iff₀ (pow_pos hjb_pos k_w), mul_comm]
      exact hf x hx'
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_two]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hfx 2
    rw [mul_pow, ← Real.rpow_natCast ((B0579.jb x) ^ (-(k_w : ℝ))) 2,
      ← Real.rpow_mul hjb_pos.le] at h1
    refine h1.trans (le_of_eq ?_)
    congr 2; ring
  have hint_le : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂B0579.cellMeasure d m) ≤
      ENNReal.ofReal (M ^ 2 * I) := by
    calc ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure d m)
        ≤ ∫⁻ x, G x ∂(B0579.cellMeasure d m) := lintegral_mono_ae hae
      _ = ∫⁻ x, (B0579.density m x : ℝ≥0∞) * G x ∂(volume.restrict (B0579.cell d)) := by
          unfold B0579.cellMeasure
          exact lintegral_withDensity_eq_lintegral_mul _
            (B0579.measurable_density m).coe_nnreal_ennreal hGm
      _ ≤ ∫⁻ x, (B0579.density m x : ℝ≥0∞) * G x :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ ≤ ∫⁻ x, ENNReal.ofReal (M ^ 2 * J x) := by
          refine lintegral_mono fun x => ?_
          have hdens : (B0579.density m x : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ m) := by
            unfold B0579.density; rfl
          have hjb1 : 1 ≤ B0579.jb x := by unfold B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
          have hjb_pos : 0 < B0579.jb x := lt_of_lt_of_le zero_lt_one hjb1
          rw [hdens, hG, ← ENNReal.ofReal_mul (Real.rpow_nonneg hjb_pos.le _)]
          refine ENNReal.ofReal_le_ofReal ?_
          calc B0579.jb x ^ m * (M ^ 2 * B0579.jb x ^ (-2 * (k_w : ℝ)))
              = M ^ 2 * (B0579.jb x ^ (m - 2 * (k_w : ℝ))) := by
                rw [mul_left_comm, ← Real.rpow_add hjb_pos]
                congr 2; ring
            _ ≤ M ^ 2 * (B0579.jb x ^ (-(2 : ℝ))) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hjb1 hm_le) (sq_nonneg M)
            _ ≤ M ^ 2 * J x :=
                mul_le_mul_of_nonneg_left (hjb_inv_le x) (sq_nonneg M)
      _ = ENNReal.ofReal (M ^ 2 * I) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hJ_int.const_mul (M ^ 2))
            (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg M) (hJ_nn x)),
            integral_const_mul]
  calc (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂B0579.cellMeasure d m) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (M ^ 2 * I)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hint_le (by norm_num)
    _ = ENNReal.ofReal ((M ^ 2 * I) ^ (1 / (2 : ℝ))) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ = ENNReal.ofReal (M * Real.sqrt I) := by
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]

/-- **Unconditional `O(ν³ / clockTheta ν r)` bound in `X_{m, d(r)}` for the BUC train comparison
part of `movEulerRes`**:
`xNorm d(r) m (fun y => movL tr r (perE κ d(r) j) y - movLGauss d(r) (perE κ d(r) j) y) ≤
  ENNReal.ofReal (C_tr * ν ^ 3 / clockTheta ν r)`. -/
theorem xNorm_movL_sub_movLGauss_le {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {m : ℝ} (hm : 8 < m) :
    ∃ C_tr ν_tr : ℝ, 0 ≤ C_tr ∧ 0 < ν_tr ∧
      ∀ ν ∈ Ioc 0 ν_tr,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          PartI.IsBUCTrain tr →
          ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r → ∀ j : Fin 2,
            let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
            xNorm d m (fun y => movL tr r (perE κ d j) y - movLGauss d (perE κ d j) y) ≤
              ENNReal.ofReal (C_tr * ν ^ 3 / clockTheta ν r) := by
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨M_E, hME_pos, hME⟩ := perE_and_pdCx_gauss_bounds hκ
  obtain ⟨C_vel, hCvel_pos, hvel⟩ := kerVelCx_perE_bound hκ
  obtain ⟨C_V, ν_V, hCV_pos, hνV_pos, hV_bd⟩ := movingTrainV_sub_datum_bound
  set k_w : ℕ := Nat.ceil m + 2
  obtain ⟨C_E, ν_E, hCE_pos, hνE_pos, hE_bd⟩ := movingTrainGradE_sub_datum_bound k_w
  obtain ⟨K_g, hKg_pos, hKg⟩ := xNorm_le_of_gauss hm0
  obtain ⟨K_p, hKp_pos, hKp⟩ := xNorm_le_of_jb_pow hm0
  set C_tr : ℝ := 2 * C_V * M_E * K_g + 2 * C_vel * C_E * K_p
  refine ⟨C_tr, min 1 (min ν_V ν_E), by positivity,
    lt_min zero_lt_one (lt_min hνV_pos hνE_pos), fun ν hν tr hbuc r hr hθ j => ?_⟩
  intro d
  have hν_pos : 0 < ν := hν.1
  have hν_le1 : ν ≤ 1 := hν.2.trans (min_le_left _ _)
  have hν_V : ν ∈ Ioc 0 ν_V :=
    ⟨hν_pos, hν.2.trans (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hν_E : ν ∈ Ioc 0 ν_E :=
    ⟨hν_pos, hν.2.trans (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hd_ge1 : 1 ≤ d := one_le_cellLen_of_theta hν_pos hν_le1 hr hθ
  have hθ_pos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ
  set q : ℝ := ν ^ 3 / clockTheta ν r
  have hq_nn : 0 ≤ q := by dsimp [q]; positivity
  -- Split `movL - movLGauss` into transport velocity difference `f_V` and strain difference `f_E`
  set f_V : ℝ × ℝ → ℂ := fun y =>
    -((((movingTrainV tr r y 0 - UnforcedLeray.Train.datum d y 0 : ℝ) : ℂ) *
          pdCx 0 (perE κ d j) y) +
        (((movingTrainV tr r y 1 - UnforcedLeray.Train.datum d y 1 : ℝ) : ℂ) *
          pdCx 1 (perE κ d j) y))
  set f_E : ℝ × ℝ → ℂ := fun y =>
    -(kerVelCx d (perE κ d j) y 0 *
          (((movingTrainGradE tr r y 0 -
            B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ)) +
        kerVelCx d (perE κ d j) y 1 *
          (((movingTrainGradE tr r y 1 -
            B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ)))
  have hsplit : (fun y => movL tr r (perE κ d j) y - movLGauss d (perE κ d j) y) = f_V + f_E := by
    funext y
    dsimp [movL, movLGauss, f_V, f_E]
    push_cast
    ring
  -- Bound `xNorm d m f_V` via `xNorm_le_of_gauss`
  have hfV_norm : xNorm d m f_V ≤ ENNReal.ofReal ((2 * C_V * M_E * q) * K_g) := by
    refine hKg d (2 * C_V * M_E * q) f_V (by positivity) (fun y hy => ?_)
    have hV0 := hV_bd ν hν_V tr hbuc r hr hθ y 0
    have hV1 := hV_bd ν hν_V tr hbuc r hr hθ y 1
    have hpd0 := (hME d hd_ge1 j).2.2 0 y hy
    have hpd1 := (hME d hd_ge1 j).2.2 1 y hy
    dsimp [f_V]
    rw [norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have h0 : |movingTrainV tr r y 0 - UnforcedLeray.Train.datum d y 0| *
        ‖pdCx 0 (perE κ d j) y‖ ≤
        (C_V * q) * (M_E * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) := by
      rw [show C_V * q = C_V * ν ^ 3 / clockTheta ν r by dsimp [q]; ring]
      exact mul_le_mul hV0 hpd0 (norm_nonneg _) (by positivity)
    have h1 : |movingTrainV tr r y 1 - UnforcedLeray.Train.datum d y 1| *
        ‖pdCx 1 (perE κ d j) y‖ ≤
        (C_V * q) * (M_E * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 16)) := by
      rw [show C_V * q = C_V * ν ^ 3 / clockTheta ν r by dsimp [q]; ring]
      exact mul_le_mul hV1 hpd1 (norm_nonneg _) (by positivity)
    linarith
  -- Bound `xNorm d m f_E` via `xNorm_le_of_jb_pow`
  have hfE_norm : xNorm d m f_E ≤ ENNReal.ofReal ((2 * C_vel * C_E * q) * K_p) := by
    refine hKp d (2 * C_vel * C_E * q) f_E (by positivity) (fun y hy => ?_)
    have hE0 := hE_bd ν hν_E tr hbuc r hr hθ y hy 0
    have hE1 := hE_bd ν hν_E tr hbuc r hr hθ y hy 1
    have hK0 := hvel d hd_ge1 j 0 y
    have hK1 := hvel d hd_ge1 j 1 y
    have hjb_nn : 0 ≤ B0579.jb y ^ k_w := pow_nonneg (by unfold B0579.jb; positivity) _
    dsimp [f_E]
    rw [norm_neg]
    have htri : B0579.jb y ^ k_w * ‖kerVelCx d (perE κ d j) y 0 *
          ((movingTrainGradE tr r y 0 -
            B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ) +
        kerVelCx d (perE κ d j) y 1 *
          ((movingTrainGradE tr r y 1 -
            B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ)‖ ≤
        ‖kerVelCx d (perE κ d j) y 0‖ *
          (B0579.jb y ^ k_w * |movingTrainGradE tr r y 0 -
            B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y|) +
        ‖kerVelCx d (perE κ d j) y 1‖ *
          (B0579.jb y ^ k_w * |movingTrainGradE tr r y 1 -
            B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y|) := by
      have h := mul_le_mul_of_nonneg_left (norm_add_le
        (kerVelCx d (perE κ d j) y 0 *
          ((movingTrainGradE tr r y 0 -
            B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ))
        (kerVelCx d (perE κ d j) y 1 *
          ((movingTrainGradE tr r y 1 -
            B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ))) hjb_nn
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs] at h
      linarith
    have h0 : ‖kerVelCx d (perE κ d j) y 0‖ *
        (B0579.jb y ^ k_w * |movingTrainGradE tr r y 0 -
          B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y|) ≤
        C_vel * (C_E * q) := by
      rw [show C_E * q = C_E * ν ^ 3 / clockTheta ν r by dsimp [q]; ring]
      exact mul_le_mul hK0 hE0 (by positivity) hCvel_pos
    have h1 : ‖kerVelCx d (perE κ d j) y 1‖ *
        (B0579.jb y ^ k_w * |movingTrainGradE tr r y 1 -
          B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y|) ≤
        C_vel * (C_E * q) := by
      rw [show C_E * q = C_E * ν ^ 3 / clockTheta ν r by dsimp [q]; ring]
      exact mul_le_mul hK1 hE1 (by positivity) hCvel_pos
    linarith
  -- Measurability of `f_V` for `eLpNorm_add_le`
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν_pos.le hr)
  have hd0 : 0 < d := div_pos (Real.rpow_pos_of_pos hν_pos _) (Real.sqrt_pos.2 ha0)
  have hfV_cont : Continuous f_V := by
    have hc_V0 := continuous_movingTrainV tr hr 0
    have hc_V1 := continuous_movingTrainV tr hr 1
    have hc_D0 : Continuous (fun y => UnforcedLeray.Train.datum d y 0) :=
      (PiLp.continuous_apply 2 _ 0).comp (UnforcedLeray.Train.datum_contDiff hd0.ne').continuous
    have hc_D1 : Continuous (fun y => UnforcedLeray.Train.datum d y 1) :=
      (PiLp.continuous_apply 2 _ 1).comp (UnforcedLeray.Train.datum_contDiff hd0.ne').continuous
    have hc_pd0 := continuous_pdCx_perE hκ hd0 j 0
    have hc_pd1 := continuous_pdCx_perE hκ hd0 j 1
    exact (((Complex.continuous_ofReal.comp (hc_V0.sub hc_D0)).mul hc_pd0).add
      ((Complex.continuous_ofReal.comp (hc_V1.sub hc_D1)).mul hc_pd1)).neg
  have hfE_sm : StronglyMeasurable f_E := by
    have hE_sm : StronglyMeasurable (perE κ d j) := (continuous_perE hκ hd0 j).stronglyMeasurable
    have hK0 := stronglyMeasurable_kerVelCx d hE_sm 0
    have hK1 := stronglyMeasurable_kerVelCx d hE_sm 1
    have hG0 := continuous_movingTrainGradE tr hr 0
    have hG1 := continuous_movingTrainGradE tr hr 1
    have hcurl_sm : ContDiff ℝ ∞ (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) :=
      dcs_contDiff_curl (UnforcedLeray.Train.datum_contDiff hd0.ne')
    have hD0 : Continuous (B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d))) :=
      ((hcurl_sm.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply contDiff_const).continuous
    have hD1 : Continuous (B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d))) :=
      ((hcurl_sm.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply contDiff_const).continuous
    have hdiff0 : StronglyMeasurable (fun y =>
        ((movingTrainGradE tr r y 0 -
          B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp (hG0.sub hD0)).stronglyMeasurable
    have hdiff1 : StronglyMeasurable (fun y =>
        ((movingTrainGradE tr r y 1 -
          B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp (hG1.sub hD1)).stronglyMeasurable
    dsimp [f_E]
    exact ((hK0.mul hdiff0).add (hK1.mul hdiff1)).neg
  rw [hsplit]
  unfold xNorm
  calc eLpNorm (f_V + f_E) 2 (B0579.cellMeasure d m)
      ≤ eLpNorm f_V 2 (B0579.cellMeasure d m) + eLpNorm f_E 2 (B0579.cellMeasure d m) :=
        eLpNorm_add_le hfV_cont.aestronglyMeasurable hfE_sm.aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal ((2 * C_V * M_E * q) * K_g) +
          ENNReal.ofReal ((2 * C_vel * C_E * q) * K_p) :=
        add_le_add hfV_norm hfE_norm
    _ = ENNReal.ofReal (C_tr * ν ^ 3 / clockTheta ν r) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        dsimp [C_tr, q]
        ring

end EulerErrorSub

open EulerErrorSub OscillatorForceSub ComplCouplingSub DirectEulerSub

/-! ## 6. Conditional assembly of `ComplModeForceEulerError` (`PartIII-a:T21/c3/3/3`) -/

/-- **Conditional assembly of `ComplModeForceEulerError` (`PartIII-a:T21/c3/3/3`, SP 2866-2888,
2991-2995)** from the Gaussian-cylinder seed-eigenmode residual bound `MovEulerGaussSubBound κ`,
using our unconditional proofs of:
* `planar_eigenvalue_eq_seed` (`modeEigen P j = seedModeEigen lam j`),
* `aesm_movEulerRes` (`AEStronglyMeasurable (movEulerRes κ P tr r j)`), and
* `xNorm_movL_sub_movLGauss_le` (`O(ν³ / clockTheta ν r)` BUC train comparison in `X_{m, d(r)}`). -/
theorem complModeForceEulerError_of (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels)
    (hG : MovEulerGaussSubBound κ) :
    UnforcedLeray.Short.IIIa.ComplModeForceEulerError κ := by
  intro hκ P hP m hm
  have hκ_copy := hκ
  obtain ⟨lam, h, hh, ℓ, hIS, he0, he1, -⟩ := hκ_copy
  obtain ⟨C_tr, ν_tr, hCtr_pos, hνtr_pos, htr_bd⟩ := xNorm_movL_sub_movLGauss_le hκ hm
  obtain ⟨C_G, D_G, hCG_pos, hDG_ge1, hG_bd⟩ := hG lam h hh ℓ hIS he0 he1 m hm
  have hDG_nn : 0 ≤ D_G := by linarith
  refine ⟨C_tr + C_G, 1, by positivity, le_rfl, fun b hb => ?_⟩
  refine ⟨min ν_tr (1 / (D_G + 1) ^ 2), lt_min hνtr_pos (by positivity),
    fun ν hν tr hbuc r hr hbr j => ?_⟩
  have hν_pos : 0 < ν := hν.1
  have hν_tr : ν ∈ Ioc 0 ν_tr := ⟨hν_pos, hν.2.trans (min_le_left _ _)⟩
  have hν_DG : ν ≤ 1 / (D_G + 1) ^ 2 := hν.2.trans (min_le_right _ _)
  have hθ : 1 ≤ clockTheta ν r := hb.trans hbr
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hd_DG : D_G ≤ d := cellLen_ge hDG_nn hν_pos hν_DG hb hr hbr
  refine ⟨aesm_movEulerRes hκ P hν_pos tr hr m j, ?_⟩
  -- Decompose `movEulerRes κ P tr r j` into the BUC train defect plus the Gaussian-cylinder defect
  have hdecomp : movEulerRes κ P tr r j =
      (fun y => movL tr r (perE κ d j) y - movLGauss d (perE κ d j) y) +
        movEulerResGauss κ lam d j := by
    funext y
    exact movEulerRes_eq_trainDiff_add_gauss κ P hP hIS tr r j y
  have h1 := htr_bd ν hν_tr tr hbuc r hr hθ j
  have h2 : xNorm d m (movEulerResGauss κ lam d j) ≤
      ENNReal.ofReal (C_G * ν ^ 3 / clockTheta ν r) := by
    refine (hG_bd d hd_DG j).trans (le_of_eq ?_)
    congr 1
    have hd2_inv : 1 / d ^ 2 = ν ^ 3 / clockTheta ν r :=
      inv_cellLen_sq_eq_nu_cube_div_theta hν_pos hr
    calc C_G / d ^ 2 = C_G * (1 / d ^ 2) := by ring
      _ = C_G * (ν ^ 3 / clockTheta ν r) := by rw [hd2_inv]
      _ = C_G * ν ^ 3 / clockTheta ν r := by ring
  -- Measurability of the Gaussian-cylinder defect for `eLpNorm_add_le`
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν_pos.le hr)
  have hd0 : 0 < d := div_pos (Real.rpow_pos_of_pos hν_pos _) (Real.sqrt_pos.2 ha0)
  have hE_sm : StronglyMeasurable (perE κ d j) := (continuous_perE hκ hd0 j).stronglyMeasurable
  have hpd0_sm : StronglyMeasurable (pdCx 0 (perE κ d j)) :=
    (continuous_pdCx_perE hκ hd0 j 0).stronglyMeasurable
  have hpd1_sm : StronglyMeasurable (pdCx 1 (perE κ d j)) :=
    (continuous_pdCx_perE hκ hd0 j 1).stronglyMeasurable
  have hK0_sm := stronglyMeasurable_kerVelCx d hE_sm 0
  have hK1_sm := stronglyMeasurable_kerVelCx d hE_sm 1
  have hD0_sm : StronglyMeasurable (fun y => ((UnforcedLeray.Train.datum d y 0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      ((PiLp.continuous_apply 2 _ 0).comp
        (UnforcedLeray.Train.datum_contDiff hd0.ne').continuous)).stronglyMeasurable
  have hD1_sm : StronglyMeasurable (fun y => ((UnforcedLeray.Train.datum d y 1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      ((PiLp.continuous_apply 2 _ 1).comp
        (UnforcedLeray.Train.datum_contDiff hd0.ne').continuous)).stronglyMeasurable
  have hcurl_sm : ContDiff ℝ ∞ (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) :=
    dcs_contDiff_curl (UnforcedLeray.Train.datum_contDiff hd0.ne')
  have hG0_sm : StronglyMeasurable (fun y =>
      ((B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((hcurl_sm.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply
        contDiff_const).continuous)).stronglyMeasurable
  have hG1_sm : StronglyMeasurable (fun y =>
      ((B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((hcurl_sm.fderiv_right (m := (1 : ℕ)) (by simp)).clm_apply
        contDiff_const).continuous)).stronglyMeasurable
  have hLG_sm : StronglyMeasurable (movLGauss d (perE κ d j)) := by
    unfold movLGauss
    exact ((hD0_sm.mul hpd0_sm).add (hD1_sm.mul hpd1_sm)).neg.sub
      ((hK0_sm.mul hG0_sm).add (hK1_sm.mul hG1_sm))
  have hResG_sm : StronglyMeasurable (movEulerResGauss κ lam d j) := by
    unfold movEulerResGauss
    exact hLG_sm.sub (stronglyMeasurable_const.mul hE_sm)
  have hL_sm : StronglyMeasurable (movL tr r (perE κ d j)) := by
    unfold movL
    have hV0 := (Complex.continuous_ofReal.comp (continuous_movingTrainV tr hr 0)).stronglyMeasurable
    have hV1 := (Complex.continuous_ofReal.comp (continuous_movingTrainV tr hr 1)).stronglyMeasurable
    have hGE0 := (Complex.continuous_ofReal.comp (continuous_movingTrainGradE tr hr 0)).stronglyMeasurable
    have hGE1 := (Complex.continuous_ofReal.comp (continuous_movingTrainGradE tr hr 1)).stronglyMeasurable
    exact ((hV0.mul hpd0_sm).add (hV1.mul hpd1_sm)).neg.sub
      ((hK0_sm.mul hGE0).add (hK1_sm.mul hGE1))
  have hdiff_sm : StronglyMeasurable
      (fun y => movL tr r (perE κ d j) y - movLGauss d (perE κ d j) y) :=
    hL_sm.sub hLG_sm
  rw [hdecomp]
  unfold xNorm
  have hθ_pos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ
  calc eLpNorm ((fun y => movL tr r (perE κ d j) y - movLGauss d (perE κ d j) y) +
          movEulerResGauss κ lam d j) 2 (B0579.cellMeasure d m)
      ≤ eLpNorm (fun y => movL tr r (perE κ d j) y - movLGauss d (perE κ d j) y) 2
          (B0579.cellMeasure d m) +
        eLpNorm (movEulerResGauss κ lam d j) 2 (B0579.cellMeasure d m) :=
        eLpNorm_add_le hdiff_sm.aestronglyMeasurable hResG_sm.aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal (C_tr * ν ^ 3 / clockTheta ν r) +
          ENNReal.ofReal (C_G * ν ^ 3 / clockTheta ν r) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal ((C_tr + C_G) * ν ^ 3 / clockTheta ν r) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **Conditional assembly of `ComplModeForceEulerError` from `SeedPlanarPointwiseEigen` and
`MovEulerGaussTailBound`** (`PartIII-a:T21/c3/3/3`). -/
theorem complModeForceEulerError_of_leaves (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels)
    (hEig : SeedPlanarPointwiseEigen κ) (hTail : MovEulerGaussTailBound κ) :
    UnforcedLeray.Short.IIIa.ComplModeForceEulerError κ :=
  complModeForceEulerError_of κ (movEulerGaussSubBound_of κ hEig hTail)

end UnforcedLeray.Short.IIIa

