import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.FlowMeas
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c1_b.FrameCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.RateSplit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.Transposition
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CommVanish
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.TrainWeightedJetPoly

/-!
# Part III-a, task `PartIII-a:T21/c5/1` decomposition (`Sub/PartIII-a_T21_c5_1.lean`, SP 2898-2918, 2991-3000)

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2918 and
2991-3000 (`eq:short-causal-moving-eq`, `eq:short-causal-ampl-moving`).

## Mathematical structure and proved reductions

For the periodized moving frame `F = periodizedFrame κ ν m b K hν.1 hF` built from a Part I seed
kernel `κ` (`IsSeedKernels κ`) and a planar reference `P` (`IsPlanarReference P`):

1. **Normalised physical dual test function `normPhysFrameLam` and its operator identities (proved here)**:
   * `normPhysFrameLam κ P ν t r i x = (clockNC P ν t r i)⁻¹ * physFrameLam κ ν r i x` scales the
     physical dual row `physFrameLam κ ν r i` by the inverse complex normaliser `(clockNC P ν t r i)⁻¹`.
   * `normAmpl_eq_ladPair`: by `FrameAmplSub.ampl_eq_phys_pairing`, the normalised amplitude
     `normAmpl F P t w r i` equals the physical cell pairing
     `ladPair (ν ^ (-2)) w (fun r' => normPhysFrameLam κ P ν t r' i) r`.
   * `hasDerivAt_normPhysFrameLam` and `ladDt_normPhysFrameLam`: combines the age derivative of
     `(clockNC P ν t · i)⁻¹` (`FrameAmplSub.hasDerivAt_clockNC_inv`) with the time derivative of
     `physFrameLam` to show that
     `ladDt (normPhysFrameLam κ P ν t · i) r x = (clockNC P ν t r i)⁻¹ * ladDt (physFrameLam κ ν · i) r x - a(r)⁻² * modeDiag P ν r i * normPhysFrameLam κ P ν t r i x`.
   * `kerAdj_normPhysFrameLam`: pulls the `x`-constant factor `(clockNC P ν t r i)⁻¹` out of the
     periodic Biot-Savart adjoint `kerAdj`.
   * `normPhysLamDual_pairing_eq_amplResidual`: proves that the physical cell pairing of `w r` with
     `normPhysLamDual κ P tr t r i` equals
     `a(r)⁻² * ((clockNC P ν t r i)⁻¹ * amplResidual κ P F tr w r i)`, where the `modeDiag P ν r i`
     term from `d/dr (clockNC P ν t r i)⁻¹` cancels the diagonal part of `movH0`.
   * `continuousOn_normAmpl`: combines `FlowMeas.continuousOn_ampl` and
     `FrameAmplSub.continuousOn_clockNC_inv` to prove continuity of `r ↦ normAmpl F P t w r i` on
     `Ioc t s`.

2. **Unconditional linear decomposition of `movH0` across `movingW = ∑ ampl_j E_j + compl` (proved here)**:
   * `integrableOn_movingPhi_physLamDual_mul` and `movH0_movingW_decomp_of_memLp`: using
     `ComplCouplingSub.xNorm_pairing_bound`, `ComplCouplingSub.integrableOn_perLam_mul`,
     `ComplCouplingSub.memLp_movingW`, and `ComplCouplingSub.memLp_frame_E`, proves that whenever
     `movLamDualHeat κ ν r i` and `movLamDualEulerSub κ lam tr r i` belong to
     `MemLp · 2 (B0579.cellMeasure d(r) (-m))`, the pairings of `movingPhi(physLamDual)` with
     `movingW ν w r` and `F.E r j` are integrable on `movingCell`, discharging the third conjunct
     of `AmplWeakFTC` via `FrameAmplSub.movH0_movingW_decomp`.

3. **Analytical leaf for the cutoff weak-flow limit (`NormAmplCutFTC`, `PartIII-a:T21/c5/1/1`)**:
   * `NormAmplCutFTC κ`: given `MovLamDualHeatBound κ` and `MovLamDualEulerSubBound κ`, testing
     `IsLinearisedFlow` against the cutoff normalised dual row
     `ladCutPhi (normPhysFrameLam κ P ν t · i) R` and passing `R → ∞` via `ladProductRule`,
     `ladRateSplit`, `ladTransposition`, `ladCommVanish`, and `ladCutLimit` yields `AEMeasurable`
     of `amplResidual` on `Ioc t s` and the Bochner integral identity for
     `normAmpl F P t w s i - normAmpl F P t w t i`.
   * `amplWeakFTC_of`: assembles `AmplWeakFTC κ` from `MovLamDualHeatBound κ`,
     `MovLamDualEulerSubBound κ`, and `NormAmplCutFTC κ` with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## Normalised physical dual test function and normalised dual generator -/

/-- Normalised physical-variable dual test function
`φ̃_i(r, x) = (clockNC P ν t r i)⁻¹ * physFrameLam κ ν r i x` (SP 2898-2918, 2998-3000). -/
def normPhysFrameLam (κ : PlanarFrameKernels) (P : PlanarData) (ν t r : ℝ) (i : Fin 2)
    (x : ℝ × ℝ) : ℂ :=
  (clockNC P ν t r i)⁻¹ * physFrameLam κ ν r i x

/-- Normalised physical-variable formal adjoint generator applied to `normPhysFrameLam`:
`(clockNC P ν t r i)⁻¹ * physLamDual κ tr r i x - a(r)⁻² * modeDiag P ν r i * normPhysFrameLam κ P ν t r i x`
(SP 2905-2918, 2998-3000). -/
def normPhysLamDual (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t r : ℝ) (i : Fin 2)
    (x : ℝ × ℝ) : ℂ :=
  (clockNC P ν t r i)⁻¹ * physLamDual κ tr r i x -
    (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * modeDiag P ν r i *
      normPhysFrameLam κ P ν t r i x

/-! ## Analytical leaf for the cutoff weak-flow limit -/

/-- **Leaf 1 (`PartIII-a:T21/c5/1/1`, `NormAmplCutFTC`, SP 2898-2918, 2998-3000)**:
Given `MovLamDualHeatBound κ` and `MovLamDualEulerSubBound κ`, testing `IsLinearisedFlow` against
the transverse cutoff `ladCutPhi (normPhysFrameLam κ P ν t · i) R` and passing `R → ∞` yields
`AEMeasurable` of `amplResidual` on `Ioc t s` and the Bochner integral identity for
`normAmpl F P t w s i - normAmpl F P t w t i`.
Composed by task `PartIII-a:T21/c5/1` via `amplWeakFTC_of`. -/
def NormAmplCutFTC (κ : PlanarFrameKernels) : Prop :=
  MovLamDualHeatBound κ →
  MovLamDualEulerSubBound κ →
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∃ b_c : ℝ, 1 ≤ b_c ∧
    ∀ b : ℝ, b_c ≤ b →
      ∃ ν_c : ℝ, 0 < ν_c ∧
        ∀ ν : ℝ, (hν : ν ∈ Ioc 0 ν_c) → ∀ (hF : PerFrameFacts κ ν m b K),
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
        ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
        ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
          HasZeroCirculation (ν ^ (-2 : ℝ)) f →
        let F := periodizedFrame κ ν m b K hν.1 hF
        (∀ i : Fin 2,
          AEMeasurable (fun r => amplResidual κ P F tr w r i) (volume.restrict (Ioc t s))) ∧
        (∀ i : Fin 2,
          normAmpl F P t w s i - normAmpl F P t w t i =
            ∫ r in Ioc t s,
              (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
                ((clockNC P ν t r i)⁻¹ * amplResidual κ P F tr w r i))

namespace WeakFTCSub

open ComplCouplingSub

/-! ## Physical pairing and operator identities for `normPhysFrameLam` -/

/-- The normalised mode amplitude `normAmpl F P t w r i` equals the physical cell pairing
`ladPair (ν ^ (-2)) w (fun r' => normPhysFrameLam κ P ν t r' i) r`. -/
theorem normAmpl_eq_ladPair (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K t r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (hF : PerFrameFacts κ ν m b K)
    (w : ℝ → ℝ × ℝ → ℂ) (i : Fin 2) :
    normAmpl (periodizedFrame κ ν m b K hν hF) P t w r i =
      ladPair (ν ^ (-2 : ℝ)) w (fun r' => normPhysFrameLam κ P ν t r' i) r := by
  unfold normAmpl ladPair normPhysFrameLam
  rw [FrameAmplSub.ampl_eq_phys_pairing κ hν hr hF w i, ← integral_const_mul]
  congr 1
  funext x
  ring

/-- Product rule for the age derivative of `normPhysFrameLam κ P ν t · i x`. -/
theorem hasDerivAt_normPhysFrameLam (κ : PlanarFrameKernels) (P : PlanarData)
    {ν t r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r) (i : Fin 2) (x : ℝ × ℝ)
    {dφ : ℂ} (hdφ : HasDerivAt (fun r' => physFrameLam κ ν r' i x) dφ r) :
    HasDerivAt (fun r' => normPhysFrameLam κ P ν t r' i x)
      ((clockNC P ν t r i)⁻¹ * dφ -
        (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * modeDiag P ν r i *
          normPhysFrameLam κ P ν t r i x) r := by
  have hNC := FrameAmplSub.hasDerivAt_clockNC_inv P hν ht hr i
  have hmul := hNC.mul hdφ
  refine hmul.congr_deriv ?_
  unfold normPhysFrameLam
  ring

/-- Classical right age derivative `ladDt` of `normPhysFrameLam κ P ν t · i x` whenever
`r' ↦ physFrameLam κ ν r' i x` is differentiable at `r`. -/
theorem ladDt_normPhysFrameLam (κ : PlanarFrameKernels) (P : PlanarData)
    {ν t r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r) (i : Fin 2) (x : ℝ × ℝ)
    (hdφ : DifferentiableAt ℝ (fun r' => physFrameLam κ ν r' i x) r) :
    ladDt (fun r' x' => normPhysFrameLam κ P ν t r' i x') r x =
      (clockNC P ν t r i)⁻¹ * ladDt (fun r' x' => physFrameLam κ ν r' i x') r x -
        (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * modeDiag P ν r i *
          normPhysFrameLam κ P ν t r i x := by
  have h1 : ladDt (fun r' x' => physFrameLam κ ν r' i x') r x =
      deriv (fun r' => physFrameLam κ ν r' i x) r :=
    ladDt_eq_of_hasDerivAt hdφ.hasDerivAt
  rw [h1]
  exact ladDt_eq_of_hasDerivAt
    (hasDerivAt_normPhysFrameLam κ P hν ht hr i x hdφ.hasDerivAt)

/-- Pulling the `x`-constant factor `(clockNC P ν t r i)⁻¹` out of `kerAdj`. -/
theorem kerAdj_normPhysFrameLam (κ : PlanarFrameKernels) (P : PlanarData)
    {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t r : ℝ) (i : Fin 2) (x : ℝ × ℝ) :
    kerAdj (ν ^ (-2 : ℝ)) (fun k y => normPhysFrameLam κ P ν t r i y *
      (B0579.pd k (UnforcedLeray.B0238.Ec tr r) y : ℂ)) x =
    (clockNC P ν t r i)⁻¹ *
      kerAdj (ν ^ (-2 : ℝ)) (fun k y => physFrameLam κ ν r i y *
        (B0579.pd k (UnforcedLeray.B0238.Ec tr r) y : ℂ)) x := by
  unfold kerAdj normPhysFrameLam
  rw [← integral_const_mul]
  congr 1
  funext y
  simp only [Fin.sum_univ_two]
  ring

/-- Physical cell pairing of `w r` with `normPhysLamDual κ P tr t r i` equals
`a(r)⁻² * ((clockNC P ν t r i)⁻¹ * amplResidual κ P F tr w r i)`: the normaliser derivative cancels
`modeDiag P ν r i * ampl F w r i`. -/
theorem normPhysLamDual_pairing_eq_amplResidual (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K t r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (w : ℝ → ℝ × ℝ → ℂ) (i : Fin 2)
    (hIntDual : IntegrableOn (fun x => w r x * physLamDual κ tr r i x)
      (B0579.cell (ν ^ (-2 : ℝ))))
    (hIntLam : IntegrableOn (fun x => w r x * physFrameLam κ ν r i x)
      (B0579.cell (ν ^ (-2 : ℝ)))) :
    (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * normPhysLamDual κ P tr t r i x) =
      (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((clockNC P ν t r i)⁻¹ *
          amplResidual κ P (periodizedFrame κ ν m b K hν hF) tr w r i) := by
  let S := B0579.cell (ν ^ (-2 : ℝ))
  have h1 : IntegrableOn (fun x => (clockNC P ν t r i)⁻¹ * (w r x * physLamDual κ tr r i x)) S :=
    hIntDual.const_mul _
  have h2 : IntegrableOn (fun x =>
      ((((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * (clockNC P ν t r i)⁻¹ * modeDiag P ν r i) *
        (w r x * physFrameLam κ ν r i x)) S :=
    hIntLam.const_mul _
  have heq : (fun x => w r x * normPhysLamDual κ P tr t r i x) =
      fun x => (clockNC P ν t r i)⁻¹ * (w r x * physLamDual κ tr r i x) -
        ((((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * (clockNC P ν t r i)⁻¹ * modeDiag P ν r i) *
          (w r x * physFrameLam κ ν r i x) := by
    funext x
    unfold normPhysLamDual normPhysFrameLam
    ring
  rw [heq, integral_sub h1 h2, integral_const_mul, integral_const_mul,
    FrameAmplSub.physLamDual_pairing_eq_movH0 κ hν hr tr w i,
    ← FrameAmplSub.ampl_eq_phys_pairing κ hν hr hF w i]
  unfold amplResidual
  ring

/-- Continuity of `r ↦ normAmpl (periodizedFrame κ ν m b K hν hF) P t w r i` on `Ioc t s`
along any `IsLinearisedFlow`. -/
theorem continuousOn_normAmpl (κ : PlanarFrameKernels) (P : PlanarData)
    {D₁ ν m b K t s : ℝ}
    (hD₁ : ∀ d : ℝ, D₁ ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hm : 8 < m) (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s)
    (hbs : b ≤ clockTheta ν s) (hF : PerFrameFacts κ ν m b K)
    (hd : ∀ r ∈ Icc t s, max D₁ 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (i : Fin 2) :
    ContinuousOn
      (fun r => normAmpl (periodizedFrame κ ν m b K hν hF) P t w r i) (Ioc t s) := by
  have hNC := FrameAmplSub.continuousOn_clockNC_inv P hν ht (s := s) i
  have hampl := (FlowMeas.continuousOn_ampl κ hD₁ hm hν ht hts hbs hF hd hw i).mono
    Ioc_subset_Icc_self
  exact hNC.mul hampl

/-! ## Integrability of `movingPhi(physLamDual) * W` and linear decomposition of `movH0` -/

/-- Whenever `movLamDualHeat κ ν r i` and `movLamDualEulerSub κ lam tr r i` belong to
`MemLp · 2 (B0579.cellMeasure d(r) (-m))`, for any `W ∈ MemLp · 2 (B0579.cellMeasure d(r) m)` the
product `movingPhi ν (physLamDual κ tr · i) r * W` is integrable on `movingCell`. -/
theorem integrableOn_movingPhi_physLamDual_mul (κ : PlanarFrameKernels) (lam : ℂ)
    {ν m r : ℝ} (hm : 8 < m) (hν : 0 < ν) (hr : 0 ≤ r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (i : Fin 2)
    (hHeat_mem : MemLp (movLamDualHeat κ ν r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)))
    (hEuler_mem : MemLp (movLamDualEulerSub κ lam tr r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)))
    {W : ℝ × ℝ → ℂ}
    (hW_mem : MemLp W 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m)) :
    IntegrableOn
      (fun y => movingPhi ν (fun r' => physLamDual κ tr r' i) r y * W y)
      (movingCell ν (ν ^ (-2 : ℝ)) r) := by
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hSub_mem : MemLp (movLamDualSub κ lam tr r i) 2 (B0579.cellMeasure d (-m)) := by
    have heq : movLamDualSub κ lam tr r i =
        movLamDualHeat κ ν r i + movLamDualEulerSub κ lam tr r i := by
      funext y
      exact movLamDualSub_eq_add κ lam tr r i y
    rw [heq]
    exact hHeat_mem.add hEuler_mem
  have hSub_int : IntegrableOn (fun y => movLamDualSub κ lam tr r i y * W y) (B0579.cell d) :=
    (xNorm_pairing_bound hSub_mem hW_mem).1
  have hLam_int : IntegrableOn
      (fun y => seedModeEigen lam i * (perLam κ d i y * W y)) (B0579.cell d) :=
    (integrableOn_perLam_mul κ hm hd i hW_mem).const_mul (seedModeEigen lam i)
  have hDual_int : IntegrableOn (fun y => movLamDual κ tr r i y * W y) (B0579.cell d) := by
    have heq : (fun y => movLamDual κ tr r i y * W y) =
        fun y => movLamDualSub κ lam tr r i y * W y +
          seedModeEigen lam i * (perLam κ d i y * W y) := by
      funext y
      unfold movLamDualSub
      ring
    rw [heq]
    exact hSub_int.add hLam_int
  have ha2 : (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) = 1 := by
    have h1 : (clockA ν r) ^ (-2 : ℝ) * (clockA ν r) ^ (2 : ℝ) = 1 := by
      rw [← Real.rpow_add ha0]
      norm_num
    rw [← Complex.ofReal_mul, h1, Complex.ofReal_one]
  have hscale : (fun y => movingPhi ν (fun r' => physLamDual κ tr r' i) r y * W y) =
      fun y => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * (movLamDual κ tr r i y * W y) := by
    funext y
    unfold movLamDual
    rw [← mul_assoc, ← mul_assoc, ha2, one_mul]
  unfold movingCell
  rw [hscale]
  exact hDual_int.const_mul _

/-- Discharges the linear decomposition of `movH0` across
`movingW ν w r = (∑ j, ampl F w r j • F.E r j) + compl F w r` whenever `movLamDualHeat` and
`movLamDualEulerSub` lie in `MemLp · 2 (B0579.cellMeasure d(r) (-m))`. -/
theorem movH0_movingW_decomp_of_memLp (κ : PlanarFrameKernels) (lam : ℂ)
    {ν m b K t r : ℝ} (hm : 8 < m) (hν : 0 < ν) (ht : 0 ≤ t) (htr : t ≤ r)
    (hbr : b ≤ clockTheta ν r)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hF : PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (i : Fin 2)
    (hHeat_mem : MemLp (movLamDualHeat κ ν r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)))
    (hEuler_mem : MemLp (movLamDualEulerSub κ lam tr r i) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m))) :
    let F := periodizedFrame κ ν m b K hν hF
    movH0 κ tr r i (movingW ν w r) =
      (∑ j : Fin 2, ampl F w r j * movH0 κ tr r i (F.E r j)) + movH0 κ tr r i (compl F w r) := by
  intro F
  have hm0 : 0 ≤ m := by linarith
  have hr0 : 0 ≤ r := ht.trans htr
  have hW_int := integrableOn_movingPhi_physLamDual_mul κ lam hm hν hr0 hd tr i hHeat_mem hEuler_mem
    (memLp_movingW hm0 hν ht htr hw)
  have hE_int : ∀ j : Fin 2,
      IntegrableOn (fun y => movingPhi ν (fun r' => physLamDual κ tr r' i) r y * F.E r j y)
        (movingCell ν (ν ^ (-2 : ℝ)) r) := fun j =>
    integrableOn_movingPhi_physLamDual_mul κ lam hm hν hr0 hd tr i hHeat_mem hEuler_mem
      (memLp_frame_E F hr0 hbr j)
  exact FrameAmplSub.movH0_movingW_decomp κ F tr w i hW_int hE_int

end WeakFTCSub

/-! ## Conditional assembly of `AmplWeakFTC` -/

open ComplCouplingSub WeakFTCSub in
/-- Conditional proof of `AmplWeakFTC κ` from `MovLamDualHeatBound κ`,
`MovLamDualEulerSubBound κ`, and `NormAmplCutFTC κ`. -/
theorem amplWeakFTC_of (κ : PlanarFrameKernels)
    (hHeat : MovLamDualHeatBound κ) (hEuler : MovLamDualEulerSubBound κ)
    (hFTC : NormAmplCutFTC κ) :
    AmplWeakFTC κ := by
  intro hκ P hP m hm K
  obtain ⟨_C_h, b_h, _hCh, hbh, Hb_h⟩ := hHeat hκ m hm
  obtain ⟨lam, _C_e, b_e, _hCe, _hbe, Hb_e⟩ := hEuler hκ m hm
  obtain ⟨b_c, _hbc, Hb_c⟩ := hFTC hHeat hEuler hκ P hP m hm K
  refine ⟨max (max b_h b_e) b_c,
    le_trans hbh (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro b hb
  obtain ⟨ν_h, hν_h, Hν_h⟩ := Hb_h b (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hb)
  obtain ⟨ν_e, hν_e, Hν_e⟩ := Hb_e b (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hb)
  obtain ⟨ν_c, hν_c, Hν_c⟩ := Hb_c b (le_trans (le_max_right _ _) hb)
  refine ⟨min (min (min ν_h ν_e) ν_c) 1, by positivity, ?_⟩
  intro ν hν hF tr htr t s ht hts hbs f w u hw hcirc
  have hν0 : 0 < ν := hν.1
  have hν_le_h : ν ≤ ν_h :=
    le_trans hν.2 (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hν_le_e : ν ≤ ν_e :=
    le_trans hν.2 (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hν_le_c : ν ≤ ν_c :=
    le_trans hν.2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hν_le_1 : ν ≤ 1 := le_trans hν.2 (min_le_right _ _)
  have hb1 : 1 ≤ b :=
    le_trans hbh (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hb)
  obtain ⟨hMeas, hInt⟩ := Hν_c ν ⟨hν0, hν_le_c⟩ hF tr htr t s ht hts hbs f w u hw hcirc
  refine ⟨hMeas, hInt, ?_⟩
  intro r hr i
  have hr0 : 0 ≤ r := ht.trans hr.1.le
  have hbr : b ≤ clockTheta ν r := hbs.trans (theta_anti hν0 hr0 hr.2)
  have hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    one_le_cellLen_of_theta hν0 hν_le_1 hr0 (hb1.trans hbr)
  obtain ⟨hHm, _hHb⟩ := Hν_h ν ⟨hν0, hν_le_h⟩ r hr0 hbr i
  obtain ⟨hEm, _hEb⟩ := Hν_e ν ⟨hν0, hν_le_e⟩ tr htr r hr0 hbr i
  exact movH0_movingW_decomp_of_memLp κ lam hm hν0 ht hr.1.le hbr hd hF hw i hHm hEm

end UnforcedLeray.Short.IIIa
