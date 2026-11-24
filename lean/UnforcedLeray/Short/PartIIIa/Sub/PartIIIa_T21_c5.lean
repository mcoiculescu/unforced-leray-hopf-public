import UnforcedLeray.Short.PartIIIa.Clock.Frame
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H1
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.PairingCoV

/-!
# Part III-a, task `PartIII-a:T21/c5`: amplitude ODE bound for the periodized frame (`FrameAmplitudeAll`)

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2933 and
2991-3000 (`eq:short-causal-moving-eq`, `eq:short-causal-damped-complement`,
`eq:short-causal-ampl-moving`).

## Mathematical structure and leaf decomposition

For the periodized frame `F = periodizedFrame κ ν m b K hν.1 hF` built from a Part I seed kernel
`κ` (`IsSeedKernels κ`):

1. **Physical-to-moving pairing identities (proved here in `FrameAmplSub`)**:
   * `ampl_eq_phys_pairing`: by `pairingCoV` (`Sub/T21_2_3/PairingCoV.lean`), the moving-frame
     amplitude `ampl F w r i = ∫ y in movingCell, F.lam r i y * movingW ν w r y` equals the
     physical cell pairing `∫ x in B0579.cell (ν ^ (-2)), w r x * physFrameLam κ ν r i x`, where
     `physFrameLam κ ν r i = physAdj (clockA ν r) (perLam κ d(r) i)`.
   * `physLamDual` and `movH0`: the formal adjoint drift-diffusion-nonlocal operator
     `physLamDual κ tr r i` (`Sub/T21_2_3/LinAdjDualitySub.lean`, `Sub/T21_2_1/KernelDefs.lean`)
     pulls back to moving coordinates via `movingPhi` (`Clock/WeakSmoothing/Adjoint.lean`), and
     `physLamDual_pairing_eq_movH0` proves that the physical cell pairing
     `∫ x in B0579.cell (ν ^ (-2)), w r x * physLamDual κ tr r i x` equals
     `((clockA ν r) ^ (-2 : ℝ) : ℂ) * movH0 κ tr r i (movingW ν w r)` (`dz = dr / a(r)²`).
   * `movH0_movingW_decomp` and `lam_pairing_compl_eq_zero`: linear decomposition of `movH0` across
     `movingW ν w r = (∑ j, ampl F w r j • F.E r j) + compl F w r` and biorthogonality
     `∫ y in movingCell, F.lam r i y * compl F w r y = 0` from `IntegrableOn` on `movingCell`.

2. **Complex normaliser `clockNC` and its age derivatives (proved here in `FrameAmplSub`)**:
   * `clockNC P ν t r i = (clockN P ν t r : ℂ) * Complex.exp ((clockPhaseIm P ν t r i : ℂ) * Complex.I)`
     incorporates the oscillatory mode phase `Im λ_i (θ_t - θ_r) + Im κ_i log(θ_t / θ_r)` while
     having exact modulus `‖clockNC P ν t r i‖ = clockN P ν t r` (`norm_clockNC`), initial value
     `clockNC P ν t t i = 1` (`clockNC_self`), and age derivative
     `d/dr (clockNC P ν t r i) = a(r)⁻² * modeDiag P ν r i * clockNC P ν t r i`
     (`hasDerivAt_clockNC`, `hasDerivAt_clockNC_inv`).
   * `normAmpl F P t w r i = (clockNC P ν t r i)⁻¹ * ampl F w r i` satisfies
     `∑ i : Fin 2, ENNReal.ofReal ‖normAmpl F P t w r i‖ = amplNorm F w r / ENNReal.ofReal (clockN P ν t r)`
     (`sum_ofReal_norm_normAmpl`).

3. **Three analytical leaves**:
   * `AmplWeakFTC` (`PartIII-a:T21/c5/1`, SP 2898-2918, 2998-3000): for `b ≥ b₀` and `ν ∈ (0, ν₀]`,
     along a weak linearised flow `IsLinearisedFlow` with `HasZeroCirculation`, testing against
     `(clockNC P ν t r i)⁻¹ * physFrameLam κ ν r i x` on `(t, s]` cancels the diagonal
     `(λ_i + κ_i / θ(r)) ampl F w r i` (with `dz = a(r)⁻² dr`) and yields the Bochner integral
     identity
     `normAmpl F P t w s i - normAmpl F P t w t i = ∫ r in Ioc t s, ((clockA ν r) ^ (-2 : ℝ) : ℂ) * ((clockNC P ν t r i)⁻¹ * amplResidual κ P F tr w r i)`,
     together with `AEMeasurable` of `amplResidual` and the linear decomposition of `movH0` across
     `movingW ν w r = (∑ j, ampl F w r j • F.E r j) + compl F w r`.
   * `AmplDirectError` (`PartIII-a:T21/c5/2`, SP 2991-2995): the direct frame error on the
     periodized growing modes `F.E r j = perE κ d(r) j` satisfies
     `∑ i : Fin 2, ‖amplDirectMat κ P F tr r i j‖ ≤ C₁ * ν ^ 3 / clockTheta ν r`.
   * `AmplComplCoupling` (`PartIII-a:T21/c5/3`, SP 2995-2997): the coupling of `movH0` on the
     complement `compl F w r` satisfies
     `∑ i : Fin 2, ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖ ≤ ENNReal.ofReal (C₂ * (1 / clockTheta ν r)) * xNorm d(r) m (compl F w r)`.

4. **Proved assembly (`frameAmplitudeAll_of`)**:
   Combines `AmplWeakFTC`, `AmplDirectError`, and `AmplComplCoupling` with `frameAmp_mono`
   (`Clock/LongAssemble/H2.lean`), the `clockNC` norm identities, `amplResidual_eq_sum_add`,
   `enorm_integral_le_lintegral_enorm`, and `lintegral_add_left'` to establish
   `FrameAmplitudeAll κ` with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## Complex mode eigenvalues, diagonal, normaliser `clockNC`, and moving pairing `movH0` -/

/-- Eigenvalue `λ_i` for mode `i ∈ {0, 1}`: `P.eigenvalue` for `i = 0`, `conj P.eigenvalue` for `i = 1`
(SP 2891-2897). -/
def modeEigen (P : PlanarData) (i : Fin 2) : ℂ :=
  if i = 0 then P.eigenvalue else starRingEnd ℂ P.eigenvalue

/-- Subleading coefficient `κ_i` for mode `i ∈ {0, 1}`: `P.kappa` for `i = 0`, `conj P.kappa` for `i = 1`
(SP 2991-2995). -/
def modeKappa (P : PlanarData) (i : Fin 2) : ℂ :=
  if i = 0 then P.kappa else starRingEnd ℂ P.kappa

/-- Instantaneous mode diagonal `λ_i + κ_i / θ(r)` removed by the normaliser (SP 2991-2997). -/
def modeDiag (P : PlanarData) (ν r : ℝ) (i : Fin 2) : ℂ :=
  modeEigen P i + modeKappa P i / (clockTheta ν r : ℂ)

/-- Imaginary part of the cumulative mode phase on `[t, r]` for mode `i ∈ {0, 1}`. -/
def clockPhaseIm (P : PlanarData) (ν t r : ℝ) (i : Fin 2) : ℝ :=
  (if i = 0 then (1 : ℝ) else -1) *
    (P.eigenvalue.im * (clockTheta ν t - clockTheta ν r) +
      P.kappa.im * Real.log (clockTheta ν t / clockTheta ν r))

/-- Complex mode normaliser `N_{t,r,i} = clockN P ν t r * exp(i * clockPhaseIm P ν t r i)`
whose derivative with respect to `r` equals `a(r)⁻² * modeDiag P ν r i * clockNC P ν t r i` and
whose modulus equals `clockN P ν t r` for both modes `i = 0, 1` (SP 2998-3000). -/
def clockNC (P : PlanarData) (ν t r : ℝ) (i : Fin 2) : ℂ :=
  (clockN P ν t r : ℂ) * Complex.exp ((clockPhaseIm P ν t r i : ℂ) * Complex.I)

/-- Normalised mode amplitude `(clockNC P ν t r i)⁻¹ * ampl F w r i` (SP 2998-3000). -/
def normAmpl {ν c m b K : ℝ} (F : MovingFrame ν c m b K) (P : PlanarData) (t : ℝ)
    (w : ℝ → ℝ × ℝ → ℂ) (r : ℝ) (i : Fin 2) : ℂ :=
  (clockNC P ν t r i)⁻¹ * ampl F w r i

/-- Physical-variable dual test function `φ_i(r, x) = a(r)⁻¹ Λ_i(d(r), x / √a(r))` associated
with the periodized dual row `perLam κ d(r) i` (SP 2898-2905). -/
def physFrameLam (κ : PlanarFrameKernels) (ν r : ℝ) (i : Fin 2) : ℝ × ℝ → ℂ :=
  physAdj (clockA ν r) (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i)

/-- Physical-variable formal adjoint operator applied to `physFrameLam κ ν · i` along the
train `tr` (SP 2905-2918, using `ladDt`, `ladLapCx`, `ladTransport` from `Sub/T21_2_3` and
`kerAdj` from `Sub/T21_2_1`). -/
def physLamDual (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2)
    (x : ℝ × ℝ) : ℂ :=
  ladDt (fun r' x' => physFrameLam κ ν r' i x') r x +
    (ν : ℂ) * ladLapCx (physFrameLam κ ν r i) x +
    ladTransport tr r (physFrameLam κ ν r i) x -
    kerAdj (ν ^ (-2 : ℝ)) (fun k y => physFrameLam κ ν r i y *
      (B0579.pd k (UnforcedLeray.B0238.Ec tr r) y : ℂ)) x

/-- Moving-variable pairing functional
`movH0 κ tr r i W = a(r)² ∫_{movingCell} movingPhi(physLamDual)(r, y) W(y) dy`
representing `(d/dz) ⟨Λ_i, W⟩ = a(r)² (d/dr) ⟨Λ_i, W⟩` along the linearised flow
(SP 2905-2918, 2991-2997). -/
def movH0 (κ : PlanarFrameKernels) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (i : Fin 2)
    (W : ℝ × ℝ → ℂ) : ℂ :=
  (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
    ∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
      movingPhi ν (fun r' => physLamDual κ tr r' i) r y * W y

/-- Mode-`i` moving-time residual pairing after subtracting the diagonal
`modeDiag P ν r i * ampl F w r i` (SP 2991-2997). -/
def amplResidual (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (w : ℝ → ℝ × ℝ → ℂ) (r : ℝ) (i : Fin 2) : ℂ :=
  movH0 κ tr r i (movingW ν w r) - modeDiag P ν r i * ampl F w r i

/-- Direct frame-error matrix entry `D_{i,j}(r) = movH0 κ tr r i (F.E r j) - δ_{i,j} modeDiag P ν r i`
(SP 2991-2995). -/
def amplDirectMat (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (r : ℝ) (i j : Fin 2) : ℂ :=
  movH0 κ tr r i (F.E r j) - (if i = j then modeDiag P ν r i else 0)

/-! ## The three analytical leaves of `FrameAmplitudeProof` -/

/-- **Leaf 1 (`AmplWeakFTC`, `PartIII-a:T21/c5/1`, SP 2898-2918, 2991-3000)**: for `b ≥ b₀` and
`ν ∈ (0, ν₀]`, weak fundamental theorem of calculus for the normalised frame amplitudes
`normAmpl F P t w · i` along a linearised flow `IsLinearisedFlow`, together with `AEMeasurable`
of `amplResidual` and the linear decomposition of `movH0` across
`movingW = (∑_j ampl_j E_j) + compl`. -/
def AmplWeakFTC (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∃ b₀ : ℝ, 1 ≤ b₀ ∧
    ∀ b : ℝ, b₀ ≤ b →
      ∃ ν₀ : ℝ, 0 < ν₀ ∧
        ∀ ν : ℝ, (hν : ν ∈ Ioc 0 ν₀) → ∀ (hF : PerFrameFacts κ ν m b K),
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
                ((clockNC P ν t r i)⁻¹ * amplResidual κ P F tr w r i)) ∧
        (∀ r ∈ Ioc t s, ∀ i : Fin 2,
          movH0 κ tr r i (movingW ν w r) =
            (∑ j : Fin 2, ampl F w r j * movH0 κ tr r i (F.E r j)) + movH0 κ tr r i (compl F w r))

/-- **Leaf 2 (`AmplDirectError`, `PartIII-a:T21/c5/2`, SP 2991-2995)**: the direct frame error on
the periodized growing modes `F.E r j = perE κ d(r) j` is bounded by `C₁ * ν ^ 3 / clockTheta ν r`. -/
def AmplDirectError (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∃ C₁ b₁ : ℝ, 0 ≤ C₁ ∧ 1 ≤ b₁ ∧
    ∀ b : ℝ, b₁ ≤ b →
      ∃ ν₁ : ℝ, 0 < ν₁ ∧
        ∀ ν : ℝ, (hν : ν ∈ Ioc 0 ν₁) → ∀ (hF : PerFrameFacts κ ν m b K),
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
        ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
        ∀ j : Fin 2,
          (∑ i : Fin 2, ‖amplDirectMat κ P (periodizedFrame κ ν m b K hν.1 hF) tr r i j‖) ≤
            C₁ * ν ^ 3 / clockTheta ν r

/-- **Leaf 3 (`AmplComplCoupling`, `PartIII-a:T21/c5/3`, SP 2995-2997)**: the coupling of `movH0`
on the complement `compl F w r` along a linearised flow is bounded by
`C₂ * (1 / clockTheta ν r) * xNorm d(r) m (compl F w r)`. -/
def AmplComplCoupling (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∃ C₂ b₂ : ℝ, 0 ≤ C₂ ∧ 1 ≤ b₂ ∧
    ∀ b : ℝ, b₂ ≤ b →
      ∃ ν₂ : ℝ, 0 < ν₂ ∧
        ∀ ν : ℝ, (hν : ν ∈ Ioc 0 ν₂) → ∀ (hF : PerFrameFacts κ ν m b K),
        ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))), PartI.IsBUCTrain tr →
        ∀ t s : ℝ, 0 ≤ t → t ≤ s → b ≤ clockTheta ν s →
        ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
          HasZeroCirculation (ν ^ (-2 : ℝ)) f →
        ∀ r ∈ Ioc t s,
          (∑ i : Fin 2,
            ENNReal.ofReal ‖movH0 κ tr r i (compl (periodizedFrame κ ν m b K hν.1 hF) w r)‖) ≤
            ENNReal.ofReal (C₂ * (1 / clockTheta ν r)) *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (compl (periodizedFrame κ ν m b K hν.1 hF) w r)

namespace FrameAmplSub

/-! ## Normaliser identities and age derivatives -/

theorem clockPhaseIm_self (P : PlanarData) (ν t : ℝ) (i : Fin 2) :
    clockPhaseIm P ν t t i = 0 := by
  unfold clockPhaseIm
  by_cases hθ : clockTheta ν t = 0
  · simp [hθ]
  · simp [sub_self, div_self hθ, Real.log_one]

theorem clockNC_self (P : PlanarData) {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (i : Fin 2) :
    clockNC P ν t t i = 1 := by
  unfold clockNC
  rw [clockN_self P hν ht, clockPhaseIm_self]
  simp

theorem norm_clockNC (P : PlanarData) {ν t r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (i : Fin 2) :
    ‖clockNC P ν t r i‖ = clockN P ν t r := by
  unfold clockNC
  rw [norm_mul, Complex.norm_of_nonneg (clockN_pos P hν ht hr).le,
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem norm_clockNC_inv (P : PlanarData) {ν t r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (i : Fin 2) :
    ‖(clockNC P ν t r i)⁻¹‖ = (clockN P ν t r)⁻¹ := by
  rw [norm_inv, norm_clockNC P hν ht hr i]

theorem clockNC_ne_zero (P : PlanarData) {ν t r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (i : Fin 2) :
    clockNC P ν t r i ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_clockNC P hν ht hr i]
  exact (clockN_pos P hν ht hr).ne'

/-- Age derivative of `clockA ν`: `(d/dr) (1 + ν r) = ν`. -/
theorem hasDerivAt_clockA (ν r : ℝ) :
    HasDerivAt (clockA ν) ν r := by
  have h1 : HasDerivAt (fun r' => 1 + ν * r') (0 + ν * 1) r :=
    (hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).const_mul ν)
  exact h1.congr_deriv (by ring)

/-- Age derivative of `clockTheta ν`: `(d/dr) θ(r) = -(clockA ν r) ^ (-2 : ℝ)`. -/
theorem hasDerivAt_clockTheta {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    HasDerivAt (clockTheta ν) (-(clockA ν r) ^ (-2 : ℝ)) r := by
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  have hνa : ν * clockA ν r ≠ 0 := (mul_pos hν ha).ne'
  have h1 : HasDerivAt (fun r' => ν * clockA ν r') (ν * ν) r :=
    (hasDerivAt_clockA ν r).const_mul ν
  have h2 : HasDerivAt (clockTheta ν) (-(ν * ν) / (ν * clockA ν r) ^ 2) r := h1.inv hνa
  refine h2.congr_deriv ?_
  rw [Real.rpow_neg ha.le, Real.rpow_two, ← one_div]
  field_simp [hν.ne', ha.ne']

/-- Age derivative of `clockN P ν t`:
`(d/dr) clockN P ν t r = (clockA ν r) ^ (-2 : ℝ) * (P.eigenvalue.re + P.kappa.re / clockTheta ν r) * clockN P ν t r`. -/
theorem hasDerivAt_clockN (P : PlanarData) {ν t r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    HasDerivAt (clockN P ν t)
      ((clockA ν r) ^ (-2 : ℝ) * (P.eigenvalue.re + P.kappa.re / clockTheta ν r) * clockN P ν t r) r := by
  have hθt : 0 < clockTheta ν t := theta_pos hν ht
  have hθr : 0 < clockTheta ν r := theta_pos hν hr
  have hq : 0 < clockTheta ν t / clockTheta ν r := div_pos hθt hθr
  have hdθ := hasDerivAt_clockTheta hν hr
  have hsub : HasDerivAt (fun r' => P.eigenvalue.re * (clockTheta ν t - clockTheta ν r'))
      (P.eigenvalue.re * (clockA ν r) ^ (-2 : ℝ)) r := by
    have hs : HasDerivAt (fun r' => clockTheta ν t - clockTheta ν r')
        (0 - -(clockA ν r) ^ (-2 : ℝ)) r :=
      (hasDerivAt_const r (clockTheta ν t)).sub hdθ
    exact (hs.const_mul P.eigenvalue.re).congr_deriv (by ring)
  have hexp := hsub.exp
  have hdiv : HasDerivAt (fun r' => clockTheta ν t / clockTheta ν r')
      ((clockTheta ν t / clockTheta ν r) * ((clockA ν r) ^ (-2 : ℝ) / clockTheta ν r)) r := by
    have hd : HasDerivAt (fun r' => clockTheta ν t / clockTheta ν r')
        ((0 * clockTheta ν r - clockTheta ν t * -(clockA ν r) ^ (-2 : ℝ)) / clockTheta ν r ^ 2) r :=
      (hasDerivAt_const r (clockTheta ν t)).div hdθ hθr.ne'
    refine hd.congr_deriv ?_
    field_simp [hθr.ne']
    ring
  have hrpow := hdiv.rpow_const (p := P.kappa.re) (Or.inl hq.ne')
  have hmul : HasDerivAt (clockN P ν t)
      (Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν r)) *
          (P.eigenvalue.re * (clockA ν r) ^ (-2 : ℝ)) *
          (clockTheta ν t / clockTheta ν r) ^ P.kappa.re +
        Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν r)) *
          ((clockTheta ν t / clockTheta ν r) * ((clockA ν r) ^ (-2 : ℝ) / clockTheta ν r) *
            P.kappa.re * (clockTheta ν t / clockTheta ν r) ^ (P.kappa.re - 1))) r :=
    hexp.mul hrpow
  refine hmul.congr_deriv ?_
  have hrp : (clockTheta ν t / clockTheta ν r) ^ (P.kappa.re - 1) *
      (clockTheta ν t / clockTheta ν r) = (clockTheta ν t / clockTheta ν r) ^ P.kappa.re := by
    have := Real.rpow_add hq (P.kappa.re - 1) 1
    rw [sub_add_cancel, Real.rpow_one] at this
    exact this.symm
  unfold clockN
  linear_combination Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν r)) *
    P.kappa.re * ((clockA ν r) ^ (-2 : ℝ) / clockTheta ν r) * hrp

/-- Age derivative of `clockPhaseIm P ν t · i`:
`(d/dr) clockPhaseIm P ν t r i = (clockA ν r) ^ (-2 : ℝ) * ((modeEigen P i).im + (modeKappa P i).im / clockTheta ν r)`. -/
theorem hasDerivAt_clockPhaseIm (P : PlanarData) {ν t r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (i : Fin 2) :
    HasDerivAt (fun r' => clockPhaseIm P ν t r' i)
      ((clockA ν r) ^ (-2 : ℝ) * ((modeEigen P i).im + (modeKappa P i).im / clockTheta ν r)) r := by
  have hθt : 0 < clockTheta ν t := theta_pos hν ht
  have hθr : 0 < clockTheta ν r := theta_pos hν hr
  have hq : 0 < clockTheta ν t / clockTheta ν r := div_pos hθt hθr
  have hdθ := hasDerivAt_clockTheta hν hr
  have hsub : HasDerivAt (fun r' => P.eigenvalue.im * (clockTheta ν t - clockTheta ν r'))
      (P.eigenvalue.im * (clockA ν r) ^ (-2 : ℝ)) r := by
    have hs : HasDerivAt (fun r' => clockTheta ν t - clockTheta ν r')
        (0 - -(clockA ν r) ^ (-2 : ℝ)) r :=
      (hasDerivAt_const r (clockTheta ν t)).sub hdθ
    exact (hs.const_mul P.eigenvalue.im).congr_deriv (by ring)
  have hdiv : HasDerivAt (fun r' => clockTheta ν t / clockTheta ν r')
      ((clockTheta ν t / clockTheta ν r) * ((clockA ν r) ^ (-2 : ℝ) / clockTheta ν r)) r := by
    have hd : HasDerivAt (fun r' => clockTheta ν t / clockTheta ν r')
        ((0 * clockTheta ν r - clockTheta ν t * -(clockA ν r) ^ (-2 : ℝ)) / clockTheta ν r ^ 2) r :=
      (hasDerivAt_const r (clockTheta ν t)).div hdθ hθr.ne'
    refine hd.congr_deriv ?_
    field_simp [hθr.ne']
    ring
  have hlog : HasDerivAt (fun r' => P.kappa.im * Real.log (clockTheta ν t / clockTheta ν r'))
      (P.kappa.im * ((clockA ν r) ^ (-2 : ℝ) / clockTheta ν r)) r := by
    have hl : HasDerivAt (fun r' => P.kappa.im * Real.log (clockTheta ν t / clockTheta ν r'))
        (P.kappa.im * (((clockTheta ν t / clockTheta ν r) *
          ((clockA ν r) ^ (-2 : ℝ) / clockTheta ν r)) / (clockTheta ν t / clockTheta ν r))) r :=
      (hdiv.log hq.ne').const_mul P.kappa.im
    refine hl.congr_deriv ?_
    field_simp [hq.ne']
  have htot : HasDerivAt (fun r' => clockPhaseIm P ν t r' i)
      ((if i = 0 then (1 : ℝ) else -1) *
        (P.eigenvalue.im * (clockA ν r) ^ (-2 : ℝ) +
          P.kappa.im * ((clockA ν r) ^ (-2 : ℝ) / clockTheta ν r))) r :=
    (hsub.add hlog).const_mul (if i = 0 then (1 : ℝ) else -1)
  refine htot.congr_deriv ?_
  unfold modeEigen modeKappa
  fin_cases i <;> simp <;> ring

/-- Age derivative of the complex normaliser `clockNC P ν t · i`:
`(d/dr) clockNC P ν t r i = a(r)⁻² * modeDiag P ν r i * clockNC P ν t r i`. -/
theorem hasDerivAt_clockNC (P : PlanarData) {ν t r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (i : Fin 2) :
    HasDerivAt (fun r' => clockNC P ν t r' i)
      ((((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * modeDiag P ν r i * clockNC P ν t r i) r := by
  have hdN : HasDerivAt (fun r' => (clockN P ν t r' : ℂ))
      ((((clockA ν r) ^ (-2 : ℝ) *
        (P.eigenvalue.re + P.kappa.re / clockTheta ν r) * clockN P ν t r : ℝ) : ℂ)) r :=
    (hasDerivAt_clockN P hν ht hr).ofReal_comp
  have hdPh : HasDerivAt (fun r' => (clockPhaseIm P ν t r' i : ℂ) * Complex.I)
      ((((clockA ν r) ^ (-2 : ℝ) *
        ((modeEigen P i).im + (modeKappa P i).im / clockTheta ν r) : ℝ) : ℂ) * Complex.I) r :=
    (hasDerivAt_clockPhaseIm P hν ht hr i).ofReal_comp.mul_const Complex.I
  have hdExp := hdPh.cexp
  have hmul : HasDerivAt (fun r' => clockNC P ν t r' i)
      (((((clockA ν r) ^ (-2 : ℝ) *
          (P.eigenvalue.re + P.kappa.re / clockTheta ν r) * clockN P ν t r : ℝ) : ℂ)) *
        Complex.exp ((clockPhaseIm P ν t r i : ℂ) * Complex.I) +
        (clockN P ν t r : ℂ) * (Complex.exp ((clockPhaseIm P ν t r i : ℂ) * Complex.I) *
          ((((clockA ν r) ^ (-2 : ℝ) *
            ((modeEigen P i).im + (modeKappa P i).im / clockTheta ν r) : ℝ) : ℂ) * Complex.I))) r :=
    hdN.mul hdExp
  refine hmul.congr_deriv ?_
  have hre : (modeEigen P i).re = P.eigenvalue.re ∧ (modeKappa P i).re = P.kappa.re := by
    unfold modeEigen modeKappa
    fin_cases i <;> simp
  have hdiag : (P.eigenvalue.re : ℂ) + (P.kappa.re : ℂ) / (clockTheta ν r : ℂ) +
      (((modeEigen P i).im : ℂ) + ((modeKappa P i).im : ℂ) / (clockTheta ν r : ℂ)) * Complex.I =
      modeDiag P ν r i := by
    rw [← hre.1, ← hre.2]
    unfold modeDiag
    have h1 : ((modeEigen P i).re : ℂ) + ((modeEigen P i).im : ℂ) * Complex.I = modeEigen P i :=
      Complex.re_add_im (modeEigen P i)
    have h2 : ((modeKappa P i).re : ℂ) + ((modeKappa P i).im : ℂ) * Complex.I = modeKappa P i :=
      Complex.re_add_im (modeKappa P i)
    linear_combination h1 + h2 / (clockTheta ν r : ℂ)
  unfold clockNC
  push_cast
  linear_combination ((((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * (clockN P ν t r : ℂ) *
    Complex.exp ((clockPhaseIm P ν t r i : ℂ) * Complex.I)) * hdiag

/-- Age derivative of the inverse normaliser `(clockNC P ν t · i)⁻¹`:
`(d/dr) (clockNC P ν t r i)⁻¹ = -(a(r)⁻² * modeDiag P ν r i * (clockNC P ν t r i)⁻¹)`. -/
theorem hasDerivAt_clockNC_inv (P : PlanarData) {ν t r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (i : Fin 2) :
    HasDerivAt (fun r' => (clockNC P ν t r' i)⁻¹)
      (-((((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * modeDiag P ν r i * (clockNC P ν t r i)⁻¹)) r := by
  have hne := clockNC_ne_zero P hν ht hr i
  have hinv := (hasDerivAt_clockNC P hν ht hr i).inv hne
  refine hinv.congr_deriv ?_
  field_simp [hne]

theorem continuousOn_clockTheta {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (S : Set ℝ)
    (hS : ∀ r ∈ S, t ≤ r) :
    ContinuousOn (clockTheta ν) S := by
  have hf : ContinuousOn (fun r => ν * clockA ν r) S := by
    unfold clockA
    exact continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
  have h0 : ∀ r ∈ S, ν * clockA ν r ≠ 0 := by
    intro r hr
    have := one_le_clockA hν.le (ht.trans (hS r hr))
    exact (mul_pos hν (by linarith)).ne'
  unfold clockTheta
  exact hf.inv₀ h0

theorem continuousOn_clockNC_inv (P : PlanarData) {ν t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t)
    (i : Fin 2) :
    ContinuousOn (fun r => (clockNC P ν t r i)⁻¹) (Ioc t s) := by
  have hθt : 0 < clockTheta ν t := theta_pos hν ht
  have hθ : ContinuousOn (clockTheta ν) (Ioc t s) :=
    continuousOn_clockTheta hν ht (Ioc t s) (fun _ hr => hr.1.le)
  have hq : ContinuousOn (fun r => clockTheta ν t / clockTheta ν r) (Ioc t s) :=
    continuousOn_const.div hθ (fun r hr => (theta_pos hν (ht.trans hr.1.le)).ne')
  have hq_ne : ∀ r ∈ Ioc t s, clockTheta ν t / clockTheta ν r ≠ 0 := fun r hr =>
    div_ne_zero hθt.ne' (theta_pos hν (ht.trans hr.1.le)).ne'
  have hp : ContinuousOn (fun r => (clockTheta ν t / clockTheta ν r) ^ P.kappa.re) (Ioc t s) :=
    hq.rpow_const (fun r hr => Or.inl (hq_ne r hr))
  have he : ContinuousOn (fun r => Real.exp (P.eigenvalue.re * (clockTheta ν t - clockTheta ν r)))
      (Ioc t s) :=
    (continuousOn_const.mul (continuousOn_const.sub hθ)).rexp
  have hN_cont : ContinuousOn (fun r => clockN P ν t r) (Ioc t s) := he.mul hp
  have hPh_cont : ContinuousOn (fun r => clockPhaseIm P ν t r i) (Ioc t s) := by
    unfold clockPhaseIm
    refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
    · exact continuousOn_const.mul (continuousOn_const.sub hθ)
    · exact continuousOn_const.mul (Real.continuousOn_log.comp hq hq_ne)
  have hNC_cont : ContinuousOn (fun r => clockNC P ν t r i) (Ioc t s) := by
    unfold clockNC
    refine ContinuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hN_cont) ?_
    exact Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hPh_cont).mul continuousOn_const)
  refine hNC_cont.inv₀ (fun r hr => ?_)
  exact clockNC_ne_zero P hν ht (ht.trans hr.1.le) i

theorem normAmpl_self {ν c m b K : ℝ} (F : MovingFrame ν c m b K) (P : PlanarData) {t : ℝ}
    (hν : 0 < ν) (ht : 0 ≤ t) (w : ℝ → ℝ × ℝ → ℂ) (i : Fin 2) :
    normAmpl F P t w t i = ampl F w t i := by
  unfold normAmpl
  rw [clockNC_self P hν ht i, inv_one, one_mul]

theorem norm_normAmpl {ν c m b K : ℝ} (F : MovingFrame ν c m b K) (P : PlanarData) {t r : ℝ}
    (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r) (w : ℝ → ℝ × ℝ → ℂ) (i : Fin 2) :
    ‖normAmpl F P t w r i‖ = ‖ampl F w r i‖ / clockN P ν t r := by
  unfold normAmpl
  rw [norm_mul, norm_clockNC_inv P hν ht hr i, inv_mul_eq_div]

theorem sum_ofReal_norm_normAmpl {ν c m b K : ℝ} (F : MovingFrame ν c m b K) (P : PlanarData)
    {t r : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r) (w : ℝ → ℝ × ℝ → ℂ) :
    (∑ i : Fin 2, ENNReal.ofReal ‖normAmpl F P t w r i‖) =
      amplNorm F w r / ENNReal.ofReal (clockN P ν t r) := by
  have hN : 0 < clockN P ν t r := clockN_pos P hν ht hr
  unfold amplNorm
  simp only [Fin.sum_univ_two, norm_normAmpl F P hν ht hr w,
    ENNReal.ofReal_div_of_pos hN, ENNReal.div_add_div_same]

/-! ## Physical-to-moving pairing identities and linear decomposition of `movH0` -/

/-- Change of variables for the frame amplitude: `ampl F w r i` equals the physical cell pairing
of `w r` with `physFrameLam κ ν r i`. -/
theorem ampl_eq_phys_pairing (κ : PlanarFrameKernels) {ν m b K r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (hF : PerFrameFacts κ ν m b K)
    (w : ℝ → ℝ × ℝ → ℂ) (i : Fin 2) :
    ampl (periodizedFrame κ ν m b K hν hF) w r i =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * physFrameLam κ ν r i x := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  have hco := pairingCoV (ν ^ (-2 : ℝ)) (clockA ν r) hc ha (w r)
    (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i)
  simpa only [ampl, periodizedFrame, movingW, movingCell, physFrameLam, mul_comm] using hco

theorem physAdj_movingPhi_pointwise (ν r : ℝ) (hν : 0 < ν) (hr : 0 ≤ r)
    (φ : ℝ → ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    physAdj (clockA ν r) (movingPhi ν φ r) x = φ r x := by
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  have hsa : Real.sqrt (clockA ν r) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have haC : (clockA ν r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  unfold physAdj movingPhi
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ haC, one_mul,
    mul_div_cancel₀ _ hsa, mul_div_cancel₀ _ hsa]

/-- Change of variables for the dual generator pairing: the physical cell integral of
`w r x * physLamDual κ tr r i x` equals
`(((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr r i (movingW ν w r)`. -/
theorem physLamDual_pairing_eq_movH0 (κ : PlanarFrameKernels) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (w : ℝ → ℝ × ℝ → ℂ) (i : Fin 2) :
    (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * physLamDual κ tr r i x) =
      (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr r i (movingW ν w r) := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  have hco := pairingCoV (ν ^ (-2 : ℝ)) (clockA ν r) hc ha (w r)
    (movingPhi ν (fun r' => physLamDual κ tr r' i) r)
  have hcongr : ∀ x,
      w r x * physAdj (clockA ν r) (movingPhi ν (fun r' => physLamDual κ tr r' i) r) x =
        w r x * physLamDual κ tr r i x := fun x => by
    rw [physAdj_movingPhi_pointwise ν r hν hr (fun r' => physLamDual κ tr r' i) x]
  simp_rw [hcongr] at hco
  have ha2 : (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) = 1 := by
    have h1 : (clockA ν r) ^ (-2 : ℝ) * (clockA ν r) ^ (2 : ℝ) = 1 := by
      rw [← Real.rpow_add ha]
      norm_num
    rw [← Complex.ofReal_mul, h1, Complex.ofReal_one]
  unfold movH0 movingCell movingW
  rw [← mul_assoc, ha2, one_mul, ← hco]
  congr 1
  funext y
  ring

/-- Linear decomposition of `movH0` across `movingW ν w r = (∑ j, ampl F w r j • F.E r j) + compl F w r`
once the pairings with `movingW ν w r` and `F.E r j` are integrable on `movingCell`. -/
theorem movH0_movingW_decomp (κ : PlanarFrameKernels) {ν m b K r : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (w : ℝ → ℝ × ℝ → ℂ) (i : Fin 2)
    (hW : IntegrableOn (fun y => movingPhi ν (fun r' => physLamDual κ tr r' i) r y * movingW ν w r y)
      (movingCell ν (ν ^ (-2 : ℝ)) r))
    (hE : ∀ j : Fin 2, IntegrableOn (fun y => movingPhi ν (fun r' => physLamDual κ tr r' i) r y * F.E r j y)
      (movingCell ν (ν ^ (-2 : ℝ)) r)) :
    movH0 κ tr r i (movingW ν w r) =
      (∑ j : Fin 2, ampl F w r j * movH0 κ tr r i (F.E r j)) + movH0 κ tr r i (compl F w r) := by
  let Φ := movingPhi ν (fun r' => physLamDual κ tr r' i) r
  let S := movingCell ν (ν ^ (-2 : ℝ)) r
  have hE0 : IntegrableOn (fun y => ampl F w r 0 * (Φ y * F.E r 0 y)) S := (hE 0).const_mul _
  have hE1 : IntegrableOn (fun y => ampl F w r 1 * (Φ y * F.E r 1 y)) S := (hE 1).const_mul _
  have hEsum : IntegrableOn (fun y => ampl F w r 0 * (Φ y * F.E r 0 y) +
      ampl F w r 1 * (Φ y * F.E r 1 y)) S := hE0.add hE1
  have hcompl_eq : (fun y => Φ y * compl F w r y) =
      fun y => Φ y * movingW ν w r y -
        (ampl F w r 0 * (Φ y * F.E r 0 y) + ampl F w r 1 * (Φ y * F.E r 1 y)) := by
    funext y
    unfold compl
    simp only [Fin.sum_univ_two]
    ring
  have hint : ∫ y in S, Φ y * compl F w r y =
      (∫ y in S, Φ y * movingW ν w r y) -
        (ampl F w r 0 * (∫ y in S, Φ y * F.E r 0 y) +
          ampl F w r 1 * (∫ y in S, Φ y * F.E r 1 y)) := by
    rw [hcompl_eq, integral_sub hW hEsum, integral_add hE0 hE1,
      integral_const_mul, integral_const_mul]
  unfold movH0
  simp only [Fin.sum_univ_two]
  change (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * (∫ y in S, Φ y * movingW ν w r y) =
    (ampl F w r 0 * ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * (∫ y in S, Φ y * F.E r 0 y)) +
      ampl F w r 1 * ((((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * (∫ y in S, Φ y * F.E r 1 y))) +
    (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) * (∫ y in S, Φ y * compl F w r y)
  rw [hint]
  ring

/-- Biorthogonality on the complement (`Λ r = 0`, SP 2990):
`∫ y in movingCell, F.lam r i y * compl F w r y = 0`. -/
theorem lam_pairing_compl_eq_zero {ν c m b K r : ℝ}
    (F : MovingFrame ν c m b K) (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r)
    (w : ℝ → ℝ × ℝ → ℂ) (i : Fin 2)
    (hW : IntegrableOn (fun y => F.lam r i y * movingW ν w r y) (movingCell ν c r))
    (hE : ∀ j : Fin 2, IntegrableOn (fun y => F.lam r i y * F.E r j y) (movingCell ν c r)) :
    (∫ y in movingCell ν c r, F.lam r i y * compl F w r y) = 0 := by
  let S := movingCell ν c r
  have hE0 : IntegrableOn (fun y => ampl F w r 0 * (F.lam r i y * F.E r 0 y)) S :=
    (hE 0).const_mul _
  have hE1 : IntegrableOn (fun y => ampl F w r 1 * (F.lam r i y * F.E r 1 y)) S :=
    (hE 1).const_mul _
  have hEsum : IntegrableOn (fun y => ampl F w r 0 * (F.lam r i y * F.E r 0 y) +
      ampl F w r 1 * (F.lam r i y * F.E r 1 y)) S := hE0.add hE1
  have hcompl_eq : (fun y => F.lam r i y * compl F w r y) =
      fun y => F.lam r i y * movingW ν w r y -
        (ampl F w r 0 * (F.lam r i y * F.E r 0 y) +
          ampl F w r 1 * (F.lam r i y * F.E r 1 y)) := by
    funext y
    unfold compl
    simp only [Fin.sum_univ_two]
    ring
  rw [hcompl_eq, integral_sub hW hEsum, integral_add hE0 hE1,
    integral_const_mul, integral_const_mul, F.dual r hr hbr i 0, F.dual r hr hbr i 1]
  change ampl F w r i - (ampl F w r 0 * (if i = 0 then 1 else 0) +
    ampl F w r 1 * (if i = 1 then 1 else 0)) = 0
  fin_cases i <;> simp

/-- Algebraic decomposition of `amplResidual` into the direct frame error on the 2-mode span and
the complement coupling `movH0 κ tr r i (compl F w r)`. -/
theorem amplResidual_eq_sum_add (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (w : ℝ → ℝ × ℝ → ℂ) (r : ℝ) (i : Fin 2)
    (hdecomp : movH0 κ tr r i (movingW ν w r) =
      (∑ j : Fin 2, ampl F w r j * movH0 κ tr r i (F.E r j)) + movH0 κ tr r i (compl F w r)) :
    amplResidual κ P F tr w r i =
      (∑ j : Fin 2, ampl F w r j * amplDirectMat κ P F tr r i j) +
        movH0 κ tr r i (compl F w r) := by
  unfold amplResidual amplDirectMat
  rw [hdecomp]
  fin_cases i <;> simp [Fin.sum_univ_two] <;> ring

/-- Pointwise bound on the normalised age-rate residual
`∑_i ‖a(r)⁻² * ((clockNC P ν t r i)⁻¹ * amplResidual_i(r))‖`
from the direct-error bound `δ` and the complement-coupling bound `γ`. -/
theorem sum_norm_age_amplResidual_le (κ : PlanarFrameKernels) (P : PlanarData)
    {ν m b K t r δ γ : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (w : ℝ → ℝ × ℝ → ℂ)
    (hν : 0 < ν) (ht : 0 ≤ t) (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hdecomp : ∀ i : Fin 2, movH0 κ tr r i (movingW ν w r) =
      (∑ j : Fin 2, ampl F w r j * movH0 κ tr r i (F.E r j)) + movH0 κ tr r i (compl F w r))
    (hdir : ∀ j : Fin 2, (∑ i : Fin 2, ‖amplDirectMat κ P F tr r i j‖) ≤ δ)
    (hcompl : (∑ i : Fin 2, ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖) ≤
      ENNReal.ofReal γ * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r)) :
    (∑ i : Fin 2,
      ENNReal.ofReal ‖(((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((clockNC P ν t r i)⁻¹ * amplResidual κ P F tr w r i)‖) ≤
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        (ENNReal.ofReal δ * (amplNorm F w r / ENNReal.ofReal (clockN P ν t r)) +
          ENNReal.ofReal γ *
            (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) /
              ENNReal.ofReal (clockN P ν t r))) := by
  have hN : 0 < clockN P ν t r := clockN_pos P hν ht hr
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  have ha2_nonneg : 0 ≤ (clockA ν r) ^ (-2 : ℝ) := Real.rpow_nonneg ha.le _
  have hR_sum : (∑ i : Fin 2, ‖amplResidual κ P F tr w r i‖) ≤
      δ * (∑ j : Fin 2, ‖ampl F w r j‖) +
        ∑ i : Fin 2, ‖movH0 κ tr r i (compl F w r)‖ := by
    have htri : ∀ i : Fin 2, ‖amplResidual κ P F tr w r i‖ ≤
        (∑ j : Fin 2, ‖ampl F w r j‖ * ‖amplDirectMat κ P F tr r i j‖) +
          ‖movH0 κ tr r i (compl F w r)‖ := by
      intro i
      rw [amplResidual_eq_sum_add κ P F tr w r i (hdecomp i)]
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_sum_le _ _).trans ?_
      simp only [norm_mul, le_rfl]
    have h0 := htri 0
    have h1 := htri 1
    have hd0 := hdir 0
    have hd1 := hdir 1
    simp only [Fin.sum_univ_two] at h0 h1 hd0 hd1 ⊢
    have hm0 : ‖ampl F w r 0‖ * (‖amplDirectMat κ P F tr r 0 0‖ + ‖amplDirectMat κ P F tr r 1 0‖) ≤
        ‖ampl F w r 0‖ * δ := mul_le_mul_of_nonneg_left hd0 (norm_nonneg _)
    have hm1 : ‖ampl F w r 1‖ * (‖amplDirectMat κ P F tr r 0 1‖ + ‖amplDirectMat κ P F tr r 1 1‖) ≤
        ‖ampl F w r 1‖ * δ := mul_le_mul_of_nonneg_left hd1 (norm_nonneg _)
    linarith
  have hofR : (∑ i : Fin 2, ENNReal.ofReal ‖amplResidual κ P F tr w r i‖) ≤
      ENNReal.ofReal δ * amplNorm F w r +
        ENNReal.ofReal γ * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) := by
    have heqL : (∑ i : Fin 2, ENNReal.ofReal ‖amplResidual κ P F tr w r i‖) =
        ENNReal.ofReal (∑ i : Fin 2, ‖amplResidual κ P F tr w r i‖) := by
      simp only [Fin.sum_univ_two, ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    have heqC : (∑ i : Fin 2, ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖) =
        ENNReal.ofReal (∑ i : Fin 2, ‖movH0 κ tr r i (compl F w r)‖) := by
      simp only [Fin.sum_univ_two, ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    have heqA : amplNorm F w r = ENNReal.ofReal (∑ j : Fin 2, ‖ampl F w r j‖) := by
      unfold amplNorm
      simp only [Fin.sum_univ_two, ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    rw [heqL, heqA, ← ENNReal.ofReal_mul hδ]
    calc ENNReal.ofReal (∑ i : Fin 2, ‖amplResidual κ P F tr w r i‖)
        ≤ ENNReal.ofReal (δ * (∑ j : Fin 2, ‖ampl F w r j‖) +
            ∑ i : Fin 2, ‖movH0 κ tr r i (compl F w r)‖) :=
          ENNReal.ofReal_le_ofReal hR_sum
      _ = ENNReal.ofReal (δ * ∑ j : Fin 2, ‖ampl F w r j‖) +
            (∑ i : Fin 2, ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), heqC]
      _ ≤ ENNReal.ofReal (δ * ∑ j : Fin 2, ‖ampl F w r j‖) +
            ENNReal.ofReal γ * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) :=
          add_le_add le_rfl hcompl
  have hmode_eq : ∀ i : Fin 2,
      ENNReal.ofReal ‖(((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((clockNC P ν t r i)⁻¹ * amplResidual κ P F tr w r i)‖ =
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        (ENNReal.ofReal ‖amplResidual κ P F tr w r i‖ / ENNReal.ofReal (clockN P ν t r)) := by
    intro i
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg ha2_nonneg, norm_clockNC_inv P hν ht hr i,
      inv_mul_eq_div, ENNReal.ofReal_mul ha2_nonneg, ENNReal.ofReal_div_of_pos hN]
  have hsum_eq :
      (∑ i : Fin 2,
        ENNReal.ofReal ‖(((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
          ((clockNC P ν t r i)⁻¹ * amplResidual κ P F tr w r i)‖) =
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        ((∑ i : Fin 2, ENNReal.ofReal ‖amplResidual κ P F tr w r i‖) /
          ENNReal.ofReal (clockN P ν t r)) := by
    simp only [Fin.sum_univ_two, hmode_eq, ← mul_add, ENNReal.div_add_div_same]
  rw [hsum_eq]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have hdiv_le := ENNReal.div_le_div_right hofR (ENNReal.ofReal (clockN P ν t r))
  rwa [ENNReal.add_div, mul_div_assoc, mul_div_assoc] at hdiv_le

theorem ofReal_norm_setIntegral_le_lintegral (g : ℝ → ℂ) (S : Set ℝ) :
    ENNReal.ofReal ‖∫ r in S, g r‖ ≤ ∫⁻ r in S, ENNReal.ofReal ‖g r‖ := by
  simpa only [ofReal_norm] using
    (enorm_integral_le_lintegral_enorm g (μ := volume.restrict S))

end FrameAmplSub

open FrameAmplSub

/-! ## Conditional assembly of `FrameAmplitudeAll` -/

/-- Assembly of `FrameAmplitudeAll κ` from the three leaves (`AmplWeakFTC`, `AmplDirectError`,
`AmplComplCoupling`). -/
theorem frameAmplitudeAll_of (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ)
    (hFTC : AmplWeakFTC κ)
    (hDir : AmplDirectError κ)
    (hCompl : AmplComplCoupling κ) :
    FrameAmplitudeAll κ := by
  intro P hP m hm K
  obtain ⟨b₀, _hb₀, hFTCB⟩ := hFTC hκ P hP m hm K
  obtain ⟨C₁, b₁, hC₁, _hb₁, hDirB⟩ := hDir hκ P hP m hm K
  obtain ⟨C₂, b₂, hC₂, _hb₂, hComplB⟩ := hCompl hκ m hm K
  set C₀ := max 1 (max C₁ C₂)
  have hC₀_pos : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hC₁_le : C₁ ≤ C₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC₂_le : C₂ ≤ C₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C₀, max b₀ (max b₁ b₂), fun C hC b hb => ?_⟩
  have hb₀' : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hb₁' : b₁ ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have hb₂' : b₂ ≤ b := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hb
  obtain ⟨ν₀, hν₀, H0⟩ := hFTCB b hb₀'
  obtain ⟨ν₁, hν₁, H1⟩ := hDirB b hb₁'
  obtain ⟨ν₂, hν₂, H2⟩ := hComplB b hb₂'
  refine ⟨min ν₀ (min ν₁ ν₂), lt_min hν₀ (lt_min hν₁ hν₂), fun ν hν hF => ?_⟩
  have hνpos : 0 < ν := hν.1
  have hν_0 : ν ∈ Ioc 0 ν₀ := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν_1 : ν ∈ Ioc 0 ν₁ :=
    ⟨hν.1, hν.2.trans (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hν_2 : ν ∈ Ioc 0 ν₂ :=
    ⟨hν.1, hν.2.trans (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hC_abs : |C₀| ≤ C := by rwa [abs_of_pos hC₀_pos]
  refine frameAmp_mono P (periodizedFrame κ ν m b K hν.1 hF) hνpos hC_abs ?_
  intro tr htr t s ht hts hbs f w u hw hz
  set F := periodizedFrame κ ν m b K hν.1 hF
  have hs0 : 0 ≤ s := ht.trans hts
  obtain ⟨hmR, hInt, hDecomp⟩ := H0 ν hν_0 hF tr htr t s ht hts hbs f w u hw hz
  let g : Fin 2 → ℝ → ℂ := fun i r =>
    (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
      ((clockNC P ν t r i)⁻¹ * amplResidual κ P F tr w r i)
  have hgm : ∀ i : Fin 2,
      AEMeasurable (fun r => ENNReal.ofReal ‖g i r‖) (volume.restrict (Ioc t s)) := by
    intro i
    have ha_cont : ContinuousOn (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ)) (Ioc t s) := by
      have hc1 : ContinuousOn (clockA ν) (Ioc t s) := by
        unfold clockA
        exact continuousOn_const.add (continuousOn_const.mul continuousOn_id)
      have hc2 : ContinuousOn (fun r => (clockA ν r) ^ (-2 : ℝ)) (Ioc t s) :=
        hc1.rpow_const (fun r hr => Or.inl (by
          have := one_le_clockA hνpos.le (ht.trans hr.1.le)
          linarith))
      exact Complex.continuous_ofReal.comp_continuousOn hc2
    have hNC : AEMeasurable (fun r => (clockNC P ν t r i)⁻¹) (volume.restrict (Ioc t s)) :=
      (continuousOn_clockNC_inv P hνpos ht i).aemeasurable measurableSet_Ioc
    have ha_m : AEMeasurable (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ))
        (volume.restrict (Ioc t s)) :=
      ha_cont.aemeasurable measurableSet_Ioc
    exact ENNReal.measurable_ofReal.comp_aemeasurable (ha_m.mul (hNC.mul (hmR i))).norm
  -- Bound normAmpl at s for each mode i : Fin 2
  have hmode_bound : ∀ i : Fin 2,
      ENNReal.ofReal ‖normAmpl F P t w s i‖ ≤
        ENNReal.ofReal ‖ampl F w t i‖ + ∫⁻ r in Ioc t s, ENNReal.ofReal ‖g i r‖ := by
    intro i
    have heq : normAmpl F P t w s i = ampl F w t i + ∫ r in Ioc t s, g i r := by
      have hsub := hInt i
      rw [normAmpl_self F P hνpos ht w i] at hsub
      exact sub_eq_iff_eq_add'.1 hsub
    have htri : ‖normAmpl F P t w s i‖ ≤ ‖ampl F w t i‖ + ‖∫ r in Ioc t s, g i r‖ := by
      rw [heq]
      exact norm_add_le _ _
    calc ENNReal.ofReal ‖normAmpl F P t w s i‖
        ≤ ENNReal.ofReal (‖ampl F w t i‖ + ‖∫ r in Ioc t s, g i r‖) :=
          ENNReal.ofReal_le_ofReal htri
      _ = ENNReal.ofReal ‖ampl F w t i‖ + ENNReal.ofReal ‖∫ r in Ioc t s, g i r‖ :=
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
      _ ≤ ENNReal.ofReal ‖ampl F w t i‖ + ∫⁻ r in Ioc t s, ENNReal.ofReal ‖g i r‖ :=
          add_le_add le_rfl (ofReal_norm_setIntegral_le_lintegral (g i) (Ioc t s))
  -- Sum over i : Fin 2
  have hsum_s : amplNorm F w s / ENNReal.ofReal (clockN P ν t s) ≤
      amplNorm F w t + ∫⁻ r in Ioc t s, (∑ i : Fin 2, ENNReal.ofReal ‖g i r‖) := by
    rw [← sum_ofReal_norm_normAmpl F P hνpos ht hs0 w]
    have h0 := hmode_bound 0
    have h1 := hmode_bound 1
    have hlsum : (∫⁻ r in Ioc t s, ENNReal.ofReal ‖g 0 r‖) +
          (∫⁻ r in Ioc t s, ENNReal.ofReal ‖g 1 r‖) =
        ∫⁻ r in Ioc t s, (∑ i : Fin 2, ENNReal.ofReal ‖g i r‖) := by
      simp only [Fin.sum_univ_two]
      exact (lintegral_add_left' (hgm 0) _).symm
    have hAt : amplNorm F w t = ENNReal.ofReal ‖ampl F w t 0‖ + ENNReal.ofReal ‖ampl F w t 1‖ := by
      unfold amplNorm
      simp only [Fin.sum_univ_two]
    have hAs : (∑ i : Fin 2, ENNReal.ofReal ‖normAmpl F P t w s i‖) =
        ENNReal.ofReal ‖normAmpl F P t w s 0‖ + ENNReal.ofReal ‖normAmpl F P t w s 1‖ :=
      Fin.sum_univ_two _
    rw [hAs]
    calc ENNReal.ofReal ‖normAmpl F P t w s 0‖ + ENNReal.ofReal ‖normAmpl F P t w s 1‖
        ≤ (ENNReal.ofReal ‖ampl F w t 0‖ + ∫⁻ r in Ioc t s, ENNReal.ofReal ‖g 0 r‖) +
            (ENNReal.ofReal ‖ampl F w t 1‖ + ∫⁻ r in Ioc t s, ENNReal.ofReal ‖g 1 r‖) :=
          add_le_add h0 h1
      _ = (ENNReal.ofReal ‖ampl F w t 0‖ + ENNReal.ofReal ‖ampl F w t 1‖) +
            ((∫⁻ r in Ioc t s, ENNReal.ofReal ‖g 0 r‖) +
              (∫⁻ r in Ioc t s, ENNReal.ofReal ‖g 1 r‖)) := by ring
      _ = amplNorm F w t + ∫⁻ r in Ioc t s, (∑ i : Fin 2, ENNReal.ofReal ‖g i r‖) := by
          rw [← hAt, hlsum]
  -- Pointwise bound on Ioc t s
  have hlint_le : (∫⁻ r in Ioc t s, (∑ i : Fin 2, ENNReal.ofReal ‖g i r‖)) ≤
      ∫⁻ r in Ioc t s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        (ENNReal.ofReal (C₀ * ν ^ 3 / clockTheta ν r) *
            (amplNorm F w r / ENNReal.ofReal (clockN P ν t r)) +
          ENNReal.ofReal (C₀ * (1 / clockTheta ν r + C₀ * ν ^ 3 / clockTheta ν r)) *
            (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) /
              ENNReal.ofReal (clockN P ν t r))) := by
    refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
    have hr0 : 0 ≤ r := ht.trans hr.1.le
    have hθr : 0 < clockTheta ν r := theta_pos hνpos hr0
    have hθr_ge_s : clockTheta ν s ≤ clockTheta ν r := theta_anti hνpos hr0 hr.2
    have hbr : b ≤ clockTheta ν r := hbs.trans hθr_ge_s
    have hδr : 0 ≤ C₀ * ν ^ 3 / clockTheta ν r := div_nonneg (by positivity) hθr.le
    have hdir_r : ∀ j : Fin 2,
        (∑ i : Fin 2, ‖amplDirectMat κ P F tr r i j‖) ≤ C₀ * ν ^ 3 / clockTheta ν r := by
      intro j
      refine (H1 ν hν_1 hF tr htr r hr0 hbr j).trans ?_
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC₁_le (by positivity)) hθr.le
    have hcompl_r : (∑ i : Fin 2, ENNReal.ofReal ‖movH0 κ tr r i (compl F w r)‖) ≤
        ENNReal.ofReal (C₀ * (1 / clockTheta ν r + C₀ * ν ^ 3 / clockTheta ν r)) *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r) := by
      refine (H2 ν hν_2 hF tr htr t s ht hts hbs f w u hw hz r hr).trans ?_
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
      have h1 : C₂ * (1 / clockTheta ν r) ≤ C₀ * (1 / clockTheta ν r) :=
        mul_le_mul_of_nonneg_right hC₂_le (by positivity)
      have h2 : 0 ≤ C₀ * (C₀ * ν ^ 3 / clockTheta ν r) := by positivity
      linarith
    exact sum_norm_age_amplResidual_le κ P F tr w hνpos ht hr0 hδr
      (hDecomp r hr) hdir_r hcompl_r
  exact hsum_s.trans (add_le_add le_rfl hlint_le)

end UnforcedLeray.Short.IIIa
