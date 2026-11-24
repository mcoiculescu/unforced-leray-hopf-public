import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5

/-!
# Part III-a, task `PartIII-a:T21/c3/3` decomposition (`Sub/PartIII-a_T21_c3_3.lean`, SP 2898-2962, 2982-2988)

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2962 and
2982-2988 (`eq:short-causal-damped-complement`, `eq:short-causal-free-moving`,
`eq:short-causal-stable-moving`).

## Mathematical structure and leaf decomposition

For the periodized frame `F = periodizedFrame κ ν m b K hν.1 hF` built from a Part I seed kernel
`κ` (`IsSeedKernels κ`), on any short moving block `[t₁, t₂]` of moving length
`0 ≤ movingZ ν t₂ - movingZ ν t₁ ≤ B` with `b ≤ clockTheta ν t₂`:

1. **Moving-time, normaliser, and complement-projection lemmas (proved here in `FrameShortBlockSub`)**:
   * `clockTheta_sub_eq_movingZ_sub`: `clockTheta ν u - clockTheta ν r = movingZ ν r - movingZ ν u`.
   * `hasDerivAt_movingZ`, `integral_clockA_inv_sq_eq`, `lintegral_clockA_inv_sq_eq`:
     `(d/dr) movingZ ν r = (clockA ν r) ^ (-2 : ℝ)` and
     `∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) = ENNReal.ofReal (movingZ ν t₂ - movingZ ν t₁)`.
   * `exp_neg_le_clockN`, `exp_mul_le_clockN_mul_exp`: for `0 ≤ u ≤ r` and `1 ≤ b ≤ clockTheta ν r`,
     `clockTheta ν u / clockTheta ν r ≤ Real.exp (movingZ ν r - movingZ ν u)` implies
     `Real.exp (-(|P.eigenvalue.re| + |P.kappa.re|) * (movingZ ν r - movingZ ν u)) ≤ clockN P ν u r`,
     and hence for any raw moving-time growth rate `μ_raw`,
     `Real.exp (μ_raw * (movingZ ν r - movingZ ν u)) ≤ clockN P ν u r * Real.exp ((μ_raw + |P.eigenvalue.re| + |P.kappa.re|) * (movingZ ν r - movingZ ν u))`.
   * `frameProj`: the moving complement projection
     `frameProj F r Ψ y = Ψ y - ∑ i : Fin 2, (∫ x in movingCell ν c r, F.lam r i x * Ψ x) * F.E r i y`
     satisfies `frameProj_E_eq_zero` (`frameProj F r (F.E r j) y = 0` by `F.dual`) and the uniform
     operator bound `xNorm_frameProj_le`:
     `xNorm d(r) m (frameProj F r Ψ) ≤ ENNReal.ofReal (1 + 2 * max K 0 ^ 2) * xNorm d(r) m Ψ`.
   * `movD`, `kerVelCx`, `movL`, `movEz`, `movOscRes`, `movEulerRes`, `complModeForce`: the moving
     operators and mode-to-complement forcing profiles `(1 - E Λ)(G(r) E_j - ∂_z E_j)`, with the
     proved norm bound `xNorm_complModeForce_le` and sum bound `sum_ampl_complModeForce_le`.

2. **Three analytical leaves**:
   * `ComplModeForceOscillator` (`PartIII-a:T21/c3/3/2`, SP 2905): the oscillator/cell-length drift
     residual `movOscRes κ ν r j = θ(r)⁻¹ D(P_{d(r)} e_j) - ∂_z(P_{d(r)} e_j) = θ(r)⁻¹ P_{d(r)}(D e_j)`
     is bounded in `X_{m,d(r)}` by `C₁ / clockTheta ν r`.
   * `ComplModeForceEulerError` (`PartIII-a:T21/c3/3/3`, SP 2866-2888, 2991-2995): the periodized
     linearised Euler eigenmode defect `movEulerRes κ P tr r j = L_{ν,c}(r) E_j - λ_j E_j` is
     bounded in `X_{m,d(r)}` by `C₂ * ν ^ 3 / clockTheta ν r`.
   * `ShortComplPerturbDuhamel` (`PartIII-a:T21/c3/3/1`, SP 2919-2925, 2937-2958, 2982-2988):
     combining `FreeMovingEnergy` (`freeMovingEnergy`), `ComplModeForceOscillator`, and
     `ComplModeForceEulerError` with the uniform `X_{m,d(r)}` boundedness of the localized
     interaction `L_{int,d}` and finite-rank coupling `-E H_0` yields a raw growth rate
     `μ_raw = normGrowthConst m + 1 + C_pert` and the variation-of-constants / Gronwall inequality
     for `xNorm d(t₂) m (compl F w t₂)` forced by `complModeForce κ P F tr r j`.

3. **Proved assembly (`frameShortBlockBound_of`)**:
   Combines `freeMovingEnergy` (`Clock/FreeMoving.lean`), `ShortComplPerturbDuhamel`,
   `ComplModeForceOscillator`, and `ComplModeForceEulerError` with `exp_mul_le_clockN_mul_exp`,
   `ofReal_clockN_mul`, and `lintegral_clockA_inv_sq_eq` to establish `FrameShortBlockBound κ`
   with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## Moving complement projection and mode-to-complement forcing operators (SP 2862-2925) -/

/-- The moving complement projection `(1 - E(r) Λ(r)) Ψ` on the cell of length `d(r) = c / √a(r)`
(SP 2916-2925, 2991). -/
def frameProj {ν c m b K : ℝ} (F : MovingFrame ν c m b K) (r : ℝ)
    (Ψ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  Ψ y - ∑ i : Fin 2, (∫ x in movingCell ν c r, F.lam r i x * Ψ x) * F.E r i y

/-- The self-similar oscillator generator `D W = Δ W + ½ y · ∇ W + 2 W` in moving coordinates
(SP 2863). -/
def movD (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  ladLapCx W y +
    ((2 : ℂ)⁻¹ * (((y.1 : ℝ) : ℂ) * pdCx 0 W y + ((y.2 : ℝ) : ℂ) * pdCx 1 W y)) +
    (2 : ℂ) * W y

/-- Complex extension of the periodic Biot-Savart velocity `K_d W` on the cell of length `d`
(SP 2864, 2876-2881). -/
def kerVelCx (d : ℝ) (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) (k : Fin 2) : ℂ :=
  ∫ z in B0579.cell d, W z * ((kerD d (y - z) k : ℝ) : ℂ)

/-- Rescaled actual-train vorticity gradient `∇_y E_mov(r, y) = a(r)^{5/2} (∇ E)(r, √a(r) y)`
in moving coordinates (SP 2861-2873). -/
def movingTrainGradE {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ)
    (y : ℝ × ℝ) (k : Fin 2) : ℝ :=
  clockA ν r ^ ((5 : ℝ) / 2) *
    B0579.pd k (UnforcedLeray.B0238.Ec tr r)
      (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)

/-- Moving linearised Euler operator `L_{ν,c}(r) W = -V(r) · ∇ W - (K_{d(r)} W) · ∇ E_mov(r)`
along the actual train `tr` (SP 2863-2865). -/
def movL {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ)
    (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  -(((movingTrainV tr r y 0 : ℝ) : ℂ) * pdCx 0 W y +
      ((movingTrainV tr r y 1 : ℝ) : ℂ) * pdCx 1 W y) -
    (kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) W y 0 *
        ((movingTrainGradE tr r y 0 : ℝ) : ℂ) +
      kerVelCx (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) W y 1 *
        ((movingTrainGradE tr r y 1 : ℝ) : ℂ))

/-- Moving-time derivative `∂_z E_j = a(r)² ∂_r (perE κ d(r) j)` of the periodized growing mode
(SP 2905). -/
def movEz (κ : PlanarFrameKernels) (ν r : ℝ) (j : Fin 2) (y : ℝ × ℝ) : ℂ :=
  (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
    ladDt (fun r' y' => perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) j y') r y

/-- Oscillator / cell-length drift residual on mode `j`:
`θ(r)⁻¹ D(E_j) - ∂_z E_j = θ(r)⁻¹ P_{d(r)}(D e_j)` (SP 2905). -/
def movOscRes (κ : PlanarFrameKernels) (ν r : ℝ) (j : Fin 2) (y : ℝ × ℝ) : ℂ :=
  ((clockTheta ν r : ℂ)⁻¹ *
      movD (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y) -
    movEz κ ν r j y

/-- Linearised Euler eigenmode defect on mode `j`:
`L_{ν,c}(r) E_j - λ_j E_j` (SP 2866-2888, 2991-2995). -/
def movEulerRes (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (j : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  movL tr r (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j) y -
    modeEigen P j * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y

/-- Mode-`j` forcing profile into the complement equation:
`(1 - E(r) Λ(r)) (movOscRes κ ν r j + movEulerRes κ P tr r j)` (SP 2916-2925, 2991-2997). -/
def complModeForce (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r : ℝ) (j : Fin 2)
    (y : ℝ × ℝ) : ℂ :=
  frameProj F r (fun y' => movOscRes κ ν r j y' + movEulerRes κ P tr r j y') y

/-! ## The three analytical leaves of `FrameShortBlockBound` -/

/-- **Leaf 2 (`ComplModeForceOscillator`, `PartIII-a:T21/c3/3/2`, SP 2905)**: the oscillator and
cell-length drift residual `movOscRes κ ν r j = θ(r)⁻¹ P_{d(r)}(D e_j)` is a.e. strongly measurable
and bounded in `X_{m,d(r)}` by `C₁ / clockTheta ν r`.
Composed by task `PartIII-a:T21/c3/3` via `frameShortBlockBound_of` (and reused by
`PartIII-a:T21/c3/2` via `frameBlockContraction_of`). -/
def ComplModeForceOscillator (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ m : ℝ, 8 < m →
  ∃ C₁ b₁ : ℝ, 0 ≤ C₁ ∧ 1 ≤ b₁ ∧
    ∀ b : ℝ, b₁ ≤ b →
      ∃ ν₁ : ℝ, 0 < ν₁ ∧
        ∀ ν ∈ Ioc 0 ν₁, ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r → ∀ j : Fin 2,
          AEStronglyMeasurable (movOscRes κ ν r j)
            (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) ∧
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movOscRes κ ν r j) ≤
            ENNReal.ofReal (C₁ / clockTheta ν r)

/-- **Leaf 3 (`ComplModeForceEulerError`, `PartIII-a:T21/c3/3/3`, SP 2866-2888, 2991-2995)**: the
linearised Euler eigenmode defect `movEulerRes κ P tr r j = L_{ν,c}(r) E_j - λ_j E_j` is a.e.
strongly measurable and bounded in `X_{m,d(r)}` by `C₂ * ν ^ 3 / clockTheta ν r`.
Composed by task `PartIII-a:T21/c3/3` via `frameShortBlockBound_of` (and reused by
`PartIII-a:T21/c3/2` via `frameBlockContraction_of`). -/
def ComplModeForceEulerError (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∃ C₂ b₂ : ℝ, 0 ≤ C₂ ∧ 1 ≤ b₂ ∧
    ∀ b : ℝ, b₂ ≤ b →
      ∃ ν₂ : ℝ, 0 < ν₂ ∧
        ∀ ν ∈ Ioc 0 ν₂,
          ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
            UnforcedLeray.Short.PartI.IsBUCTrain tr →
            ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r → ∀ j : Fin 2,
              AEStronglyMeasurable (movEulerRes κ P tr r j)
                (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) ∧
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movEulerRes κ P tr r j) ≤
                ENNReal.ofReal (C₂ * ν ^ 3 / clockTheta ν r)

/-- **Leaf 1 (`ShortComplPerturbDuhamel`, `PartIII-a:T21/c3/3/1`, SP 2919-2925, 2937-2958,
2982-2988)**: assuming `FreeMovingEnergy`, the boundedness in `X_{m,d(r)}` of the localized
interaction `L_{int,d}` and finite-rank coupling `-E H_0` yields `C_pert ≥ 0` such that along any
weak linearised flow `IsLinearisedFlow` with `HasZeroCirculation`, the complement `compl F w`
satisfies the variation-of-constants / Gronwall inequality on `[t₁, t₂]` with raw moving-time growth
rate `μ_raw = normGrowthConst m + 1 + C_pert` and mode forcing `complModeForce κ P F tr r j`.
Composed by task `PartIII-a:T21/c3/3` via `frameShortBlockBound_of`. -/
def ShortComplPerturbDuhamel (κ : PlanarFrameKernels) : Prop :=
  FreeMovingEnergy →
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∃ C_pert b₀ : ℝ, 0 ≤ C_pert ∧ 1 ≤ b₀ ∧
    ∀ b : ℝ, b₀ ≤ b →
      ∃ ν₀ : ℝ, 0 < ν₀ ∧
        ∀ ν (hν : ν ∈ Ioc 0 ν₀), ∀ hF : PerFrameFacts κ ν m b K,
          ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
            UnforcedLeray.Short.PartI.IsBUCTrain tr →
            ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
              ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
                HasZeroCirculation (ν ^ (-2 : ℝ)) f →
                let F := periodizedFrame κ ν m b K hν.1 hF
                let μ_raw := normGrowthConst m + 1 + C_pert
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂) ≤
                  ENNReal.ofReal (Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁))) *
                      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) +
                    ∫⁻ r in Ioc t₁ t₂,
                      ENNReal.ofReal
                          ((clockA ν r) ^ (-2 : ℝ) *
                            Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) *
                        (∑ j : Fin 2,
                          ENNReal.ofReal ‖ampl F w r j‖ *
                            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                              (complModeForce κ P F tr r j))

namespace FrameShortBlockSub

/-! ## Moving-time, clock, and normaliser identities -/

/-- Exact identity `clockTheta ν u - clockTheta ν r = movingZ ν r - movingZ ν u` (SP 2855:
`z = ν⁻¹ - θ`). -/
theorem clockTheta_sub_eq_movingZ_sub {ν u r : ℝ} (hν : 0 < ν) (hu : 0 ≤ u) (hr : 0 ≤ r) :
    clockTheta ν u - clockTheta ν r = movingZ ν r - movingZ ν u := by
  have ha_u : 0 < clockA ν u := by unfold clockA; positivity
  have ha_r : 0 < clockA ν r := by unfold clockA; positivity
  unfold clockTheta movingZ clockA
  field_simp [hν.ne', ha_u.ne', ha_r.ne']
  ring

/-- Age derivative of moving time `movingZ ν`: `(d/dr) movingZ ν r = (clockA ν r) ^ (-2 : ℝ)`
(SP 2858). -/
theorem hasDerivAt_movingZ {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    HasDerivAt (movingZ ν) ((clockA ν r) ^ (-2 : ℝ)) r := by
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  have h1 : HasDerivAt (clockA ν) ν r := FrameAmplSub.hasDerivAt_clockA ν r
  have h2 : HasDerivAt (movingZ ν) ((1 * clockA ν r - r * ν) / (clockA ν r) ^ 2) r :=
    (hasDerivAt_id r).div h1 ha.ne'
  refine h2.congr_deriv ?_
  rw [Real.rpow_neg ha.le, Real.rpow_two, ← one_div]
  unfold clockA
  field_simp [ha.ne']
  ring

/-- Set integral of `(clockA ν r) ^ (-2 : ℝ)` on `Ioc t₁ t₂` equals `movingZ ν t₂ - movingZ ν t₁`. -/
theorem integral_clockA_inv_sq_eq {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    ∫ r in Ioc t₁ t₂, (clockA ν r) ^ (-2 : ℝ) = movingZ ν t₂ - movingZ ν t₁ := by
  rw [← intervalIntegral.integral_of_le h12]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => ?_) ?_
  · rw [uIcc_of_le h12] at hr
    exact hasDerivAt_movingZ hν (ht₁.trans hr.1)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le h12]
    refine ContinuousOn.integrableOn_Icc ?_
    have hc1 : ContinuousOn (clockA ν) (Icc t₁ t₂) := by
      unfold clockA
      exact continuousOn_const.add (continuousOn_const.mul continuousOn_id)
    exact hc1.rpow_const (fun r hr => Or.inl (by
      have := one_le_clockA hν.le (ht₁.trans hr.1)
      linarith))

/-- Lebesgue integral of `ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ))` on `Ioc t₁ t₂` equals
`ENNReal.ofReal (movingZ ν t₂ - movingZ ν t₁)`. -/
theorem lintegral_clockA_inv_sq_eq {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    ∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) =
      ENNReal.ofReal (movingZ ν t₂ - movingZ ν t₁) := by
  have hint : IntegrableOn (fun r => (clockA ν r) ^ (-2 : ℝ)) (Ioc t₁ t₂) := by
    refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
    refine ContinuousOn.integrableOn_Icc ?_
    have hc1 : ContinuousOn (clockA ν) (Icc t₁ t₂) := by
      unfold clockA
      exact continuousOn_const.add (continuousOn_const.mul continuousOn_id)
    exact hc1.rpow_const (fun r hr => Or.inl (by
      have := one_le_clockA hν.le (ht₁.trans hr.1)
      linarith))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc t₁ t₂)] (fun r => (clockA ν r) ^ (-2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have ha : 0 < clockA ν r := by
      have := one_le_clockA hν.le (ht₁.trans hr.1.le)
      linarith
    exact (Real.rpow_pos_of_pos ha _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg, integral_clockA_inv_sq_eq hν ht₁ h12]

/-- Exponential lower bound on `clockN P ν u r` for `0 ≤ u ≤ r` and `1 ≤ clockTheta ν r`:
`Real.exp (-(|P.eigenvalue.re| + |P.kappa.re|) * (movingZ ν r - movingZ ν u)) ≤ clockN P ν u r`. -/
theorem exp_neg_le_clockN (P : PlanarData) {ν u r : ℝ} (hν : 0 < ν) (hu : 0 ≤ u) (hur : u ≤ r)
    (hθ1 : 1 ≤ clockTheta ν r) :
    Real.exp (-(|P.eigenvalue.re| + |P.kappa.re|) * (movingZ ν r - movingZ ν u)) ≤
      clockN P ν u r := by
  have hr : 0 ≤ r := hu.trans hur
  have hθu : 0 < clockTheta ν u := theta_pos hν hu
  have hθr : 0 < clockTheta ν r := theta_pos hν hr
  have hθ_le : clockTheta ν r ≤ clockTheta ν u := theta_anti hν hu hur
  have hz_eq : clockTheta ν u - clockTheta ν r = movingZ ν r - movingZ ν u :=
    clockTheta_sub_eq_movingZ_sub hν hu hr
  have hz_nonneg : 0 ≤ movingZ ν r - movingZ ν u := by linarith
  set Δz := movingZ ν r - movingZ ν u
  set q := clockTheta ν u / clockTheta ν r
  have hq1 : 1 ≤ q := (one_le_div hθr).2 hθ_le
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hq_exp : q ≤ Real.exp Δz := by
    have hq_split : q = 1 + Δz / clockTheta ν r := by
      simp only [q, Δz, ← hz_eq]
      rw [one_add_div hθr.ne']
      ring
    have hdiv_le : Δz / clockTheta ν r ≤ Δz := div_le_self hz_nonneg hθ1
    calc q = 1 + Δz / clockTheta ν r := hq_split
      _ ≤ 1 + Δz := by linarith
      _ ≤ Real.exp Δz := by linarith [Real.add_one_le_exp Δz]
  have hexp_eig :
      Real.exp (-|P.eigenvalue.re| * Δz) ≤
        Real.exp (P.eigenvalue.re * (clockTheta ν u - clockTheta ν r)) := by
    rw [hz_eq]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_abs_le P.eigenvalue.re) hz_nonneg)
  have hrpow_kap : Real.exp (-|P.kappa.re| * Δz) ≤ q ^ P.kappa.re := by
    have h1 : q ^ (-|P.kappa.re|) ≤ q ^ P.kappa.re :=
      Real.rpow_le_rpow_of_exponent_le hq1 (neg_abs_le P.kappa.re)
    have h2 : q ^ |P.kappa.re| ≤ Real.exp (|P.kappa.re| * Δz) := by
      calc q ^ |P.kappa.re| ≤ (Real.exp Δz) ^ |P.kappa.re| :=
            Real.rpow_le_rpow hq0.le hq_exp (abs_nonneg _)
        _ = Real.exp (|P.kappa.re| * Δz) := by
            rw [← Real.exp_mul, mul_comm]
    have h3 : Real.exp (-|P.kappa.re| * Δz) ≤ q ^ (-|P.kappa.re|) := by
      rw [neg_mul, Real.exp_neg, Real.rpow_neg hq0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hq0 _) h2
    exact h3.trans h1
  unfold clockN
  calc Real.exp (-(|P.eigenvalue.re| + |P.kappa.re|) * Δz)
      = Real.exp (-|P.eigenvalue.re| * Δz) * Real.exp (-|P.kappa.re| * Δz) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (P.eigenvalue.re * (clockTheta ν u - clockTheta ν r)) * q ^ P.kappa.re :=
        mul_le_mul hexp_eig hrpow_kap (Real.exp_pos _).le (Real.exp_pos _).le

/-- Relating a raw moving-time exponential `Real.exp (μ_raw * (movingZ ν r - movingZ ν u))` to
`clockN P ν u r`:
`Real.exp (μ_raw * Δz) ≤ clockN P ν u r * Real.exp ((μ_raw + |P.eigenvalue.re| + |P.kappa.re|) * Δz)`. -/
theorem exp_mul_le_clockN_mul_exp (P : PlanarData) {ν u r : ℝ} (μ_raw : ℝ)
    (hν : 0 < ν) (hu : 0 ≤ u) (hur : u ≤ r) (hθ1 : 1 ≤ clockTheta ν r) :
    Real.exp (μ_raw * (movingZ ν r - movingZ ν u)) ≤
      clockN P ν u r *
        Real.exp ((μ_raw + |P.eigenvalue.re| + |P.kappa.re|) * (movingZ ν r - movingZ ν u)) := by
  set Δz := movingZ ν r - movingZ ν u
  have h1 := exp_neg_le_clockN P hν hu hur hθ1
  calc Real.exp (μ_raw * Δz)
      = Real.exp (-(|P.eigenvalue.re| + |P.kappa.re|) * Δz) *
          Real.exp ((μ_raw + |P.eigenvalue.re| + |P.kappa.re|) * Δz) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ clockN P ν u r * Real.exp ((μ_raw + |P.eigenvalue.re| + |P.kappa.re|) * Δz) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

/-! ## Properties of the moving complement projection `frameProj` -/

/-- `compl F w r` is `frameProj F r (movingW ν w r)`. -/
theorem compl_eq_frameProj {ν c m b K : ℝ} (F : MovingFrame ν c m b K)
    (w : ℝ → ℝ × ℝ → ℂ) (r : ℝ) :
    compl F w r = frameProj F r (movingW ν w r) := rfl

/-- Biorthogonality `F.dual` implies `frameProj F r (F.E r j) = 0`. -/
theorem frameProj_E_eq_zero {ν c m b K : ℝ} (F : MovingFrame ν c m b K) {r : ℝ}
    (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r) (j : Fin 2) (y : ℝ × ℝ) :
    frameProj F r (F.E r j) y = 0 := by
  unfold frameProj
  simp only [F.dual r hr hbr _ j, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, sub_self]

/-- `frameProj F r` preserves `AEStronglyMeasurable` with respect to `cellMeasure`. -/
theorem aesm_frameProj {ν c m b K : ℝ} (F : MovingFrame ν c m b K) {r : ℝ}
    (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r) {Ψ : ℝ × ℝ → ℂ}
    (hΨ : AEStronglyMeasurable Ψ (B0579.cellMeasure (cellLen c (clockA ν r)) m)) :
    AEStronglyMeasurable (frameProj F r Ψ) (B0579.cellMeasure (cellLen c (clockA ν r)) m) := by
  have hE : ∀ i : Fin 2, AEStronglyMeasurable (F.E r i)
      (B0579.cellMeasure (cellLen c (clockA ν r)) m) :=
    fun i => (F.E_meas r hr hbr i).mono_ac (B0579.cellMeasure_ac _ _)
  exact hΨ.sub (aesm_sum_smul (fun i => ∫ x in movingCell ν c r, F.lam r i x * Ψ x) (F.E r) hE)

/-- Uniform `X_{m,d(r)}` operator norm bound for `frameProj F r`:
`xNorm d(r) m (frameProj F r Ψ) ≤ ENNReal.ofReal (1 + 2 * max K 0 ^ 2) * xNorm d(r) m Ψ`. -/
theorem xNorm_frameProj_le {ν c m b K : ℝ} (F : MovingFrame ν c m b K) {r : ℝ}
    (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r) {Ψ : ℝ × ℝ → ℂ}
    (hΨ : AEStronglyMeasurable Ψ (B0579.cellMeasure (cellLen c (clockA ν r)) m)) :
    xNorm (cellLen c (clockA ν r)) m (frameProj F r Ψ) ≤
      ENNReal.ofReal (1 + 2 * max K 0 ^ 2) * xNorm (cellLen c (clockA ν r)) m Ψ := by
  set Kp := max K 0
  have hK0 : 0 ≤ Kp := le_max_right K 0
  have hKle : ENNReal.ofReal K ≤ ENNReal.ofReal Kp := ENNReal.ofReal_le_ofReal (le_max_left K 0)
  have hE : ∀ i : Fin 2, AEStronglyMeasurable (F.E r i)
      (B0579.cellMeasure (cellLen c (clockA ν r)) m) :=
    fun i => (F.E_meas r hr hbr i).mono_ac (B0579.cellMeasure_ac _ _)
  have hEb : ∀ i : Fin 2, eLpNorm (F.E r i) 2
      (B0579.cellMeasure (cellLen c (clockA ν r)) m) ≤ ENNReal.ofReal Kp :=
    fun i => (F.E_bdd r hr hbr i).trans hKle
  have hsub := eLpNorm_sub_sum_le
    (W := Ψ) (fun i => ∫ x in movingCell ν c r, F.lam r i x * Ψ x) (F.E r)
    (ENNReal.ofReal Kp) hΨ hE hEb
  have hlam : ∀ i : Fin 2,
      ENNReal.ofReal ‖∫ x in movingCell ν c r, F.lam r i x * Ψ x‖ ≤
        ENNReal.ofReal Kp * xNorm (cellLen c (clockA ν r)) m Ψ :=
    fun i => (F.lam_bdd r hr hbr i Ψ).trans (mul_le_mul_of_nonneg_right hKle zero_le)
  have hsum_lam :
      (∑ i : Fin 2, ENNReal.ofReal ‖∫ x in movingCell ν c r, F.lam r i x * Ψ x‖) ≤
        2 * (ENNReal.ofReal Kp * xNorm (cellLen c (clockA ν r)) m Ψ) := by
    calc (∑ i : Fin 2, ENNReal.ofReal ‖∫ x in movingCell ν c r, F.lam r i x * Ψ x‖)
        ≤ ∑ _i : Fin 2, ENNReal.ofReal Kp * xNorm (cellLen c (clockA ν r)) m Ψ :=
          Finset.sum_le_sum (fun i _ => hlam i)
      _ = 2 * (ENNReal.ofReal Kp * xNorm (cellLen c (clockA ν r)) m Ψ) := by
          rw [Fin.sum_univ_two]; ring
  have hofR : ENNReal.ofReal (1 + 2 * Kp ^ 2) =
      1 + 2 * ENNReal.ofReal Kp * ENNReal.ofReal Kp := by
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, sq,
      ← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul zero_le_two,
      ENNReal.ofReal_ofNat]
  unfold xNorm frameProj
  calc eLpNorm (fun y => Ψ y - ∑ i : Fin 2, (∫ x in movingCell ν c r, F.lam r i x * Ψ x) * F.E r i y)
        2 (B0579.cellMeasure (cellLen c (clockA ν r)) m)
      ≤ xNorm (cellLen c (clockA ν r)) m Ψ +
          (∑ i : Fin 2, ENNReal.ofReal ‖∫ x in movingCell ν c r, F.lam r i x * Ψ x‖) *
            ENNReal.ofReal Kp := hsub
    _ ≤ xNorm (cellLen c (clockA ν r)) m Ψ +
          (2 * (ENNReal.ofReal Kp * xNorm (cellLen c (clockA ν r)) m Ψ)) *
            ENNReal.ofReal Kp :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hsum_lam zero_le)
    _ = (1 + 2 * ENNReal.ofReal Kp * ENNReal.ofReal Kp) * xNorm (cellLen c (clockA ν r)) m Ψ := by
        ring
    _ = ENNReal.ofReal (1 + 2 * Kp ^ 2) * xNorm (cellLen c (clockA ν r)) m Ψ := by
        rw [← hofR]

/-- Pointwise `X_{m,d(r)}` bound on `complModeForce κ P F tr r j` from the oscillator and Euler
mode-residual bounds. -/
theorem xNorm_complModeForce_le (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K r C₁ C₂ : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (j : Fin 2)
    (hν : 0 < ν) (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hOsc_m : AEStronglyMeasurable (movOscRes κ ν r j)
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m))
    (hOsc_b : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movOscRes κ ν r j) ≤
      ENNReal.ofReal (C₁ / clockTheta ν r))
    (hEul_m : AEStronglyMeasurable (movEulerRes κ P tr r j)
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m))
    (hEul_b : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (movEulerRes κ P tr r j) ≤
      ENNReal.ofReal (C₂ * ν ^ 3 / clockTheta ν r)) :
    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j) ≤
      ENNReal.ofReal
        ((1 + 2 * max K 0 ^ 2) * max C₁ C₂ * (1 + ν ^ 3) / clockTheta ν r) := by
  have hθr : 0 < clockTheta ν r := theta_pos hν hr
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  have hproj := xNorm_frameProj_le F hr hbr (hOsc_m.add hEul_m)
  have hadd : xNorm d m (fun y => movOscRes κ ν r j y + movEulerRes κ P tr r j y) ≤
      xNorm d m (movOscRes κ ν r j) + xNorm d m (movEulerRes κ P tr r j) :=
    eLpNorm_add_le hOsc_m hEul_m (by norm_num)
  have hsum_le :
      ENNReal.ofReal (C₁ / clockTheta ν r) + ENNReal.ofReal (C₂ * ν ^ 3 / clockTheta ν r) ≤
        ENNReal.ofReal (max C₁ C₂ * (1 + ν ^ 3) / clockTheta ν r) := by
    rw [← ENNReal.ofReal_add (div_nonneg hC₁ hθr.le) (div_nonneg (by positivity) hθr.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← add_div]
    refine div_le_div_of_nonneg_right ?_ hθr.le
    have h1 : C₁ ≤ max C₁ C₂ := le_max_left C₁ C₂
    have h2 : C₂ * ν ^ 3 ≤ max C₁ C₂ * ν ^ 3 :=
      mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (by positivity)
    linarith
  have hK_nonneg : 0 ≤ 1 + 2 * max K 0 ^ 2 := by positivity
  unfold complModeForce
  calc xNorm d m (frameProj F r (fun y => movOscRes κ ν r j y + movEulerRes κ P tr r j y))
      ≤ ENNReal.ofReal (1 + 2 * max K 0 ^ 2) *
          xNorm d m (fun y => movOscRes κ ν r j y + movEulerRes κ P tr r j y) := hproj
    _ ≤ ENNReal.ofReal (1 + 2 * max K 0 ^ 2) *
          (ENNReal.ofReal (C₁ / clockTheta ν r) + ENNReal.ofReal (C₂ * ν ^ 3 / clockTheta ν r)) :=
        mul_le_mul_of_nonneg_left (hadd.trans (add_le_add hOsc_b hEul_b)) zero_le
    _ ≤ ENNReal.ofReal (1 + 2 * max K 0 ^ 2) *
          ENNReal.ofReal (max C₁ C₂ * (1 + ν ^ 3) / clockTheta ν r) :=
        mul_le_mul_of_nonneg_left hsum_le zero_le
    _ = ENNReal.ofReal ((1 + 2 * max K 0 ^ 2) * max C₁ C₂ * (1 + ν ^ 3) / clockTheta ν r) := by
        rw [← ENNReal.ofReal_mul hK_nonneg]
        congr 1
        ring

/-- Summing `ENNReal.ofReal ‖ampl F w r j‖ * xNorm d(r) m (complModeForce κ P F tr r j)` over
`j : Fin 2` is bounded by `ENNReal.ofReal η * amplNorm F w r`. -/
theorem sum_ampl_complModeForce_le (κ : PlanarFrameKernels) (P : PlanarData) {ν m b K r η : ℝ}
    (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (w : ℝ → ℝ × ℝ → ℂ)
    (hforce : ∀ j : Fin 2,
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j) ≤
        ENNReal.ofReal η) :
    (∑ j : Fin 2,
        ENNReal.ofReal ‖ampl F w r j‖ *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j)) ≤
      ENNReal.ofReal η * amplNorm F w r := by
  unfold amplNorm
  calc (∑ j : Fin 2,
          ENNReal.ofReal ‖ampl F w r j‖ *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j))
      ≤ ∑ j : Fin 2, ENNReal.ofReal ‖ampl F w r j‖ * ENNReal.ofReal η :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hforce j) zero_le)
    _ = ENNReal.ofReal η * ∑ j : Fin 2, ENNReal.ofReal ‖ampl F w r j‖ := by
        rw [Fin.sum_univ_two, Fin.sum_univ_two]; ring

end FrameShortBlockSub

open FrameShortBlockSub

/-! ## Conditional assembly of `FrameShortBlockBound` -/

/-- Assembly of `FrameShortBlockBound κ` from `freeMovingEnergy` (`Clock/FreeMoving.lean`) and the
three leaves `ShortComplPerturbDuhamel`, `ComplModeForceOscillator`, and
`ComplModeForceEulerError`. -/
theorem frameShortBlockBound_of (κ : PlanarFrameKernels)
    (hPert : ShortComplPerturbDuhamel κ)
    (hOsc : ComplModeForceOscillator κ)
    (hEul : ComplModeForceEulerError κ) :
    FrameShortBlockBound κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨b_free, hFreeB⟩ := freeMovingEnergy m hm 1 zero_lt_one
  obtain ⟨C_pert, b_pert, hC_pert, hb_pert, hPertB⟩ := hPert freeMovingEnergy hκ P hP m hm K
  obtain ⟨C₁, b_osc, hC₁, _hb_osc, hOscB⟩ := hOsc hκ m hm
  obtain ⟨C₂, b_eul, hC₂, _hb_eul, hEulB⟩ := hEul hκ P hP m hm
  set μ_raw := normGrowthConst m + 1 + C_pert
  set μ := μ_raw + |P.eigenvalue.re| + |P.kappa.re|
  have hCm_pos : 0 < normGrowthConst m := by
    unfold normGrowthConst; positivity
  have hμ_raw_pos : 0 < μ_raw := by positivity
  have hμ_pos : 0 < μ := by
    have := abs_nonneg P.eigenvalue.re
    have := abs_nonneg P.kappa.re
    positivity
  set M_B := Real.exp (μ * B)
  have hM_B_ge : 1 ≤ M_B := Real.one_le_exp (mul_nonneg hμ_pos.le hB.le)
  set C_force := (1 + 2 * max K 0 ^ 2) * max C₁ C₂
  have hC_force_nonneg : 0 ≤ C_force := by
    have : 0 ≤ max C₁ C₂ := le_trans hC₁ (le_max_left C₁ C₂)
    positivity
  set C_B := B * M_B * C_force
  have hC_B_nonneg : 0 ≤ C_B := by positivity
  set b₂ := max (max b_free b_pert) (max b_osc b_eul)
  have hb₂_ge : 1 ≤ b₂ :=
    le_trans hb_pert (le_trans (le_max_right _ _) (le_max_left _ _))
  refine ⟨M_B, C_B, b₂, hM_B_ge, hC_B_nonneg, hb₂_ge, fun b hb => ?_⟩
  have hb_free' : b_free ≤ b :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hb
  have hb_pert' : b_pert ≤ b :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hb
  have hb_osc' : b_osc ≤ b :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have hb_eul' : b_eul ≤ b :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hb
  obtain ⟨ν_free, hν_free, _Hfree⟩ := hFreeB b hb_free'
  obtain ⟨ν_pert, hν_pert, HPert⟩ := hPertB b hb_pert'
  obtain ⟨ν_osc, hν_osc, HOsc⟩ := hOscB b hb_osc'
  obtain ⟨ν_eul, hν_eul, HEul⟩ := hEulB b hb_eul'
  refine ⟨min (min ν_free ν_pert) (min ν_osc ν_eul),
    lt_min (lt_min hν_free hν_pert) (lt_min hν_osc hν_eul),
    fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbs hZ f w u hw hz => ?_⟩
  have hνpos : 0 < ν := hν.1
  have hν_p : ν ∈ Ioc 0 ν_pert :=
    ⟨hν.1, hν.2.trans (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  have hν_o : ν ∈ Ioc 0 ν_osc :=
    ⟨hν.1, hν.2.trans (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hν_e : ν ∈ Ioc 0 ν_eul :=
    ⟨hν.1, hν.2.trans (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  set F := periodizedFrame κ ν m b K hν.1 hF
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hb1 : 1 ≤ b := hb₂_ge.trans hb
  have hθt₂_ge_one : 1 ≤ clockTheta ν t₂ := hb1.trans hbs
  have hθt₂_pos : 0 < clockTheta ν t₂ := theta_pos hνpos ht₂
  -- 1. Apply the perturbed Duhamel inequality on [t₁, t₂]
  have hDuh := HPert ν hν_p hF tr htr t₁ t₂ ht₁ h12 hbs f w u hw hz
  -- 2. Bound the homogeneous factor by clockN P ν t₁ t₂ * M_B
  have hHom_real :
      Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁)) ≤ clockN P ν t₁ t₂ * M_B := by
    calc Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁))
        ≤ clockN P ν t₁ t₂ * Real.exp (μ * (movingZ ν t₂ - movingZ ν t₁)) :=
          exp_mul_le_clockN_mul_exp P μ_raw hνpos ht₁ h12 hθt₂_ge_one
      _ ≤ clockN P ν t₁ t₂ * M_B := by
          refine mul_le_mul_of_nonneg_left ?_ (clockN_pos P hνpos ht₁ ht₂).le
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hZ hμ_pos.le)
  have hHom :
      ENNReal.ofReal (Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν t₁))) *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) ≤
        ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal M_B *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (clockN_pos P hνpos ht₁ ht₂).le]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hHom_real) zero_le
  -- 3. Bound the forcing integral on Ioc t₁ t₂
  set S : ℝ≥0∞ := ⨆ r ∈ Icc t₁ t₂, amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r)
  set η_t₂ : ℝ := C_force * (1 + ν ^ 3) / clockTheta ν t₂
  have hη_t₂_nonneg : 0 ≤ η_t₂ := div_nonneg (by positivity) hθt₂_pos.le
  have hInt_pt : ∀ r ∈ Ioc t₁ t₂,
      ENNReal.ofReal
          ((clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) *
        (∑ j : Fin 2,
          ENNReal.ofReal ‖ampl F w r j‖ *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j)) ≤
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (M_B * η_t₂) * S)) := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1.le
    have ha_pos : 0 < clockA ν r := by
      have := one_le_clockA hνpos.le hr0
      linarith
    have ha2_nonneg : 0 ≤ (clockA ν r) ^ (-2 : ℝ) := (Real.rpow_pos_of_pos ha_pos _).le
    have hθr_ge_t₂ : clockTheta ν t₂ ≤ clockTheta ν r := theta_anti hνpos hr0 hr.2
    have hbr : b ≤ clockTheta ν r := hbs.trans hθr_ge_t₂
    have hforce_r : ∀ j : Fin 2,
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j) ≤
          ENNReal.ofReal η_t₂ := by
      intro j
      obtain ⟨hOm, hOb⟩ := HOsc ν hν_o r hr0 hbr j
      obtain ⟨hEm, hEb⟩ := HEul ν hν_e tr htr r hr0 hbr j
      refine (xNorm_complModeForce_le κ P F tr j hνpos hr0 hbr hC₁ hC₂ hOm hOb hEm hEb).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      exact div_le_div_of_nonneg_left (by positivity) hθt₂_pos hθr_ge_t₂
    have hsum_r := sum_ampl_complModeForce_le κ P F tr w hforce_r
    have hZr_le : movingZ ν t₂ - movingZ ν r ≤ B := by
      have h1 := FrameStableSub.movingZ_le_movingZ hνpos ht₁ hr.1.le
      linarith
    have hexp_r :
        Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r)) ≤ clockN P ν r t₂ * M_B := by
      calc Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))
          ≤ clockN P ν r t₂ * Real.exp (μ * (movingZ ν t₂ - movingZ ν r)) :=
            exp_mul_le_clockN_mul_exp P μ_raw hνpos hr0 hr.2 hθt₂_ge_one
        _ ≤ clockN P ν r t₂ * M_B := by
            refine mul_le_mul_of_nonneg_left ?_ (clockN_pos P hνpos hr0 ht₂).le
            exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hZr_le hμ_pos.le)
    have hN_r : 0 < clockN P ν t₁ r := clockN_pos P hνpos ht₁ hr0
    have hN_rt₂ : 0 < clockN P ν r t₂ := clockN_pos P hνpos hr0 ht₂
    have hN_ne0 : ENNReal.ofReal (clockN P ν t₁ r) ≠ 0 :=
      (ENNReal.ofReal_pos.2 hN_r).ne'
    have hN_netop : ENNReal.ofReal (clockN P ν t₁ r) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hampl_split :
        ENNReal.ofReal (clockN P ν r t₂) * amplNorm F w r ≤
          ENNReal.ofReal (clockN P ν t₁ t₂) * S := by
      have hdiv : amplNorm F w r =
          ENNReal.ofReal (clockN P ν t₁ r) *
            (amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r)) :=
        (ENNReal.mul_div_cancel hN_ne0 hN_netop).symm
      have hsup : amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r) ≤ S :=
        le_biSup (fun u => amplNorm F w u / ENNReal.ofReal (clockN P ν t₁ u)) ⟨hr.1.le, hr.2⟩
      rw [hdiv, ← mul_assoc, mul_comm (ENNReal.ofReal (clockN P ν r t₂)),
        ← FrameStableSub.ofReal_clockN_mul P hνpos ht₁ hr0 ht₂]
      exact mul_le_mul_of_nonneg_left hsup zero_le
    rw [ENNReal.ofReal_mul ha2_nonneg, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    calc ENNReal.ofReal (Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j))
        ≤ (ENNReal.ofReal (clockN P ν r t₂) * ENNReal.ofReal M_B) *
            (ENNReal.ofReal η_t₂ * amplNorm F w r) := by
          rw [← ENNReal.ofReal_mul hN_rt₂.le]
          exact mul_le_mul (ENNReal.ofReal_le_ofReal hexp_r) hsum_r zero_le zero_le
      _ = (ENNReal.ofReal M_B * ENNReal.ofReal η_t₂) *
            (ENNReal.ofReal (clockN P ν r t₂) * amplNorm F w r) := by
          ring
      _ ≤ (ENNReal.ofReal M_B * ENNReal.ofReal η_t₂) *
            (ENNReal.ofReal (clockN P ν t₁ t₂) * S) :=
          mul_le_mul_of_nonneg_left hampl_split zero_le
      _ = ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (M_B * η_t₂) * S) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          ring
  have hInt :
      (∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal
            ((clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j))) ≤
        ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) := by
    calc (∫⁻ r in Ioc t₁ t₂,
          ENNReal.ofReal
              ((clockA ν r) ^ (-2 : ℝ) * Real.exp (μ_raw * (movingZ ν t₂ - movingZ ν r))) *
            (∑ j : Fin 2,
              ENNReal.ofReal ‖ampl F w r j‖ *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j)))
        ≤ ∫⁻ r in Ioc t₁ t₂,
            ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
              (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (M_B * η_t₂) * S)) :=
          setLIntegral_mono' measurableSet_Ioc hInt_pt
      _ = (∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ))) *
            (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (M_B * η_t₂) * S)) := by
          refine lintegral_mul_const _ ?_
          unfold clockA
          exact ENNReal.measurable_ofReal.comp
            ((measurable_const.add (measurable_const.mul measurable_id)).pow_const (-2 : ℝ))
      _ = ENNReal.ofReal (movingZ ν t₂ - movingZ ν t₁) *
            (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (M_B * η_t₂) * S)) := by
          rw [lintegral_clockA_inv_sq_eq hνpos ht₁ h12]
      _ ≤ ENNReal.ofReal B *
            (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (M_B * η_t₂) * S)) :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hZ) zero_le
      _ = ENNReal.ofReal (clockN P ν t₁ t₂) *
            ((ENNReal.ofReal B * ENNReal.ofReal (M_B * η_t₂)) * S) := by
          ring
      _ = ENNReal.ofReal (clockN P ν t₁ t₂) *
            (ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) := by
          rw [← ENNReal.ofReal_mul hB.le]
          congr 3
          simp only [C_B, η_t₂]
          ring
  calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂)
      ≤ ENNReal.ofReal (clockN P ν t₁ t₂) *
            (ENNReal.ofReal M_B *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) +
          ENNReal.ofReal (clockN P ν t₁ t₂) *
            (ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) :=
        hDuh.trans (add_le_add hHom hInt)
    _ = ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal M_B *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) +
            ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) := by
        rw [← mul_add]

end UnforcedLeray.Short.IIIa
