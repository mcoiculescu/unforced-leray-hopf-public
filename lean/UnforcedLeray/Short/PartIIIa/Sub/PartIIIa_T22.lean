import UnforcedLeray.Short.PartIIIa.CanonicalTransfer
import UnforcedLeray.Short.PartIIIa.T20_CTEmbeddings
import UnforcedLeray.Short.PartIIIa.T21_FullClock
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainL2DecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainStrainIntegralProof
import UnforcedLeray.Short.Spine.Proofs.TrainEstimates.FluctuationIntegral
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartI.Tasks.CanonicalBranchProof
import UnforcedLeray.Short.PartI.Tasks.CanonicalMellinProof
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch

/-!
# Part III-a, task `PartIII-a:T22` shared module (`tails/canonical-transfer.tex`, SP 3106-3404)

Shared unconditional Part I bundles, clock/scaling identities, physical-cylinder canonical column
`canonicalPhysColumn`, intermediate leaf `Prop`s for `LongComparison` (`T22/2/1..3`) and
`AbsoluteStress` (`T22/6/1`), and the final `canonicalTransferAll_of` assembly helper.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.T22Sub

open UnforcedLeray.Short.IIIa

/-! ## 1. Unconditional Part I & Spine bundles for `T22` children -/

theorem trainComparison_unconditional : UnforcedLeray.Short.PartI.TrainComparison :=
  UnforcedLeray.Short.PartI.trainComparison_proof

theorem trainOverlap_unconditional : UnforcedLeray.Short.PartI.TrainOverlap := by
  have hHN := UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hFD := UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hMP := UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hMD := UnforcedLeray.Short.PartI.overlap_mean_decay hHN hFD hMP
  exact UnforcedLeray.Short.PartI.trainOverlap_proof hFD hMD

theorem trainL2Decay_unconditional : UnforcedLeray.Short.PartI.TrainL2Decay :=
  UnforcedLeray.Short.PartI.trainL2Decay_proof trainOverlap_unconditional

theorem trainStrainIntegral_unconditional : UnforcedLeray.Short.PartI.TrainStrainIntegral :=
  UnforcedLeray.Short.PartI.trainStrainIntegral_proof trainOverlap_unconditional

theorem trainFluctuationIntegral_unconditional :
    UnforcedLeray.Short.PartI.TrainFluctuationIntegral :=
  UnforcedLeray.Short.Spine.trainFluctuationIntegral_proof
    trainL2Decay_unconditional trainOverlap_unconditional

theorem trainMeanEquations_unconditional : UnforcedLeray.Short.PartI.TrainMeanEquations :=
  UnforcedLeray.Short.PartI.trainMeanEquations_proof

theorem trainFluctuationDecay_unconditional : UnforcedLeray.Short.PartI.TrainFluctuationDecay := by
  have hHN := UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hFD := UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hOv := trainOverlap_unconditional
  have hVort := UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails := UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  exact UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hFD hOv

theorem trainTransverseTails_unconditional : UnforcedLeray.Short.PartI.TrainTransverseTails := by
  have hOv := trainOverlap_unconditional
  have hVort := UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails := UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  exact UnforcedLeray.Short.PartI.trainTransverseTails_proof hVort hTails

theorem canonicalBranch_unconditional : UnforcedLeray.Short.PartI.CanonicalBranch :=
  UnforcedLeray.Short.PartI.canonicalBranch_proof

theorem canonicalMellin_unconditional : UnforcedLeray.Short.PartI.CanonicalMellin :=
  UnforcedLeray.Short.PartI.canonicalMellin_proof

theorem canonicalBranchHyp_unconditional : UnforcedLeray.Cons.C01.CanonicalBranchHyp :=
  UnforcedLeray.Short.Spine.canonicalBranchHyp

/-! ## 2. Exact clock, cell-length, and canonical-column identities (SP 3112-3128, 3191-3197) -/

theorem clockAge_nonneg {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) (hθν : θ ≤ ν⁻¹) :
    0 ≤ clockAge ν θ := by
  unfold clockAge
  have h1 : ν * θ ≤ 1 := by
    calc ν * θ ≤ ν * ν⁻¹ := mul_le_mul_of_nonneg_left hθν hν.le
      _ = 1 := mul_inv_cancel₀ hν.ne'
  exact div_nonneg (by linarith) (by positivity)

theorem clockAge_inv {ν : ℝ} (hν : 0 < ν) : clockAge ν ν⁻¹ = 0 := by
  unfold clockAge
  rw [mul_inv_cancel₀ hν.ne', sub_self, zero_div]

theorem clockAge_eq_coreEnd {ν b : ℝ} (hν : 0 < ν) (hb : 0 < b) :
    clockAge ν b = coreEnd ν b := by
  unfold clockAge coreEnd
  have hν_ne : ν ≠ 0 := hν.ne'
  have hb_ne : b ≠ 0 := hb.ne'
  field_simp

theorem clockA_clockAge {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    clockA ν (clockAge ν θ) = (ν * θ)⁻¹ := by
  unfold clockA clockAge
  have hν_ne : ν ≠ 0 := hν.ne'
  have hθ_ne : θ ≠ 0 := hθ.ne'
  field_simp
  ring

theorem clockTheta_clockAge {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    clockTheta ν (clockAge ν θ) = θ := by
  unfold clockTheta
  rw [clockA_clockAge hν hθ]
  have hν_ne : ν ≠ 0 := hν.ne'
  have hθ_ne : θ ≠ 0 := hθ.ne'
  field_simp

theorem clockAge_clockTheta {ν s : ℝ} (hν : 0 < ν) (ha : 0 < clockA ν s) :
    clockAge ν (clockTheta ν s) = s := by
  unfold clockAge clockTheta clockA at *
  have hν_ne : ν ≠ 0 := hν.ne'
  have ha_ne : 1 + ν * s ≠ 0 := ha.ne'
  field_simp
  ring

theorem dOfTheta_eq_cellLen {ν s : ℝ} (hν : 0 < ν) (ha : 0 < clockA ν s) :
    dOfTheta ν (clockTheta ν s) = cellLen (ν ^ (-2 : ℝ)) (clockA ν s) := by
  unfold dOfTheta clockTheta cellLen
  have hdiv : (ν * clockA ν s)⁻¹ / ν ^ 3 = (ν ^ (-2 : ℝ)) ^ 2 / clockA ν s := by
    have hpow : (ν ^ (-2 : ℝ)) ^ 2 = (ν ^ 4)⁻¹ := by
      rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]
      ring
    rw [hpow]
    have hν_ne : ν ≠ 0 := hν.ne'
    have ha_ne : clockA ν s ≠ 0 := ha.ne'
    field_simp
  rw [hdiv, Real.sqrt_div (by positivity), Real.sqrt_sq (Real.rpow_pos_of_pos hν (-2)).le]

theorem dOfTheta_inv {ν : ℝ} (hν : 0 < ν) :
    dOfTheta ν ν⁻¹ = ν ^ (-2 : ℝ) := by
  have h := dOfTheta_eq_cellLen (s := 0) hν (by unfold clockA; positivity)
  unfold clockTheta clockA cellLen at h
  simpa using h

theorem one_le_dOfTheta {ν θ : ℝ} (hν : 0 < ν) (hθ : ν ^ 3 ≤ θ) :
    1 ≤ dOfTheta ν θ := by
  unfold dOfTheta
  rw [Real.one_le_sqrt]
  exact (one_le_div (by positivity)).2 hθ

theorem gaugeFactor_ne_zero (P : PlanarData) {ν : ℝ} (hν : 0 < ν) :
    P.gaugeFactor ν ≠ 0 := by
  unfold PlanarData.gaugeFactor
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => hν.ne' (Complex.ofReal_eq_zero.1 h.1)

/-- Physical-cylinder periodized canonical column
`w_can(s, x) = N_ν J_{a(s)}(P_{d(θ(s))} V_can(θ(s)))(x)` (SP 3191-3192). -/
def canonicalPhysColumn (P : PlanarData) (ν : ℝ) (s : ℝ) : ℝ × ℝ → ℂ :=
  fun x => P.gaugeFactor ν * Jscale (clockA ν s) (canonicalPeriodized P ν (clockTheta ν s)) x

/-- At `s = 0` (`θ = ν⁻¹`), `canonicalPhysColumn P ν 0` coincides pointwise with
`preparedDatum P ν` (`q_{1/ν} = e^{λ/ν}(1/ν)^κ V_can(1/ν)`). -/
theorem canonicalPhysColumn_zero_eq_preparedDatum (P : PlanarData) {ν : ℝ} (hν : 0 < ν) :
    canonicalPhysColumn P ν 0 = preparedDatum P ν := by
  funext x
  unfold canonicalPhysColumn preparedDatum canonicalPeriodized periodizeC planarMode
    PlanarData.gaugeFactor Jscale clockTheta clockA
  have hθ0 : (ν * (1 + ν * 0))⁻¹ = ν⁻¹ := by simp
  rw [hθ0, dOfTheta_inv hν]
  have ha1 : (1 + ν * 0 : ℝ) = 1 := by ring
  simp only [ha1, Real.one_rpow, Complex.ofReal_one, one_mul, Real.sqrt_one, div_one]
  rw [← tsum_mul_left]
  congr 1
  funext n
  have hcpow : ((ν⁻¹ : ℝ) : ℂ) ^ P.kappa = (ν : ℂ) ^ (-P.kappa) := by
    rw [Complex.ofReal_inv, Complex.cpow_neg]
    have harg : (ν : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hν.le]
      exact Real.pi_ne_zero.symm
    exact Complex.inv_cpow_eq_ite (ν : ℂ) P.kappa ▸ by simp [harg]
  have hexp : P.eigenvalue / (ν : ℂ) = P.eigenvalue * ((ν⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  rw [hexp, ← hcpow]
  ring

/-- Rescaling `canonicalPhysColumn P ν` to heat coordinates recovers `canonicalPeriodized P ν θ`
identically on `(0, ∞)`. -/
theorem heatColumn_canonicalPhysColumn_eq (P : PlanarData) {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    heatColumn P ν (canonicalPhysColumn P ν) θ = canonicalPeriodized P ν θ := by
  funext y
  unfold heatColumn canonicalPhysColumn JscaleInv Jscale
  rw [clockA_clockAge hν hθ, clockTheta_clockAge hν hθ]
  set a : ℝ := (ν * θ)⁻¹
  have ha : 0 < a := inv_pos.2 (mul_pos hν hθ)
  have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hpow : (a ^ 2 : ℝ) * a ^ (-2 : ℝ) = 1 := by
    rw [Real.rpow_neg ha.le, Real.rpow_two, mul_inv_cancel₀ (pow_ne_zero 2 ha.ne')]
  have hgf : (P.gaugeFactor ν)⁻¹ * P.gaugeFactor ν = 1 :=
    inv_mul_cancel₀ (gaugeFactor_ne_zero P hν)
  have hcoord : (Real.sqrt a * y.1 / Real.sqrt a, Real.sqrt a * y.2 / Real.sqrt a) = y := by
    ext <;> simp [mul_div_cancel_left₀ _ hsq]
  dsimp only
  rw [hcoord]
  calc (P.gaugeFactor ν)⁻¹ * (((a ^ 2 : ℝ) : ℂ) *
        (P.gaugeFactor ν * (((a ^ (-2 : ℝ) : ℝ) : ℂ) * canonicalPeriodized P ν θ y)))
      = ((P.gaugeFactor ν)⁻¹ * P.gaugeFactor ν) *
          ((((a ^ 2 * a ^ (-2 : ℝ) : ℝ)) : ℂ) * canonicalPeriodized P ν θ y) := by
        push_cast; ring
    _ = canonicalPeriodized P ν θ y := by
        rw [hgf, hpow, Complex.ofReal_one, one_mul, one_mul]

/-! ## 3. Sub-leaf `Prop`s for `PartIII-a:T22/2` (`LongComparison`) and `PartIII-a:T22/6` -/

/-- **`PartIII-a:T22/2/1`**: regularity, symmetry, exact quadrupole identity
`Q_d P_d V_can(θ) = 𝔐(V_can(θ))`, and `X_{m,d}` norms of `preparedDatum` and `canonicalPeriodized`
(SP 3121-3128, 3223-3225, 3300-3302). -/
def CTCanonicalBranchProps : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m →
    (∀ ν ∈ Ioc (0 : ℝ) 1,
      MemLp (preparedDatum P ν) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (preparedDatum P ν) ∧
      IsCentrallyEven (preparedDatum P ν)) ∧
    (∀ ν θ : ℝ, 0 < ν → 0 < θ → 1 ≤ dOfTheta ν θ →
      MemLp (canonicalPeriodized P ν θ) 2 (B0579.cellMeasure (dOfTheta ν θ) m) ∧
      HasZeroCirculation (dOfTheta ν θ) (canonicalPeriodized P ν θ) ∧
      IsCentrallyEven (canonicalPeriodized P ν θ) ∧
      quadQ (dOfTheta ν θ) (canonicalPeriodized P ν θ) = quadrupole (P.canonical θ)) ∧
    (∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∃ C : ℝ, 0 < C ∧
      ∀ ν ∈ Ioc (0 : ℝ) 1, ∀ θ : ℝ, b ≤ θ → 1 ≤ dOfTheta ν θ →
        ENNReal.ofReal (Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re) *
            xNorm (dOfTheta ν θ) m (canonicalPeriodized P ν θ) ≤ ENNReal.ofReal C) ∧
    (∀ b : ℝ, 0 < b → ∃ C : ℝ, 0 < C ∧
      ∀ ν ∈ Ioc (0 : ℝ) 1, ∀ θ ∈ Ioc (0 : ℝ) b, 1 ≤ dOfTheta ν θ →
        xNorm (dOfTheta ν θ) m (canonicalPeriodized P ν θ) ≤ ENNReal.ofReal C)

/-- **`PartIII-a:T22/2/2`**: weak linearised equation and residual bounds (`eq:ct-long-residual`
on `b ≤ θ ≤ ν⁻¹` and `eq:ct-late-residual` on `r ≤ θ ≤ b`, SP 3129-3215) for the physical-cylinder
periodized canonical column `canonicalPhysColumn P ν`. -/
def CTCanonicalResidual : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, b₀ ≤ b →
    (∃ (C a₀ ν₀ : ℝ), 0 < C ∧ 0 < a₀ ∧ 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∃ (u_can : ℝ → ℝ × ℝ → Fin 2 → ℂ) (f_res : ℝ → ℝ × ℝ → ℂ),
          (∀ s ∈ Icc (0 : ℝ) (coreEnd ν b),
            IsBiotSavart (ν ^ (-2 : ℝ)) (canonicalPhysColumn P ν s) (u_can s) ∧
            MemLp (f_res s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
            HasZeroCirculation (ν ^ (-2 : ℝ)) (f_res s) ∧
            IsCentrallyEven (f_res s) ∧
            Tendsto (fun s' => xNorm (ν ^ (-2 : ℝ)) m (f_res s' - f_res s))
              (𝓝[Icc (0 : ℝ) (coreEnd ν b)] s) (𝓝 0)) ∧
          (∀ φ, B0579.IsCylTest (ν ^ (-2 : ℝ)) φ → ∀ s ∈ Icc (0 : ℝ) (coreEnd ν b),
            IntegrableOn (flowIntegrand tr (canonicalPhysColumn P ν s) (u_can s) s φ)
              (B0579.cell (ν ^ (-2 : ℝ))) ∧
            IntervalIntegrable (fun τ =>
              (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                flowIntegrand tr (canonicalPhysColumn P ν τ) (u_can τ) τ φ x) +
              (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ))) volume 0 s ∧
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), canonicalPhysColumn P ν s x * (φ x : ℂ) =
              (∫ x in B0579.cell (ν ^ (-2 : ℝ)), preparedDatum P ν x * (φ x : ℂ)) +
              ∫ τ in (0 : ℝ)..s,
                ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                  flowIntegrand tr (canonicalPhysColumn P ν τ) (u_can τ) τ φ x) +
                (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ)))) ∧
          (∀ θ ∈ Icc b ν⁻¹,
            ENNReal.ofReal (Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re *
                (clockA ν (clockAge ν θ)) ^ 2 / ‖P.gaugeFactor ν‖) *
              xNorm (dOfTheta ν θ) m
                (JscaleInv (clockA ν (clockAge ν θ)) (f_res (clockAge ν θ))) ≤
              ENNReal.ofReal (C * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ) +
                ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3))))) ∧
    (∀ r : ℝ, 0 < r → r ≤ b →
      ∃ (C_r a₀ ν_r : ℝ), 0 < C_r ∧ 0 < a₀ ∧ 0 < ν_r ∧ ∀ ν ∈ Ioc 0 ν_r,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∃ (u_can : ℝ → ℝ × ℝ → Fin 2 → ℂ) (f_res : ℝ → ℝ × ℝ → ℂ),
            (∀ s ∈ Icc (coreEnd ν b) (clockAge ν r),
              IsBiotSavart (ν ^ (-2 : ℝ)) (canonicalPhysColumn P ν s) (u_can s) ∧
              MemLp (f_res s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
              HasZeroCirculation (ν ^ (-2 : ℝ)) (f_res s) ∧
              IsCentrallyEven (f_res s) ∧
              Tendsto (fun s' => xNorm (ν ^ (-2 : ℝ)) m (f_res s' - f_res s))
                (𝓝[Icc (coreEnd ν b) (clockAge ν r)] s) (𝓝 0)) ∧
            (∀ φ, B0579.IsCylTest (ν ^ (-2 : ℝ)) φ → ∀ s ∈ Icc (coreEnd ν b) (clockAge ν r),
              IntegrableOn (flowIntegrand tr (canonicalPhysColumn P ν s) (u_can s) s φ)
                (B0579.cell (ν ^ (-2 : ℝ))) ∧
              IntervalIntegrable (fun τ =>
                (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                  flowIntegrand tr (canonicalPhysColumn P ν τ) (u_can τ) τ φ x) +
                (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ)))
                volume (coreEnd ν b) s ∧
              ∫ x in B0579.cell (ν ^ (-2 : ℝ)), canonicalPhysColumn P ν s x * (φ x : ℂ) =
                (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                  canonicalPhysColumn P ν (coreEnd ν b) x * (φ x : ℂ)) +
                ∫ τ in (coreEnd ν b)..s,
                  ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                    flowIntegrand tr (canonicalPhysColumn P ν τ) (u_can τ) τ φ x) +
                  (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ)))) ∧
            (∀ θ ∈ Icc r b,
              ENNReal.ofReal ((clockA ν (clockAge ν θ)) ^ 2 / ‖P.gaugeFactor ν‖) *
                xNorm (dOfTheta ν θ) m
                  (JscaleInv (clockA ν (clockAge ν θ)) (f_res (clockAge ν θ))) ≤
                ENNReal.ofReal (C_r * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ) +
                  ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)))))

/-- **`PartIII-a:T22/2/3`**: inhomogeneous Duhamel transfer from `CTCanonicalBranchProps` and
`CTCanonicalResidual`, yielding BOTH `CTLongComparison` (`b ≤ θ ≤ ν⁻¹`, SP 3217-3226) AND the
compact-window inhomogeneous Duhamel reduction (`r ≤ θ ≤ b`, SP 3290-3299) so `T22/4` needs only
plug in `CTKineticImpulse` and `CTPartialMoment`. -/
def CTDuhamelTransfer : Prop :=
  CTLongComparison ∧
    (CTEmbeddings → CTKineticImpulse → CTPartialMoment → CTCompactComparison)

/-- **`PartIII-a:T22/6/1`**: absolute stress impulse bound (`eq:ct-absolute-impulse`, SP 3275-3289,
stated for `k ≤ 1` so `k = 0` supplies the small-clock tail `O_K(𝒜_ν r^{σ+5/2})` in `T22/7`
`CTStressDefect` SP 3385-3387, and `r = b, k ≤ 1` supplies the `θ ≤ b` half of `T22/6`
`CTAbsoluteStress` SP 3373-3378). -/
def CTAbsoluteImpulse : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ m : ℝ, 8 < m → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ k : ℕ, k ≤ 1 → ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b →
      ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ r : ℝ, 0 < r → r ≤ b →
            ∀ h : ℝ × ℝ → ℂ, MemLp h 2 (B0579.cellMeasure (dOfTheta ν r) m) →
              HasZeroCirculation (dOfTheta ν r) h → IsCentrallyEven h →
              ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr (clockAge ν r) (Jscale (ν * r)⁻¹ h) w u →
                ∀ μ ∈ K,
                  ∫⁻ s in Ioi (clockAge ν r), ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) *
                      sAbs tr μ (u s) s ≤
                    ENNReal.ofReal (C * (ν ^ (3 + 2 * μ.re) / ν ^ (-2 : ℝ)) * ν ^ k *
                      r ^ (μ.re + 5 / 2 + (k : ℝ) / 2) *
                      max 1 ((ν ^ 3 / r) ^ (1 / 4 : ℝ))) * kinNorm (dOfTheta ν r) h

/-- Top-level conjunction of all 9 `CanonicalTransfer.lean` propositions (`PartIII-a:T22`). -/
theorem canonicalTransferAll_of
    (h1 : CTLongComparison) (h2 : CTKineticImpulse) (h3 : CTPartialMoment)
    (h4 : CTTestedImpulse) (h5 : CTCompactComparison) (h6 : CTMellin)
    (h7 : CTAbsoluteStress) (h8 : CTStressDefect) (h9 : CTAnisotropy) :
    CTLongComparison ∧ CTKineticImpulse ∧ CTPartialMoment ∧ CTTestedImpulse ∧
      CTCompactComparison ∧ CTMellin ∧ CTAbsoluteStress ∧ CTStressDefect ∧ CTAnisotropy :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end UnforcedLeray.Short.IIIa.T22Sub
