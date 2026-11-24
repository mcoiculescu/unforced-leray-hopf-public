import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Short.PartIIa.Tasks.R04ResidualPeriodic
import UnforcedLeray.Short.PartIIa.Tasks.R05ResidualFromTable.EnvelopeLp
import UnforcedLeray.Lib.AxisymmetricB.AxisRegularity

/-!
# Part II-a, task `PartII-a:R05`: similarity integration from the late table and early bound

Target: `ringResidualFromTable : RingResidualFromTable` (`Short/PartII-a/StatementsRing.lean`, line 263).
Source of record: `the November 2 reference manuscript`, lines 1277–1297.

## Architecture
1. `ProfileDerivs.lean` establishes the 5-term off-axis chart representation `resFiveTerms` of
   `ringResidual R ν ψ pr τ`, its `C^1` regularity off `Axi.axis` (`contDiffOn_ringResidual`),
   its classical directional derivative formula `fderiv_ringResidual_eq_resFiveTerms`, and time
   continuity in `τ` at fixed `y ∉ Axi.axis` (`continuous_ringResidual_time`,
   `continuous_fderiv_ringResidual_time`).
2. `EnvelopeBounds.lean` combines `RingLateTable` and `RingEarlyBound` at weight `m = 1`
   (`extract_all_coeff_bounds`) to bound `‖ringResidual R ν ψ pr τ y‖` and
   `‖fderiv ℝ (ringResidual R ν ψ pr τ) y v‖` (`‖v‖ ≤ 1`) off `Axi.axis` by
   `(25 * B * R⁻¹) * resEnvelope (Axi.age R y) (Axi.trans R y)` (`ringResidual_pointwise_envelope_bounds`).
3. `EnvelopeLp.lean` integrates `spatialEnvelope R` in the ring chart `(s, η)` (`Axi.lintegral_ringChart`)
   to prove `MemLp (spatialEnvelope R) (ENNReal.ofReal p) volume` with `L^p` norm bounded by
   `envConst * R ^ (2 / p)`, and deduces `MemLp`, `eLpNorm` bounds (`memLp_and_norm_le_of_envelope`),
   and `L^p` continuity in `τ` by dominated convergence (`tendsto_eLpNorm_sub_of_envelope`).
4. This file supplies `HasWeakSpatialDerivative` across the codimension-2 symmetry axis via
   `Axi.hasWeakSpatialDerivative_of_offAxis`, combines it with `ringResidual_periodic` (`R04`),
   and proves `ringResidualFromTable : RingResidualFromTable`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.RingLift UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.B0188 UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa.R05

/-- Euclidean norm of every standard basis vector `coordinateVector i` (`i : Fin 3`) is `1`. -/
theorem norm_coordinateVector_eq_one (i : Fin 3) : ‖coordinateVector i‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  fin_cases i <;> simp [Axi.coordinateVector_apply]

theorem norm_coordinateVector_le_one (i : Fin 3) : ‖coordinateVector i‖ ≤ 1 :=
  (norm_coordinateVector_eq_one i).le

/-- Algebraic identity `R⁻¹ * R ^ (2 / p) = (R⁻¹) ^ (1 - 2 / p)` for `R > 0`. -/
theorem inv_mul_rpow_two_div {R p : ℝ} (hR : 0 < R) :
    R⁻¹ * R ^ (2 / p) = (R⁻¹) ^ (1 - 2 / p) := by
  have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
  rw [sub_eq_add_neg, Real.rpow_add hRinv, Real.rpow_one,
    ← Real.rpow_neg_one R, ← Real.rpow_mul hR.le]
  congr 2
  ring

/-- Off-axis continuity of the `i`-th classical partial derivative of `ringResidual R ν ψ pr τ`. -/
theorem continuousOn_fderiv_ringResidual_coord {R ν c : ℝ} (hR : 2 ≤ R) (hν : 0 < ν) (hc : 0 < c)
    {ψ pr : ProfilePoint → ℝ} (htr : IsExactPlanarTrain ν c ψ pr) (τ : ℝ) (i : Fin 3) :
    ContinuousOn (fun y => fderiv ℝ (ringResidual R ν ψ pr τ) y (coordinateVector i)) Axi.axisᶜ := by
  have hcd := contDiffOn_ringResidual hR hν hc htr τ
  have hfd : ContinuousOn (fderiv ℝ (ringResidual R ν ψ pr τ)) Axi.axisᶜ :=
    hcd.continuousOn_fderiv_of_isOpen Axi.isOpen_compl_axis le_rfl
  exact hfd.clm_apply continuousOn_const

/-- **`PartII-a:R05`: similarity integration from the late table and early bound**
(source lines 1277–1297). -/
theorem ringResidualFromTable : RingResidualFromTable := by
  intro hLate hEarly ρ p hρ hp
  obtain ⟨ν₀, hν₀, C₀, d, hC₀, hCoeff⟩ := extract_all_coeff_bounds hLate hEarly hρ
  refine ⟨ν₀, hν₀, 100 * envConst * C₀, d, ?_⟩
  intro ν hν ψ pr htr R hR
  have hν_pos : 0 < ν := hν.1
  have hc_pos : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν_pos _
  have hR_pos : 0 < R := by linarith
  obtain ⟨hψ_per, hpr_per⟩ := exactTrain_periodic htr
  refine ⟨fun τ => ringResidual_periodic R ν (ν ^ (-ρ)) hR ψ pr hψ_per hpr_per τ, ?_⟩
  -- Unpack the five coefficient envelope bounds
  obtain ⟨bA1, bB1, bA2, bB2, bB3⟩ := hCoeff ν hν ψ pr htr
  set c := ν ^ (-ρ)
  set B₀ := polyConst C₀ d ν c
  have hB₀ : 0 ≤ B₀ := by
    change 0 ≤ polyConst C₀ d ν c
    unfold polyConst
    positivity
  set K := 25 * B₀ * R⁻¹
  have hK : 0 ≤ K := by positivity
  -- Define the candidate weak partial derivatives `G τ i`
  let F : ℝ → SpatialField := ringResidual R ν ψ pr
  let G : ℝ → Fin 3 → SpatialField :=
    fun τ i y => fderiv ℝ (ringResidual R ν ψ pr τ) y (coordinateVector i)
  have hF_meas : ∀ τ, AEStronglyMeasurable (F τ) volume := fun τ =>
    aestronglyMeasurable_of_continuousOn_offAxis
      (contDiffOn_ringResidual hR hν_pos hc_pos htr τ).continuousOn
  have hG_meas : ∀ i τ, AEStronglyMeasurable (G τ i) volume := fun i τ =>
    aestronglyMeasurable_of_continuousOn_offAxis
      (continuousOn_fderiv_ringResidual_coord hR hν_pos hc_pos htr τ i)
  have hF_bdd : ∀ τ, ∀ y ∉ Axi.axis, ‖F τ y‖ ≤ K * spatialEnvelope R y := fun τ y hy =>
    (ringResidual_pointwise_envelope_bounds hR hν_pos hc_pos hB₀ htr bA1 bB1 bA2 bB2 bB3 τ hy).1
  have hG_bdd : ∀ i τ, ∀ y ∉ Axi.axis, ‖G τ i y‖ ≤ K * spatialEnvelope R y := fun i τ y hy =>
    (ringResidual_pointwise_envelope_bounds hR hν_pos hc_pos hB₀ htr bA1 bB1 bA2 bB2 bB3 τ hy).2
      (coordinateVector i) (norm_coordinateVector_le_one i)
  have hF_lp : ∀ τ, MemLp (F τ) (ENNReal.ofReal p) volume ∧
      (eLpNorm (F τ) (ENNReal.ofReal p) volume).toReal ≤ K * envConst * R ^ (2 / p) :=
    fun τ => memLp_and_norm_le_of_envelope hR hp hK (hF_meas τ) (hF_bdd τ)
  have hG_lp : ∀ τ i, MemLp (G τ i) (ENNReal.ofReal p) volume ∧
      (eLpNorm (G τ i) (ENNReal.ofReal p) volume).toReal ≤ K * envConst * R ^ (2 / p) :=
    fun τ i => memLp_and_norm_le_of_envelope hR hp hK (hG_meas i τ) (hG_bdd i τ)
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal hp
  refine ⟨G, fun τ => (hF_lp τ).1, ?_, ?_, ?_⟩
  · -- `MemLp (G τ i)` and `HasWeakSpatialDerivative i (F τ) (G τ i)`
    intro τ i
    refine ⟨(hG_lp τ i).1, ?_⟩
    exact Axi.hasWeakSpatialDerivative_of_offAxis hp2
      (contDiffOn_ringResidual hR hν_pos hc_pos htr τ)
      (fun S _ => (hF_lp τ).1.restrict S) i
      (fun S _ => (hG_lp τ i).1.restrict S)
  · -- Uniform `W^{1,p}` norm bound across `τ`
    intro τ
    have h0 := (hF_lp τ).2
    have hsum : ∑ i : Fin 3, (eLpNorm (G τ i) (ENNReal.ofReal p) volume).toReal ≤
        3 * (K * envConst * R ^ (2 / p)) := by
      rw [Fin.sum_univ_three]
      linarith [(hG_lp τ 0).2, (hG_lp τ 1).2, (hG_lp τ 2).2]
    have htot : (eLpNorm (F τ) (ENNReal.ofReal p) volume).toReal +
        ∑ i : Fin 3, (eLpNorm (G τ i) (ENNReal.ofReal p) volume).toReal ≤
        4 * (K * envConst * R ^ (2 / p)) := by linarith
    have halg : 4 * (K * envConst * R ^ (2 / p)) =
        polyConst (100 * envConst * C₀) d ν c * (R⁻¹) ^ (1 - 2 / p) := by
      calc 4 * (K * envConst * R ^ (2 / p))
          = (100 * envConst * B₀) * (R⁻¹ * R ^ (2 / p)) := by
              change 4 * ((25 * B₀ * R⁻¹) * envConst * R ^ (2 / p)) = _
              ring
        _ = (100 * envConst * B₀) * (R⁻¹) ^ (1 - 2 / p) := by
              rw [inv_mul_rpow_two_div hR_pos]
        _ = polyConst (100 * envConst * C₀) d ν c * (R⁻¹) ^ (1 - 2 / p) := by
              change (100 * envConst * polyConst C₀ d ν c) * (R⁻¹) ^ (1 - 2 / p) = _
              unfold polyConst
              ring
    exact htot.trans_eq halg
  · -- Continuity in `τ` in `W^{1,p}`
    intro τ₀
    have hF_t : Tendsto (fun τ => (eLpNorm (F τ - F τ₀) (ENNReal.ofReal p) volume).toReal)
        (𝓝 τ₀) (𝓝 0) :=
      tendsto_eLpNorm_sub_of_envelope hR hp hK hF_meas hF_bdd
        (fun y hy => continuous_ringResidual_time hR hν_pos hc_pos htr hy) τ₀
    have hG_t : ∀ i : Fin 3,
        Tendsto (fun τ => (eLpNorm (G τ i - G τ₀ i) (ENNReal.ofReal p) volume).toReal)
          (𝓝 τ₀) (𝓝 0) :=
      fun i => tendsto_eLpNorm_sub_of_envelope hR hp hK (hG_meas i) (hG_bdd i)
        (fun y hy => continuous_fderiv_ringResidual_time hR hν_pos hc_pos htr hy (coordinateVector i))
        τ₀
    have hsum_t : Tendsto (fun τ =>
        ∑ i : Fin 3, (eLpNorm (G τ i - G τ₀ i) (ENNReal.ofReal p) volume).toReal)
        (𝓝 τ₀) (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ (fun i _ => hG_t i)
    simpa using hF_t.add hsum_t

end UnforcedLeray.Short.PartIIa
