import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy
import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8

/-!
# Part II-b, task `PartII-b:T16` (`HilbertBodyComparison`): conditional assembly and reduction

Source of record: `the November 2 reference manuscript`, lines 1955-1990
(Hilbert endpoint of `bg:lp-free-comparison`, `CompRate 2 (1/4) (1/28)`).

## Proved here (zero `sorry`)

* `obsOp_pointwise_split`: pointwise bound on `B(b_ε - b_0)` splitting `∂_q(b_ε - b_0) =
  (Q_ε b_ε - ∂_q b_0) + ε(2 S b_ε + η ∂_η b_ε + b_ε)` into the localized `(Q_ε, ∂_η, id)` difference
  on `obsBox σ H₁ L₁` and the `O(Γ³ ε)` remainder controlled by the `r = 2` physical graph bound
  (`phys_graph_poly 2`);
* `omega_rate_1_28`: rate algebra converting `ω ≤ C₁ Γ^{k₁} ε^{1/14}` and `√ω + ω + √ε` into
  `O(Γ^k ε^{1/28})` for `0 < ε ≤ 1`;
* `hilbertBodyComparison_of`: conditional proof of `HilbertBodyComparison` from the two leaves
  `CompactFreeBodyRateH2` (`PartII-b:T16/1`, Part II-a `near:compact-free-comparison` in `H_2`) and
  `TestedGradientEnergyH2` (`PartII-b:T16/2`, the chart-level tested energy inequality against
  `χ² w`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Indicator of a profile on the observation box `obsBox σ H₁ L₁`. -/
def indBox (σ H₁ L₁ : ℝ) (P : CProf) : CProf :=
  (obsBox σ H₁ L₁).indicator P

theorem measurableSet_obsBox (σ H₁ L₁ : ℝ) : MeasurableSet (obsBox σ H₁ L₁) :=
  measurableSet_Icc.prod (MeasurableSet.univ.prod measurableSet_Icc)

theorem aestronglyMeasurable_indBox {c r : ℝ} (σ H₁ L₁ : ℝ) {P : CProf}
    (hP : AEStronglyMeasurable P (hMeas c r)) :
    AEStronglyMeasurable (indBox σ H₁ L₁ P) (hMeas c r) :=
  hP.indicator (measurableSet_obsBox σ H₁ L₁)

/-- **Leaf 1 (`PartII-b:T16/1`, `CompactFreeBodyRateH2`)** (SP 1691-1700, Proposition
`near:compact-free-comparison`, first rate `‖χ₁(T_ε - T_0)‖_{H_2 → H_2} ≤ C Γ^k ε^{1/14}`): on the
enlarged observation box `obsBox (σ/2) (2*H₁) (L₁ + 1)` (containing `obsBox σ H₁ L₁` when
`0 < σ ≤ H₁` and `0 ≤ L₁`), the `H_2` norm of `b_ε - b_0` is bounded by
`C₁ Γ^{k₁} ε^{1/14} ‖F‖_{H_2}`. -/
def CompactFreeBodyRateH2 : Prop :=
  ∃ (k₁ : ℕ) (C₁ : ℝ), 0 < C₁ ∧
    ∀ (Γ ν c σ H₁ L₁ : ℝ) (μ : ℂ), 1 ≤ Γ → ν ≤ Γ → ν⁻¹ ≤ Γ → c ≤ Γ → c⁻¹ ≤ Γ → σ⁻¹ ≤ Γ →
      H₁ ≤ Γ → L₁ ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + 1 / 4 → 0 < ν → 0 < c → 0 < σ →
      σ ≤ H₁ → 0 ≤ L₁ →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
    ∀ F bε b0 : CProf, InHr c 2 F → InHr c 2 bε → IsResponse ν c ε μ 2 F bε →
      IsFlatResponse ν μ F b0 → InFlatClass c 2 b0 →
      hNorm c 2 (indBox (σ / 2) (2 * H₁) (L₁ + 1) (bε - b0)) ≤
        ENNReal.ofReal (C₁ * Γ ^ k₁ * ε ^ (1 / 14 : ℝ)) * hNorm c 2 F

/-- **Leaf 2 (`PartII-b:T16/2`, `TestedGradientEnergyH2`)** (SP 1955-1988): testing the subtracted
equations of `b_ε = T_ε F` and `b_0 = T_0 F` against `χ²(b_ε - b_0)` (using `drift_identity_H2` and
`diffusion_difference_terms` of `Tasks/HilbertEnergy.lean`, absorbing one quarter of the gradient
energy from the first diffusion term, bounding the second diffusion term by `O(Γ^k ε)` via the
`r = 2` bounds for `S b_0, S b_ε`, bounding the projection-source pairing by `2ω`, and retaining the
nonnegative radial frame discrepancy `O(ε²)`) upgrades an enlarged-box `H_2` bound `ω` on `b_ε - b_0`
to an `O(Γ^{k₂}(√ω + ω + √ε))` bound on `(√s(Q_ε b_ε - ∂_q b_0), √s(∂_η b_ε - ∂_η b_0))` on
`obsBox σ H₁ L₁`. -/
def TestedGradientEnergyH2 : Prop :=
  ∃ (k₂ : ℕ) (C₂ : ℝ), 0 < C₂ ∧
    ∀ (Γ ν c σ H₁ L₁ : ℝ) (μ : ℂ), 1 ≤ Γ → ν ≤ Γ → ν⁻¹ ≤ Γ → c ≤ Γ → c⁻¹ ≤ Γ → σ⁻¹ ≤ Γ →
      H₁ ≤ Γ → L₁ ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + 1 / 4 → 0 < ν → 0 < c → 0 < σ →
      σ ≤ H₁ → 0 ≤ L₁ →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
    ∀ F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0 : CProf,
      InHr c 2 F → InHr c 2 bε → IsResponse ν c ε μ 2 F bε →
      IsFlatResponse ν μ F b0 → InFlatClass c 2 b0 →
      HasWeakVec vS dZero bε Sbε → HasWeakVec (vQ ε) (dQ ε) bε Qbε →
      HasWeakVec vEta dZero bε Ebε →
      AEStronglyMeasurable Sbε (hMeas c 2) →
      AEStronglyMeasurable (sqrtS Qbε) (hMeas c 2) →
      AEStronglyMeasurable (sqrtS Ebε) (hMeas c 2) →
      HasWeakVec vS dZero b0 Sb0 → HasWeakVec vQ0 dZero b0 Qb0 →
      HasWeakVec vEta dZero b0 Eb0 →
      AEStronglyMeasurable Sb0 (hMeas c 2) →
      AEStronglyMeasurable (sqrtS Qb0) (hMeas c 2) →
      AEStronglyMeasurable (sqrtS Eb0) (hMeas c 2) →
      ∀ om : ℝ, 0 ≤ om →
        hNorm c 2 (indBox (σ / 2) (2 * H₁) (L₁ + 1) (bε - b0)) ≤
          ENNReal.ofReal om * hNorm c 2 F →
        hNorm c 2 (indBox σ H₁ L₁ (sqrtS (Qbε - Qb0))) +
            hNorm c 2 (indBox σ H₁ L₁ (sqrtS (Ebε - Eb0))) ≤
          ENNReal.ofReal (C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε)) * hNorm c 2 F

theorem obsBox_subset_enlarged {σ H₁ L₁ : ℝ} (hσ : 0 < σ) :
    obsBox σ H₁ L₁ ⊆ obsBox (σ / 2) (2 * H₁) (L₁ + 1) := by
  rintro x ⟨⟨hx1, hx2⟩, -, ⟨hx3, hx4⟩⟩
  have hH₁ : 0 < H₁ := lt_of_lt_of_le hσ (hx1.trans hx2)
  exact ⟨⟨by linarith, by linarith⟩, trivial, ⟨by linarith, by linarith⟩⟩

theorem hNorm_indBox_le_enlarged {c r σ H₁ L₁ : ℝ} (hσ : 0 < σ) (P : CProf) :
    hNorm c r (indBox σ H₁ L₁ P) ≤ hNorm c r (indBox (σ / 2) (2 * H₁) (L₁ + 1) P) := by
  apply eLpNorm_mono
  intro x
  unfold indBox
  by_cases hx : x ∈ obsBox σ H₁ L₁
  · have hx' : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1) := obsBox_subset_enlarged hσ hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg _

theorem obsOp_pointwise_split {σ H₁ L₁ Γ ε : ℝ} (hσ : 0 < σ) (hσΓ : σ⁻¹ ≤ Γ)
    (hL₁ : L₁ ≤ Γ) (hΓ1 : 1 ≤ Γ) (hε0 : 0 < ε)
    (B : ObsOp σ H₁ L₁ Γ) (bε Sbε Qbε Ebε b0 Qb0 Eb0 : CProf) (x : Coord) :
    ‖B.apply (bε - b0) (dqOf ε bε Sbε Qbε Ebε - Qb0) (Ebε - Eb0) x‖ ≤
      Γ ^ 2 *
        (‖indBox σ H₁ L₁ (bε - b0) x‖ +
          ‖indBox σ H₁ L₁ (sqrtS (Qbε - Qb0)) x‖ +
          ‖indBox σ H₁ L₁ (sqrtS (Ebε - Eb0)) x‖) +
      2 * Γ ^ 3 * ε *
        (‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) := by
  have hRHS_nonneg : 0 ≤
      Γ ^ 2 *
        (‖indBox σ H₁ L₁ (bε - b0) x‖ +
          ‖indBox σ H₁ L₁ (sqrtS (Qbε - Qb0)) x‖ +
          ‖indBox σ H₁ L₁ (sqrtS (Ebε - Eb0)) x‖) +
      2 * Γ ^ 3 * ε *
        (‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) := by positivity
  by_cases hx : x ∈ obsBox σ H₁ L₁
  · obtain ⟨hAq, hAeta, hA0⟩ := obsOp_coeff_bound B x
    set gq := dqOf ε bε Sbε Qbε Ebε - Qb0
    set gη := Ebε - Eb0
    set d := bε - b0
    have hB : ‖B.apply d gq gη x‖ ≤ Γ * (‖gq x‖ + ‖gη x‖ + ‖d x‖) := by
      unfold ObsOp.apply
      calc ‖B.Aq x (gq x) + B.Aeta x (gη x) + B.A0 x (d x)‖
          ≤ ‖B.Aq x (gq x) + B.Aeta x (gη x)‖ + ‖B.A0 x (d x)‖ := norm_add_le _ _
        _ ≤ ‖B.Aq x (gq x)‖ + ‖B.Aeta x (gη x)‖ + ‖B.A0 x (d x)‖ :=
            add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ‖B.Aq x‖ * ‖gq x‖ + ‖B.Aeta x‖ * ‖gη x‖ + ‖B.A0 x‖ * ‖d x‖ :=
            add_le_add (add_le_add (ContinuousLinearMap.le_opNorm _ _)
              (ContinuousLinearMap.le_opNorm _ _)) (ContinuousLinearMap.le_opNorm _ _)
        _ ≤ Γ * ‖gq x‖ + Γ * ‖gη x‖ + Γ * ‖d x‖ := by gcongr
        _ = Γ * (‖gq x‖ + ‖gη x‖ + ‖d x‖) := by ring
    have hgq_eq : gq x = (Qbε - Qb0) x +
        (ε : ℂ) • ((2 : ℂ) • Sbε x + (x.2.2 : ℂ) • Ebε x + bε x) := by
      change dqOf ε bε Sbε Qbε Ebε x - Qb0 x = (Qbε x - Qb0 x) + _
      rw [dqOf_eq_add]
      abel
    have hη : |x.2.2| ≤ Γ := (abs_le.mpr hx.2.2).trans hL₁
    have hL1 : ‖(ε : ℂ) • ((2 : ℂ) • Sbε x + (x.2.2 : ℂ) • Ebε x + bε x)‖ ≤
        ε * (2 * ‖Sbε x‖ + Γ * ‖Ebε x‖ + ‖bε x‖) := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hε0.le]
      gcongr
      calc ‖(2 : ℂ) • Sbε x + (x.2.2 : ℂ) • Ebε x + bε x‖
          ≤ ‖(2 : ℂ) • Sbε x + (x.2.2 : ℂ) • Ebε x‖ + ‖bε x‖ := norm_add_le _ _
        _ ≤ ‖(2 : ℂ) • Sbε x‖ + ‖(x.2.2 : ℂ) • Ebε x‖ + ‖bε x‖ :=
            add_le_add (norm_add_le _ _) le_rfl
        _ = 2 * ‖Sbε x‖ + |x.2.2| * ‖Ebε x‖ + ‖bε x‖ := by
            simp [norm_smul, Real.norm_eq_abs]
        _ ≤ 2 * ‖Sbε x‖ + Γ * ‖Ebε x‖ + ‖bε x‖ := by gcongr
    have hgq : ‖gq x‖ ≤ ‖(Qbε - Qb0) x‖ + ε * (2 * ‖Sbε x‖ + Γ * ‖Ebε x‖ + ‖bε x‖) := by
      rw [hgq_eq]
      exact (norm_add_le _ _).trans (add_le_add le_rfl hL1)
    have hQdiff : ‖(Qbε - Qb0) x‖ ≤ Γ * ‖indBox σ H₁ L₁ (sqrtS (Qbε - Qb0)) x‖ := by
      unfold indBox
      rw [Set.indicator_of_mem hx]
      exact norm_le_gamma_mul_norm_sqrtS hσ hσΓ hΓ1 (Qbε - Qb0) hx
    have hEdiff : ‖gη x‖ ≤ Γ * ‖indBox σ H₁ L₁ (sqrtS (Ebε - Eb0)) x‖ := by
      unfold indBox
      rw [Set.indicator_of_mem hx]
      exact norm_le_gamma_mul_norm_sqrtS hσ hσΓ hΓ1 (Ebε - Eb0) hx
    have hddiff : ‖d x‖ = ‖indBox σ H₁ L₁ (bε - b0) x‖ := by
      unfold indBox
      rw [Set.indicator_of_mem hx]
    have hEε : ‖Ebε x‖ ≤ Γ * ‖sqrtS Ebε x‖ :=
      norm_le_gamma_mul_norm_sqrtS hσ hσΓ hΓ1 Ebε hx
    have h1Γ : 1 ≤ Γ := hΓ1
    have hΓ2 : Γ ≤ Γ ^ 2 := by nlinarith
    have h1Γ2 : 1 ≤ Γ ^ 2 := by nlinarith
    have hL1_bound : ε * (2 * ‖Sbε x‖ + Γ * ‖Ebε x‖ + ‖bε x‖) ≤
        2 * Γ ^ 2 * ε * (‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) := by
      have : 2 * ‖Sbε x‖ + Γ * ‖Ebε x‖ + ‖bε x‖ ≤
          2 * Γ ^ 2 * (‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) := by
        nlinarith [norm_nonneg (bε x), norm_nonneg (Sbε x), norm_nonneg (sqrtS Qbε x),
          norm_nonneg (sqrtS Ebε x), mul_le_mul_of_nonneg_left hEε (by linarith : (0 : ℝ) ≤ Γ)]
      calc ε * (2 * ‖Sbε x‖ + Γ * ‖Ebε x‖ + ‖bε x‖)
          ≤ ε * (2 * Γ ^ 2 * (‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖)) :=
            mul_le_mul_of_nonneg_left this hε0.le
        _ = 2 * Γ ^ 2 * ε * (‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) := by ring
    have hcomb : ‖gq x‖ + ‖gη x‖ + ‖d x‖ ≤
        Γ * (‖indBox σ H₁ L₁ (bε - b0) x‖ +
          ‖indBox σ H₁ L₁ (sqrtS (Qbε - Qb0)) x‖ +
          ‖indBox σ H₁ L₁ (sqrtS (Ebε - Eb0)) x‖) +
        2 * Γ ^ 2 * ε * (‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖) := by
      nlinarith [norm_nonneg (indBox σ H₁ L₁ (bε - b0) x)]
    calc ‖B.apply d gq gη x‖ ≤ Γ * (‖gq x‖ + ‖gη x‖ + ‖d x‖) := hB
      _ ≤ Γ * (Γ * (‖indBox σ H₁ L₁ (bε - b0) x‖ +
            ‖indBox σ H₁ L₁ (sqrtS (Qbε - Qb0)) x‖ +
            ‖indBox σ H₁ L₁ (sqrtS (Ebε - Eb0)) x‖) +
          2 * Γ ^ 2 * ε * (‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖)) :=
          mul_le_mul_of_nonneg_left hcomb (by linarith)
      _ = _ := by ring
  · rw [obsOp_apply_eq_zero_of_notMem B _ _ _ hx, norm_zero]
    exact hRHS_nonneg

theorem omega_rate_1_28 {C₁ Γ ε : ℝ} {k₁ : ℕ} (hC₁ : 0 < C₁) (hΓ1 : 1 ≤ Γ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Real.sqrt (C₁ * Γ ^ k₁ * ε ^ (1 / 14 : ℝ)) +
        C₁ * Γ ^ k₁ * ε ^ (1 / 14 : ℝ) + Real.sqrt ε ≤
      (2 * C₁ + 2) * Γ ^ k₁ * ε ^ (1 / 28 : ℝ) := by
  have hΓk1 : 1 ≤ Γ ^ k₁ := one_le_pow₀ hΓ1
  have hε14_le : ε ^ (1 / 14 : ℝ) ≤ ε ^ (1 / 28 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
  have hε2_le : Real.sqrt ε ≤ ε ^ (1 / 28 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
  have hsq_omega : Real.sqrt (C₁ * Γ ^ k₁ * ε ^ (1 / 14 : ℝ)) ≤
      (C₁ + 1) * Γ ^ k₁ * ε ^ (1 / 28 : ℝ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hC₁.le]
    have hsqC : Real.sqrt C₁ ≤ C₁ + 1 := by
      nlinarith [Real.sq_sqrt hC₁.le, sq_nonneg (Real.sqrt C₁ - 1)]
    have hsqΓ : Real.sqrt (Γ ^ k₁) ≤ Γ ^ k₁ := by
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Γ ^ k₁),
        Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < Γ ^ k₁)]
    have hsqε : Real.sqrt (ε ^ (1 / 14 : ℝ)) = ε ^ (1 / 28 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε0.le]
      norm_num
    rw [hsqε]
    have hCG : Real.sqrt C₁ * Real.sqrt (Γ ^ k₁) ≤ (C₁ + 1) * Γ ^ k₁ :=
      mul_le_mul hsqC hsqΓ (Real.sqrt_nonneg _) (by linarith)
    exact mul_le_mul_of_nonneg_right hCG (Real.rpow_nonneg hε0.le _)
  have homega : C₁ * Γ ^ k₁ * ε ^ (1 / 14 : ℝ) ≤ C₁ * Γ ^ k₁ * ε ^ (1 / 28 : ℝ) :=
    mul_le_mul_of_nonneg_left hε14_le (by positivity)
  have hsqe : Real.sqrt ε ≤ 1 * Γ ^ k₁ * ε ^ (1 / 28 : ℝ) := by
    calc Real.sqrt ε ≤ 1 * ε ^ (1 / 28 : ℝ) := by linarith
      _ ≤ (1 * Γ ^ k₁) * ε ^ (1 / 28 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hε0.le _)
  linarith

/-- **Conditional assembly of `HilbertBodyComparison`** (`PartII-b:T16`, SP 1955-1990) from
`CompactFreeBodyRateH2` and `TestedGradientEnergyH2`. -/
theorem hilbertBodyComparison_of (hBody : CompactFreeBodyRateH2)
    (hGrad : TestedGradientEnergyH2) : HilbertBodyComparison := by
  obtain ⟨Cp, hCp, hphys⟩ := phys_graph_poly 2 (by norm_num) (by norm_num)
  obtain ⟨Cf, hCf, hflat⟩ := flat_graph_poly 2 (by norm_num) (by norm_num)
  obtain ⟨k₁, C₁, hC₁, hB1⟩ := hBody
  obtain ⟨k₂, C₂, hC₂, hG2⟩ := hGrad
  have hgap2 : (3 / (2 : ℝ) - 1) / 2 = 1 / 4 := by norm_num
  set K : ℕ := k₁ + k₂ + 6
  set C_tot : ℝ := C₁ + C₂ * (2 * C₁ + 2) + 2 * Cp
  have hC_tot : 0 < C_tot := by positivity
  refine ⟨K, C_tot, hC_tot, ?_⟩
  intro Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap hν hc hσ
    B ε hε0 hε1 hP F bε b0 hF hbε_in hbε_resp hb0_resp hb0_class
  have hgap' : Γ⁻¹ ≤ μ.re + (3 / (2 : ℝ) - 1) / 2 := by rwa [hgap2]
  obtain ⟨Sbε, Qbε, Ebε, hSε, hQε, hEε, mSε, mQε, mEε, hgε⟩ :=
    hphys Γ ν c ε μ hΓ1 hμΓ hgap' hν hc hε0 hε1 hP F bε hF hbε_resp
  obtain ⟨Sb0, Qb0, Eb0, hS0, hQ0, hE0, mS0, mQ0, mE0, hg0⟩ :=
    hflat Γ ν c μ hΓ1 hμΓ hgap' hν hc F b0 hF hb0_resp hb0_class
  have hDbε : HasWeakVec vQ0 dZero bε (dqOf ε bε Sbε Qbε Ebε) :=
    hasWeakVec_dqOf ε hSε hQε hEε
  refine ⟨dqOf ε bε Sbε Qbε Ebε - Qb0, Ebε - Eb0,
    flatCls_hasWeakVec_sub hDbε hQ0, flatCls_hasWeakVec_sub hEε hE0, ?_⟩
  by_cases hne : (obsBox σ H₁ L₁).Nonempty
  · obtain ⟨x₀, ⟨⟨hx₀1, hx₀2⟩, -, ⟨hx₀3, hx₀4⟩⟩⟩ := hne
    have hσH₁ : σ ≤ H₁ := hx₀1.trans hx₀2
    have hL₁0 : 0 ≤ L₁ := (abs_nonneg x₀.2.2).trans (abs_le.mpr ⟨hx₀3, hx₀4⟩)
    set om : ℝ := C₁ * Γ ^ k₁ * ε ^ (1 / 14 : ℝ)
    have hom0 : 0 ≤ om := by positivity
    have hbody_enl := hB1 Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap
      hν hc hσ hσH₁ hL₁0 ε hε0 hε1 hP F bε b0 hF hbε_in hbε_resp hb0_resp hb0_class
    have hbody_box : hNorm c 2 (indBox σ H₁ L₁ (bε - b0)) ≤ ENNReal.ofReal om * hNorm c 2 F :=
      (hNorm_indBox_le_enlarged hσ (bε - b0)).trans hbody_enl
    have hgrad_box := hG2 Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap
      hν hc hσ hσH₁ hL₁0 ε hε0 hε1 hP F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0 hF hbε_in hbε_resp
      hb0_resp hb0_class hSε hQε hEε mSε mQε mEε hS0 hQ0 hE0 mS0 mQ0 mE0 om hom0 hbody_enl
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    set P_d := indBox σ H₁ L₁ (bε - b0)
    set P_Q := indBox σ H₁ L₁ (sqrtS (Qbε - Qb0))
    set P_E := indBox σ H₁ L₁ (sqrtS (Ebε - Eb0))
    have mPd : AEStronglyMeasurable P_d (hMeas c 2) :=
      aestronglyMeasurable_indBox σ H₁ L₁ (hbε_in.meas.sub hb0_class.inHr.meas)
    have mPQ : AEStronglyMeasurable P_Q (hMeas c 2) := by
      have : sqrtS (Qbε - Qb0) = sqrtS Qbε - sqrtS Qb0 := flatCls_sqrtS_sub Qbε Qb0
      dsimp [P_Q]
      rw [this]
      exact aestronglyMeasurable_indBox σ H₁ L₁ (mQε.sub mQ0)
    have mPE : AEStronglyMeasurable P_E (hMeas c 2) := by
      have : sqrtS (Ebε - Eb0) = sqrtS Ebε - sqrtS Eb0 := flatCls_sqrtS_sub Ebε Eb0
      dsimp [P_E]
      rw [this]
      exact aestronglyMeasurable_indBox σ H₁ L₁ (mEε.sub mE0)
    set f_loc : Coord → ℝ := fun x => ‖P_d x‖ + ‖P_Q x‖ + ‖P_E x‖
    set f_ε : Coord → ℝ := fun x => ‖bε x‖ + ‖Sbε x‖ + ‖sqrtS Qbε x‖ + ‖sqrtS Ebε x‖
    have mf_loc : AEStronglyMeasurable f_loc (hMeas c 2) :=
      (mPd.norm.add mPQ.norm).add mPE.norm
    have mf_ε : AEStronglyMeasurable f_ε (hMeas c 2) :=
      ((hbε_in.meas.norm.add mSε.norm).add mQε.norm).add mEε.norm
    have hmono : hNorm c 2 (B.apply (bε - b0) (dqOf ε bε Sbε Qbε Ebε - Qb0) (Ebε - Eb0)) ≤
        eLpNorm ((Γ ^ 2) • f_loc + (2 * Γ ^ 3 * ε) • f_ε) (ENNReal.ofReal 2) (hMeas c 2) := by
      apply eLpNorm_mono_real
      intro x
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, f_loc, f_ε, P_d, P_Q, P_E] using
        obsOp_pointwise_split hσ hσΓ hL₁ hΓ1 hε0 B bε Sbε Qbε Ebε b0 Qb0 Eb0 x
    have hsplit_norm :
        eLpNorm ((Γ ^ 2) • f_loc + (2 * Γ ^ 3 * ε) • f_ε) (ENNReal.ofReal 2) (hMeas c 2) ≤
          ENNReal.ofReal (Γ ^ 2) * eLpNorm f_loc (ENNReal.ofReal 2) (hMeas c 2) +
            ENNReal.ofReal (2 * Γ ^ 3 * ε) * eLpNorm f_ε (ENNReal.ofReal 2) (hMeas c 2) := by
      calc eLpNorm ((Γ ^ 2) • f_loc + (2 * Γ ^ 3 * ε) • f_ε) (ENNReal.ofReal 2) (hMeas c 2)
          ≤ eLpNorm ((Γ ^ 2) • f_loc) (ENNReal.ofReal 2) (hMeas c 2) +
              eLpNorm ((2 * Γ ^ 3 * ε) • f_ε) (ENNReal.ofReal 2) (hMeas c 2) :=
            eLpNorm_add_le (mf_loc.const_smul _) (mf_ε.const_smul _) hp1
        _ = ENNReal.ofReal (Γ ^ 2) * eLpNorm f_loc (ENNReal.ofReal 2) (hMeas c 2) +
              ENNReal.ofReal (2 * Γ ^ 3 * ε) * eLpNorm f_ε (ENNReal.ofReal 2) (hMeas c 2) := by
            rw [eLpNorm_const_smul, eLpNorm_const_smul,
              Real.enorm_eq_ofReal (by positivity), Real.enorm_eq_ofReal (by positivity)]
    have hloc_le : eLpNorm f_loc (ENNReal.ofReal 2) (hMeas c 2) ≤
        hNorm c 2 P_d + (hNorm c 2 P_Q + hNorm c 2 P_E) := by
      calc eLpNorm f_loc (ENNReal.ofReal 2) (hMeas c 2)
          ≤ eLpNorm (fun x => ‖P_d x‖ + ‖P_Q x‖) (ENNReal.ofReal 2) (hMeas c 2) +
              eLpNorm (fun x => ‖P_E x‖) (ENNReal.ofReal 2) (hMeas c 2) :=
            eLpNorm_add_le (mPd.norm.add mPQ.norm) mPE.norm hp1
        _ ≤ (eLpNorm (fun x => ‖P_d x‖) (ENNReal.ofReal 2) (hMeas c 2) +
              eLpNorm (fun x => ‖P_Q x‖) (ENNReal.ofReal 2) (hMeas c 2)) +
              eLpNorm (fun x => ‖P_E x‖) (ENNReal.ofReal 2) (hMeas c 2) :=
            add_le_add (eLpNorm_add_le mPd.norm mPQ.norm hp1) le_rfl
        _ = hNorm c 2 P_d + (hNorm c 2 P_Q + hNorm c 2 P_E) := by
            simp only [eLpNorm_norm, hNorm, add_assoc]
    have h4ε : eLpNorm f_ε (ENNReal.ofReal 2) (hMeas c 2) ≤
        ENNReal.ofReal Γ * (ENNReal.ofReal (Cp * Γ ^ 2) * hNorm c 2 F) :=
      (eLpNorm_add4_norm_le hp1 hbε_in.meas mSε mQε mEε).trans
        (graph_sum_le_of_graphBound hν hνΓ hΓ1 hgε)
    have hloc_F : eLpNorm f_loc (ENNReal.ofReal 2) (hMeas c 2) ≤
        ENNReal.ofReal (om + C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε)) * hNorm c 2 F := by
      calc eLpNorm f_loc (ENNReal.ofReal 2) (hMeas c 2)
          ≤ hNorm c 2 P_d + (hNorm c 2 P_Q + hNorm c 2 P_E) := hloc_le
        _ ≤ ENNReal.ofReal om * hNorm c 2 F +
              ENNReal.ofReal (C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε)) * hNorm c 2 F :=
            add_le_add hbody_box hgrad_box
        _ = ENNReal.ofReal (om + C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε)) * hNorm c 2 F := by
            rw [← add_mul, ENNReal.ofReal_add hom0 (by positivity)]
    have h_all :
        ENNReal.ofReal (Γ ^ 2) * eLpNorm f_loc (ENNReal.ofReal 2) (hMeas c 2) +
          ENNReal.ofReal (2 * Γ ^ 3 * ε) * eLpNorm f_ε (ENNReal.ofReal 2) (hMeas c 2) ≤
        ENNReal.ofReal (Γ ^ 2 * (om + C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε)) +
          2 * Cp * Γ ^ 6 * ε) * hNorm c 2 F := by
      have h1 : ENNReal.ofReal (Γ ^ 2) * eLpNorm f_loc (ENNReal.ofReal 2) (hMeas c 2) ≤
          ENNReal.ofReal (Γ ^ 2 * (om + C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε))) *
            hNorm c 2 F := by
        calc ENNReal.ofReal (Γ ^ 2) * eLpNorm f_loc (ENNReal.ofReal 2) (hMeas c 2)
            ≤ ENNReal.ofReal (Γ ^ 2) *
                (ENNReal.ofReal (om + C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε)) *
                  hNorm c 2 F) := by gcongr
          _ = ENNReal.ofReal (Γ ^ 2 * (om + C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε))) *
                hNorm c 2 F := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      have h2 : ENNReal.ofReal (2 * Γ ^ 3 * ε) * eLpNorm f_ε (ENNReal.ofReal 2) (hMeas c 2) ≤
          ENNReal.ofReal (2 * Cp * Γ ^ 6 * ε) * hNorm c 2 F := by
        calc ENNReal.ofReal (2 * Γ ^ 3 * ε) * eLpNorm f_ε (ENNReal.ofReal 2) (hMeas c 2)
            ≤ ENNReal.ofReal (2 * Γ ^ 3 * ε) *
                (ENNReal.ofReal Γ * (ENNReal.ofReal (Cp * Γ ^ 2) * hNorm c 2 F)) := by gcongr
          _ = ENNReal.ofReal (2 * Cp * Γ ^ 6 * ε) * hNorm c 2 F := by
              rw [← mul_assoc (ENNReal.ofReal Γ), ← ENNReal.ofReal_mul (by positivity),
                ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
              congr 2
              ring
      calc ENNReal.ofReal (Γ ^ 2) * eLpNorm f_loc (ENNReal.ofReal 2) (hMeas c 2) +
            ENNReal.ofReal (2 * Γ ^ 3 * ε) * eLpNorm f_ε (ENNReal.ofReal 2) (hMeas c 2)
          ≤ ENNReal.ofReal (Γ ^ 2 * (om + C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε))) *
              hNorm c 2 F +
            ENNReal.ofReal (2 * Cp * Γ ^ 6 * ε) * hNorm c 2 F := add_le_add h1 h2
        _ = ENNReal.ofReal (Γ ^ 2 * (om + C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε)) +
              2 * Cp * Γ ^ 6 * ε) * hNorm c 2 F := by
            rw [← add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
    refine (hmono.trans (hsplit_norm.trans h_all)).trans ?_
    gcongr
    have homega_bd : Real.sqrt om + om + Real.sqrt ε ≤
        (2 * C₁ + 2) * Γ ^ k₁ * ε ^ (1 / 28 : ℝ) :=
      omega_rate_1_28 (k₁ := k₁) hC₁ hΓ1 hε0 hε1
    have hε14_le : ε ^ (1 / 14 : ℝ) ≤ ε ^ (1 / 28 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
    have hε1_le : ε ≤ ε ^ (1 / 28 : ℝ) := by
      calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
        _ ≤ ε ^ (1 / 28 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
    have hpow1 : Γ ^ 2 * Γ ^ k₁ ≤ Γ ^ K :=
      by rw [← pow_add]; exact pow_le_pow_right₀ hΓ1 (by omega)
    have hpow2 : Γ ^ 2 * (Γ ^ k₂ * Γ ^ k₁) ≤ Γ ^ K :=
      by rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hΓ1 (by omega)
    have hpow3 : Γ ^ 6 ≤ Γ ^ K :=
      pow_le_pow_right₀ hΓ1 (by omega)
    have ht1 : Γ ^ 2 * om ≤ C₁ * Γ ^ K * ε ^ (1 / 28 : ℝ) := by
      calc Γ ^ 2 * (C₁ * Γ ^ k₁ * ε ^ (1 / 14 : ℝ))
          = C₁ * (Γ ^ 2 * Γ ^ k₁) * ε ^ (1 / 14 : ℝ) := by ring
        _ ≤ C₁ * Γ ^ K * ε ^ (1 / 28 : ℝ) := by
            gcongr
    have ht2 : Γ ^ 2 * (C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε)) ≤
        C₂ * (2 * C₁ + 2) * Γ ^ K * ε ^ (1 / 28 : ℝ) := by
      calc Γ ^ 2 * (C₂ * Γ ^ k₂ * (Real.sqrt om + om + Real.sqrt ε))
          ≤ Γ ^ 2 * (C₂ * Γ ^ k₂ * ((2 * C₁ + 2) * Γ ^ k₁ * ε ^ (1 / 28 : ℝ))) := by
            gcongr
        _ = C₂ * (2 * C₁ + 2) * (Γ ^ 2 * (Γ ^ k₂ * Γ ^ k₁)) * ε ^ (1 / 28 : ℝ) := by ring
        _ ≤ C₂ * (2 * C₁ + 2) * Γ ^ K * ε ^ (1 / 28 : ℝ) := by
            gcongr
    have ht3 : 2 * Cp * Γ ^ 6 * ε ≤ 2 * Cp * Γ ^ K * ε ^ (1 / 28 : ℝ) := by
      gcongr
    dsimp [C_tot]
    linarith
  · have hzero : B.apply (bε - b0) (dqOf ε bε Sbε Qbε Ebε - Qb0) (Ebε - Eb0) = 0 := by
      funext x
      have hx : x ∉ obsBox σ H₁ L₁ := fun h => hne ⟨x, h⟩
      exact obsOp_apply_eq_zero_of_notMem B _ _ _ hx
    rw [hNorm, hzero, eLpNorm_zero]
    exact zero_le

end UnforcedLeray.Short.IIb

end
