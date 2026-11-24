import UnforcedLeray.Short.PartIIa.StatementsNear
import UnforcedLeray.Short.PartIIa.ComposeNear
import UnforcedLeray.Short.PartIIa.Tasks.F16HalfDrift
import UnforcedLeray.Short.PartIIa.Tasks.N01StressMaps
import UnforcedLeray.Short.PartIIa.Sub.N01.Dissipation
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# `Sub/PartII-a_N05`: uniform local regularity of outputs (`NearLocalRegularity`)

Source of record: `the November 2 reference manuscript`,
lines 1751-1799 (`near:local-smoothing` and the local `H¹` body bound).

## Concrete definitions and proved helpers in this file

1. **Unweighted `L²` and weak `H¹(s, q, η)` norms on the periodised box/cell** (`cellMeasure c`):
   * `cellL2Norm c u := (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)`
   * `HasWeakCellH1 c σ H1 L1 U u ds dq deta`: `u` is a `c`-periodic representative of `U`
     supported in `σ ≤ s ≤ H1`, `|η| ≤ L1`, with `u, ds, dq, deta ∈ L²(cellMeasure c)` satisfying
     the distributional integration-by-parts identities against every smooth periodic meridional
     test `φ` (`IsMeridTest c φ`) in the three directions `(pdS, pdQ, pdEta)`.
   * `cellH1Norm c u ds dq deta := cellL2Norm c u + cellL2Norm c ds + cellL2Norm c dq + cellL2Norm c deta`.

2. **Gagliardo / difference-quotient `H^{1/4}(s, q, η)` norm on the periodised box/cell**:
   * `shiftS`, `shiftQ`, `shiftEta`: translations by `h ∈ ℝ` in `(s, q, η)`.
   * `gagliardoDir14 c shift u := (∫ h in Icc (-1 : ℝ) 1, |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)`.
   * `HasCellH14 c σ H1 L1 U u`: `u` is a `c`-periodic representative of `U` supported in
     `σ ≤ s ≤ H1`, `|η| ≤ L1` (hence vanishing for `s ≤ 0`), in `L²(cellMeasure c)`, with
     integrable `|h|^{-3/2}` difference-quotient integrals on `Icc (-1 : ℝ) 1` in all three
     directions `(shiftS, shiftQ, shiftEta)`.
   * `cellH14Norm c u := cellL2Norm c u + gagliardoDir14 c shiftS u + gagliardoDir14 c shiftQ u + gagliardoDir14 c shiftEta u`.

3. **Proved in this file (zero `sorry`)**:
   * `dissipationBound : N01.DissipationBound` assembled unconditionally from `N01.dissipationBound_of`
     and the accepted `N01` leaf theorems;
   * `integrableOn_Icc_abs_rpow_neg_half`, `setIntegral_Icc_abs_rpow_neg_half`:
     `∫ h in Icc (-1 : ℝ) 1, |h| ^ (-(1 / 2 : ℝ)) = 4`;
   * `integrableOn_gagliardo_of_holderHalf`, `gagliardoDir14_le_of_holderHalf`,
     `hasCellH14_of_holderHalf`: any box-supported representative satisfying `O(|h|^{1/2})`
     `L²(cellMeasure c)` difference-quotient bounds (`∫ ‖u(shift h p) - u p‖² ≤ A² |h|` for
     `|h| ≤ 1`, as given by the commuting flow identity of lines 1775-1782) belongs to `HasCellH14`
     with `cellH14Norm c u ≤ 7 * A`;
   * `dsFromS`, `dqFromSQE`, `norm_dsFromS_le`, `norm_dqFromSQE_le`: coordinate conversion
     `∂_s = s⁻¹ S` and `∂_q = Q_ε + ε (2S + η ∂_η + 1)` (lines 1791-1792) with polynomial bounds
     in `Gamma` on the observation box `σ ≤ s ≤ H1`, `|η| ≤ L1`;
   * `nearLocalRegularity_of`: conditional assembly of `NearLocalRegularity` from the four leaf
     obligations `BodyEpsLocalH1`, `BodyFlatLocalH1`, `StressEpsLocalH14`, `StressFlatLocalH14`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-! ### 1. Unconditional `DissipationBound` from `PartII-a:N01` -/

/-- Unconditional dissipation bound (`PartII-a:N01/12`, recorded for `PartII-a:N05`). -/
theorem dissipationBound : N01.DissipationBound :=
  N01.dissipationBound_of N01.phaseSemigroupConj N01.phaseLerayConj N01.phaseDivScale
    N01.cartLiftRows N01.cartLiftNorm N01.tensorTestReIm

/-! ### 2. Concrete `H¹(s, q, η)` and `H^{1/4}(s, q, η)` norms on `cellMeasure c` -/

/-- Unweighted `L²` norm on the cell `(0, ∞) × (0, c] × ℝ` (`cellMeasure c`). -/
def cellL2Norm (c : ℝ) (u : Profile → MeridC) : ℝ :=
  (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)

/-- Weak first derivatives `(ds, dq, deta)` in `(s, q, η)` in the unweighted Lebesgue measure
`cellMeasure c` for an `HSpace c MeridC` element `U` localised to the box `σ ≤ s ≤ H1`,
`|η| ≤ L1`. -/
structure HasWeakCellH1 (c σ H1 L1 : ℝ) (U : HSpace c MeridC)
    (u ds dq deta : Profile → MeridC) : Prop where
  ae_eq : (U : Profile → MeridC) =ᵐ[measureH c] u
  periodic_u : QPeriodic c u
  periodic_ds : QPeriodic c ds
  periodic_dq : QPeriodic c dq
  periodic_deta : QPeriodic c deta
  support_u : ∀ p : Profile, u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1
  support_ds : ∀ p : Profile, ds p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1
  support_dq : ∀ p : Profile, dq p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1
  support_deta : ∀ p : Profile, deta p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1
  memLp_u : MemLp u 2 (cellMeasure c)
  memLp_ds : MemLp ds 2 (cellMeasure c)
  memLp_dq : MemLp dq 2 (cellMeasure c)
  memLp_deta : MemLp deta 2 (cellMeasure c)
  ibp_s : ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (ds p) (φ p) ∂(cellMeasure c) = -∫ p, inner ℂ (u p) (pdS φ p) ∂(cellMeasure c)
  ibp_q : ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (dq p) (φ p) ∂(cellMeasure c) = -∫ p, inner ℂ (u p) (pdQ φ p) ∂(cellMeasure c)
  ibp_eta : ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (deta p) (φ p) ∂(cellMeasure c) = -∫ p, inner ℂ (u p) (pdEta φ p) ∂(cellMeasure c)

/-- Unweighted `H¹(s, q, η)` norm on the periodised box/cell (`cellMeasure c`). -/
def cellH1Norm (c : ℝ) (u ds dq deta : Profile → MeridC) : ℝ :=
  cellL2Norm c u + cellL2Norm c ds + cellL2Norm c dq + cellL2Norm c deta

/-- Coordinate shift in `s`: `(s, q, η) ↦ (s + h, q, η)`. -/
def shiftS (h : ℝ) (p : Profile) : Profile := (p.1 + h, p.2.1, p.2.2)

/-- Coordinate shift in `q`: `(s, q, η) ↦ (s, q + h, η)`. -/
def shiftQ (h : ℝ) (p : Profile) : Profile := (p.1, p.2.1 + h, p.2.2)

/-- Coordinate shift in `η`: `(s, q, η) ↦ (s, q, η + h)`. -/
def shiftEta (h : ℝ) (p : Profile) : Profile := (p.1, p.2.1, p.2.2 + h)

/-- 1D directional Gagliardo `H^{1/4}` difference-quotient seminorm on `cellMeasure c`
(source lines 1781-1786: for `|h| ≤ 1`, square the `L²` difference and integrate against
`|h|^{-3/2}`). -/
def gagliardoDir14 (c : ℝ) (shift : ℝ → Profile → Profile) (u : Profile → MeridC) : ℝ :=
  (∫ h in Icc (-1 : ℝ) 1,
    |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)

/-- Unweighted Gagliardo `H^{1/4}(s, q, η)` norm on the periodised box/cell (`cellMeasure c`). -/
def cellH14Norm (c : ℝ) (u : Profile → MeridC) : ℝ :=
  cellL2Norm c u +
    gagliardoDir14 c shiftS u +
    gagliardoDir14 c shiftQ u +
    gagliardoDir14 c shiftEta u

/-- Membership in `H^{1/4}(s, q, η)` on `cellMeasure c` for an `HSpace c MeridC` element `U`
localised to `σ ≤ s ≤ H1`, `|η| ≤ L1`: `u` is a `c`-periodic representative of `U` supported in
the box, belongs to `L²(cellMeasure c)`, and has integrable `|h|^{-3/2}` difference-quotient
integrals on `Icc (-1 : ℝ) 1` in all three coordinate directions. -/
structure HasCellH14 (c σ H1 L1 : ℝ) (U : HSpace c MeridC) (u : Profile → MeridC) : Prop where
  ae_eq : (U : Profile → MeridC) =ᵐ[measureH c] u
  periodic_u : QPeriodic c u
  support_u : ∀ p : Profile, u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1
  memLp_u : MemLp u 2 (cellMeasure c)
  integrable_s : IntegrableOn
    (fun h : ℝ => |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shiftS h p) - u p‖ ^ 2 ∂(cellMeasure c))
    (Icc (-1 : ℝ) 1) volume
  integrable_q : IntegrableOn
    (fun h : ℝ => |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shiftQ h p) - u p‖ ^ 2 ∂(cellMeasure c))
    (Icc (-1 : ℝ) 1) volume
  integrable_eta : IntegrableOn
    (fun h : ℝ => |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shiftEta h p) - u p‖ ^ 2 ∂(cellMeasure c))
    (Icc (-1 : ℝ) 1) volume

/-! ### 3. Basic properties of `cellL2Norm`, `cellH1Norm`, `gagliardoDir14`, `cellH14Norm` -/

theorem cellL2Norm_nonneg (c : ℝ) (u : Profile → MeridC) : 0 ≤ cellL2Norm c u :=
  Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _

theorem cellH1Norm_nonneg (c : ℝ) (u ds dq deta : Profile → MeridC) :
    0 ≤ cellH1Norm c u ds dq deta := by
  unfold cellH1Norm
  linarith [cellL2Norm_nonneg c u, cellL2Norm_nonneg c ds,
    cellL2Norm_nonneg c dq, cellL2Norm_nonneg c deta]

theorem gagliardoDir14_nonneg (c : ℝ) (shift : ℝ → Profile → Profile) (u : Profile → MeridC) :
    0 ≤ gagliardoDir14 c shift u := by
  unfold gagliardoDir14
  refine Real.rpow_nonneg (integral_nonneg fun h => ?_) _
  exact mul_nonneg (Real.rpow_nonneg (abs_nonneg h) _) (integral_nonneg fun _ => sq_nonneg _)

theorem cellH14Norm_nonneg (c : ℝ) (u : Profile → MeridC) : 0 ≤ cellH14Norm c u := by
  unfold cellH14Norm
  linarith [cellL2Norm_nonneg c u, gagliardoDir14_nonneg c shiftS u,
    gagliardoDir14_nonneg c shiftQ u, gagliardoDir14_nonneg c shiftEta u]

/-! ### 4. Coordinate-derivative conversion on the observation box (source lines 1789-1793) -/

/-- `∂_s u = s⁻¹ S u` (source line 1791). -/
def dsFromS (Sb : Profile → MeridC) (p : Profile) : MeridC :=
  (p.1⁻¹ : ℝ) • Sb p

/-- `∂_q u = Q_ε u + ε (2 S u + η ∂_η u + u)` (source line 1792). -/
def dqFromSQE (ε : ℝ) (b Sb Qb Eb : Profile → MeridC) (p : Profile) : MeridC :=
  Qb p + (ε : ℝ) • ((2 : ℝ) • Sb p + p.2.2 • Eb p + b p)

theorem norm_dsFromS_le {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hμM : 0 ≤ M) (Sb : Profile → MeridC) {p : Profile} (hp : σ ≤ p.1) :
    ‖dsFromS Sb p‖ ≤ Gamma ν c σ H1 L1 M γs χ χ1 * ‖Sb p‖ := by
  have hp0 : 0 < p.1 := lt_of_lt_of_le hσ hp
  have hinv : p.1⁻¹ ≤ σ⁻¹ := inv_anti₀ hσ hp
  have hG : σ⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
    unfold Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  rw [dsFromS, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hp0.le)]
  exact mul_le_mul_of_nonneg_right (hinv.trans hG) (norm_nonneg _)

theorem norm_dqFromSQE_le {ν c σ H1 L1 M γs ε : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hγ : 0 < γs) (hμM : 0 ≤ M)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (b Sb Qb Eb : Profile → MeridC) {p : Profile}
    (hpη : |p.2.2| ≤ L1) :
    ‖dqFromSQE ε b Sb Qb Eb p‖ ≤
      Gamma ν c σ H1 L1 M γs χ χ1 * (‖Qb p‖ + ‖Sb p‖ + ‖Eb p‖ + ‖b p‖) := by
  have hG2 : 2 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
    unfold Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    have : 0 ≤ L1 := (abs_nonneg p.2.2).trans hpη
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hGL : L1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
    unfold Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hηG : |p.2.2| ≤ Gamma ν c σ H1 L1 M γs χ χ1 := hpη.trans hGL
  have h1 : ‖(2 : ℝ) • Sb p + p.2.2 • Eb p + b p‖ ≤
      2 * ‖Sb p‖ + |p.2.2| * ‖Eb p‖ + ‖b p‖ := by
    calc ‖(2 : ℝ) • Sb p + p.2.2 • Eb p + b p‖
        ≤ ‖(2 : ℝ) • Sb p + p.2.2 • Eb p‖ + ‖b p‖ := norm_add_le _ _
      _ ≤ ‖(2 : ℝ) • Sb p‖ + ‖p.2.2 • Eb p‖ + ‖b p‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ = 2 * ‖Sb p‖ + |p.2.2| * ‖Eb p‖ + ‖b p‖ := by
          simp [norm_smul, Real.norm_eq_abs]
  calc ‖dqFromSQE ε b Sb Qb Eb p‖
      ≤ ‖Qb p‖ + ‖(ε : ℝ) • ((2 : ℝ) • Sb p + p.2.2 • Eb p + b p)‖ := norm_add_le _ _
    _ = ‖Qb p‖ + ε * ‖(2 : ℝ) • Sb p + p.2.2 • Eb p + b p‖ := by
        rw [norm_smul, Real.norm_of_nonneg hε0]
    _ ≤ ‖Qb p‖ + 1 * (2 * ‖Sb p‖ + |p.2.2| * ‖Eb p‖ + ‖b p‖) := by
        gcongr
    _ ≤ Gamma ν c σ H1 L1 M γs χ χ1 * (‖Qb p‖ + ‖Sb p‖ + ‖Eb p‖ + ‖b p‖) := by
        have := mul_le_mul_of_nonneg_right hηG (norm_nonneg (Eb p))
        nlinarith [norm_nonneg (Qb p), norm_nonneg (Sb p), norm_nonneg (Eb p), norm_nonneg (b p)]

/-! ### 5. The Gagliardo difference-quotient kernel `|h|^{-3/2}` on `Icc (-1 : ℝ) 1` -/

theorem integrableOn_Ioc_rpow_neg_half :
    IntegrableOn (fun h : ℝ => h ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) volume := by
  have hint : IntervalIntegrable (fun h : ℝ => h ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  simpa [uIoc_of_le (zero_le_one' ℝ)] using hint.1

theorem setIntegral_Ioc_rpow_neg_half :
    ∫ h in Ioc (0 : ℝ) 1, h ^ (-(1 / 2 : ℝ)) = 2 := by
  rw [← intervalIntegral.integral_of_le (zero_le_one' ℝ),
    integral_rpow (Or.inl (by norm_num))]
  norm_num

theorem integrableOn_Icc_abs_rpow_neg_half :
    IntegrableOn (fun h : ℝ => |h| ^ (-(1 / 2 : ℝ))) (Icc (-1 : ℝ) 1) volume := by
  have h_pos : IntegrableOn (fun h : ℝ => |h| ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) volume := by
    refine integrableOn_Ioc_rpow_neg_half.congr_fun (fun h hh => ?_) measurableSet_Ioc
    rw [abs_of_pos hh.1]
  have h_pos_Icc : IntegrableOn (fun h : ℝ => |h| ^ (-(1 / 2 : ℝ))) (Icc (0 : ℝ) 1) volume := by
    rwa [integrableOn_Icc_iff_integrableOn_Ioc]
  have h_neg_Icc : IntegrableOn (fun h : ℝ => |h| ^ (-(1 / 2 : ℝ))) (Icc (-1 : ℝ) 0) volume := by
    have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Icc (0 : ℝ) 1 = Icc (-1 : ℝ) 0 := by
      ext x; simp [mem_Icc]
    rw [← hpre]
    have hcomp := (hmp.integrableOn_comp_preimage (MeasurableEquiv.neg ℝ).measurableEmbedding).2
      h_pos_Icc
    refine hcomp.congr_fun (fun h _ => ?_) (by rw [hpre]; exact measurableSet_Icc)
    simp [Function.comp_apply, abs_neg]
  have hunion : Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) 0 ∪ Ioc (0 : ℝ) 1 :=
    (Icc_union_Ioc_eq_Icc (by norm_num) (by norm_num)).symm
  rw [hunion]
  exact h_neg_Icc.union h_pos

theorem setIntegral_Icc_abs_rpow_neg_half :
    ∫ h in Icc (-1 : ℝ) 1, |h| ^ (-(1 / 2 : ℝ)) = 4 := by
  have h_pos : ∫ h in Ioc (0 : ℝ) 1, |h| ^ (-(1 / 2 : ℝ)) = 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun h hh => by rw [abs_of_pos hh.1])]
    exact setIntegral_Ioc_rpow_neg_half
  have h_pos_Icc : ∫ h in Icc (0 : ℝ) 1, |h| ^ (-(1 / 2 : ℝ)) = 2 := by
    rwa [MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h_neg_Icc : ∫ h in Icc (-1 : ℝ) 0, |h| ^ (-(1 / 2 : ℝ)) = 2 := by
    have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Icc (0 : ℝ) 1 = Icc (-1 : ℝ) 0 := by
      ext x; simp [mem_Icc]
    have heq : ∫ h in Icc (-1 : ℝ) 0, |h| ^ (-(1 / 2 : ℝ)) =
        ∫ h in (Neg.neg : ℝ → ℝ) ⁻¹' Icc (0 : ℝ) 1,
          (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) (-h) := by
      rw [hpre]
      refine setIntegral_congr_fun measurableSet_Icc (fun h _ => by simp [abs_neg])
    rw [heq,
      hmp.setIntegral_preimage_emb (MeasurableEquiv.neg ℝ).measurableEmbedding
        (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) (Icc (0 : ℝ) 1),
      h_pos_Icc]
  have hunion : Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) 0 ∪ Ioc (0 : ℝ) 1 :=
    (Icc_union_Ioc_eq_Icc (by norm_num) (by norm_num)).symm
  have hdisj : Disjoint (Icc (-1 : ℝ) 0) (Ioc (0 : ℝ) 1) :=
    Set.disjoint_left.2 fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hint1 : IntegrableOn (fun h : ℝ => |h| ^ (-(1 / 2 : ℝ))) (Icc (-1 : ℝ) 0) volume :=
    integrableOn_Icc_abs_rpow_neg_half.mono_set (by rw [hunion]; exact subset_union_left)
  have hint2 : IntegrableOn (fun h : ℝ => |h| ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) volume :=
    integrableOn_Icc_abs_rpow_neg_half.mono_set (by rw [hunion]; exact subset_union_right)
  rw [hunion, setIntegral_union hdisj measurableSet_Ioc hint1 hint2, h_neg_Icc, h_pos]
  norm_num

/-- Pointwise bound on the Gagliardo integrand from a 1/2-Hölder `L²` translation estimate
`∫ ‖u(shift h p) - u p‖² ≤ A² |h|` (source lines 1775-1782). -/
theorem gagliardo_integrand_le_of_holderHalf {c A : ℝ} (shift : ℝ → Profile → Profile)
    (u : Profile → MeridC) {h : ℝ}
    (hh : ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤ A ^ 2 * |h|) :
    |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤
      A ^ 2 * |h| ^ (-(1 / 2 : ℝ)) := by
  by_cases h0 : h = 0
  · subst h0
    have hpow : (0 : ℝ) ^ (-(3 / 2 : ℝ)) = 0 := Real.zero_rpow (by norm_num)
    simp [hpow]
  · have hpos : 0 < |h| := abs_pos.2 h0
    calc |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c)
        ≤ |h| ^ (-(3 / 2 : ℝ)) * (A ^ 2 * |h|) :=
          mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hpos.le _)
      _ = A ^ 2 * (|h| ^ (-(3 / 2 : ℝ)) * |h| ^ (1 : ℝ)) := by
          rw [Real.rpow_one]; ring
      _ = A ^ 2 * |h| ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hpos]; norm_num

/-- Integrability of the Gagliardo difference-quotient integrand on `Icc (-1 : ℝ) 1` from a
1/2-Hölder `L²` translation bound. -/
theorem integrableOn_gagliardo_of_holderHalf {c A : ℝ} (shift : ℝ → Profile → Profile)
    (u : Profile → MeridC)
    (hm : AEStronglyMeasurable
      (fun h : ℝ => ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c))
      (volume.restrict (Icc (-1 : ℝ) 1)))
    (hh : ∀ h ∈ Icc (-1 : ℝ) 1,
      ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤ A ^ 2 * |h|) :
    IntegrableOn
      (fun h : ℝ => |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c))
      (Icc (-1 : ℝ) 1) volume := by
  have hmaj : IntegrableOn (fun h : ℝ => A ^ 2 * |h| ^ (-(1 / 2 : ℝ))) (Icc (-1 : ℝ) 1) volume :=
    integrableOn_Icc_abs_rpow_neg_half.const_mul (A ^ 2)
  have hm_all : AEStronglyMeasurable
      (fun h : ℝ => |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c))
      (volume.restrict (Icc (-1 : ℝ) 1)) := by
    have h1 : Measurable (fun h : ℝ => |h| ^ (-(3 / 2 : ℝ))) :=
      (continuous_abs.measurable).pow_const _
    exact h1.aestronglyMeasurable.mul hm
  refine Integrable.mono' hmaj hm_all ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with h hmem
  have hnonneg : 0 ≤ |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c) :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg h) _) (integral_nonneg fun _ => sq_nonneg _)
  rw [Real.norm_of_nonneg hnonneg]
  exact gagliardo_integrand_le_of_holderHalf shift u (hh h hmem)

/-- Bound `gagliardoDir14 c shift u ≤ 2 * A` from a 1/2-Hölder `L²` translation estimate
`∫ ‖u(shift h p) - u p‖² ≤ A² |h|` on `Icc (-1 : ℝ) 1` (source lines 1781-1782). -/
theorem gagliardoDir14_le_of_holderHalf {c A : ℝ} (hA : 0 ≤ A) (shift : ℝ → Profile → Profile)
    (u : Profile → MeridC)
    (hm : AEStronglyMeasurable
      (fun h : ℝ => ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c))
      (volume.restrict (Icc (-1 : ℝ) 1)))
    (hh : ∀ h ∈ Icc (-1 : ℝ) 1,
      ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤ A ^ 2 * |h|) :
    gagliardoDir14 c shift u ≤ 2 * A := by
  have hint := integrableOn_gagliardo_of_holderHalf shift u hm hh
  have hmaj : IntegrableOn (fun h : ℝ => A ^ 2 * |h| ^ (-(1 / 2 : ℝ))) (Icc (-1 : ℝ) 1) volume :=
    integrableOn_Icc_abs_rpow_neg_half.const_mul (A ^ 2)
  have hle : ∫ h in Icc (-1 : ℝ) 1,
      |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤ 4 * A ^ 2 := by
    calc ∫ h in Icc (-1 : ℝ) 1,
          |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c)
        ≤ ∫ h in Icc (-1 : ℝ) 1, A ^ 2 * |h| ^ (-(1 / 2 : ℝ)) := by
          refine setIntegral_mono_on hint hmaj measurableSet_Icc (fun h hmem => ?_)
          exact gagliardo_integrand_le_of_holderHalf shift u (hh h hmem)
      _ = A ^ 2 * ∫ h in Icc (-1 : ℝ) 1, |h| ^ (-(1 / 2 : ℝ)) := integral_const_mul _ _
      _ = 4 * A ^ 2 := by rw [setIntegral_Icc_abs_rpow_neg_half]; ring
  unfold gagliardoDir14
  calc (∫ h in Icc (-1 : ℝ) 1,
        |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (4 * A ^ 2) ^ (1 / 2 : ℝ) := by
        refine Real.rpow_le_rpow ?_ hle (by norm_num)
        exact integral_nonneg fun h => mul_nonneg (Real.rpow_nonneg (abs_nonneg h) _)
          (integral_nonneg fun _ => sq_nonneg _)
    _ = 2 * A := by
        rw [← Real.sqrt_eq_rpow, show (4 : ℝ) * A ^ 2 = (2 * A) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]

/-- Combined criterion for `HasCellH14` and `cellH14Norm c u ≤ 7 * A` from `cellL2Norm c u ≤ A`
and 1/2-Hölder `L²(cellMeasure c)` translation bounds `∫ ‖u(shift h p) - u p‖² ≤ A² |h|` on
`Icc (-1 : ℝ) 1` in the three coordinate directions `(shiftS, shiftQ, shiftEta)`. -/
theorem hasCellH14_of_holderHalf {c σ H1 L1 A : ℝ} (hA : 0 ≤ A)
    (U : HSpace c MeridC) (u : Profile → MeridC)
    (hae : (U : Profile → MeridC) =ᵐ[measureH c] u)
    (hper : QPeriodic c u)
    (hsupp : ∀ p : Profile, u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hmem : MemLp u 2 (cellMeasure c))
    (hL2 : cellL2Norm c u ≤ A)
    (hms : AEStronglyMeasurable
      (fun h : ℝ => ∫ p, ‖u (shiftS h p) - u p‖ ^ 2 ∂(cellMeasure c))
      (volume.restrict (Icc (-1 : ℝ) 1)))
    (hmq : AEStronglyMeasurable
      (fun h : ℝ => ∫ p, ‖u (shiftQ h p) - u p‖ ^ 2 ∂(cellMeasure c))
      (volume.restrict (Icc (-1 : ℝ) 1)))
    (hme : AEStronglyMeasurable
      (fun h : ℝ => ∫ p, ‖u (shiftEta h p) - u p‖ ^ 2 ∂(cellMeasure c))
      (volume.restrict (Icc (-1 : ℝ) 1)))
    (hhs : ∀ h ∈ Icc (-1 : ℝ) 1,
      ∫ p, ‖u (shiftS h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤ A ^ 2 * |h|)
    (hhq : ∀ h ∈ Icc (-1 : ℝ) 1,
      ∫ p, ‖u (shiftQ h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤ A ^ 2 * |h|)
    (hhe : ∀ h ∈ Icc (-1 : ℝ) 1,
      ∫ p, ‖u (shiftEta h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤ A ^ 2 * |h|) :
    HasCellH14 c σ H1 L1 U u ∧ cellH14Norm c u ≤ 7 * A := by
  refine ⟨⟨hae, hper, hsupp, hmem,
    integrableOn_gagliardo_of_holderHalf shiftS u hms hhs,
    integrableOn_gagliardo_of_holderHalf shiftQ u hmq hhq,
    integrableOn_gagliardo_of_holderHalf shiftEta u hme hhe⟩, ?_⟩
  unfold cellH14Norm
  have gs := gagliardoDir14_le_of_holderHalf hA shiftS u hms hhs
  have gq := gagliardoDir14_le_of_holderHalf hA shiftQ u hmq hhq
  have ge := gagliardoDir14_le_of_holderHalf hA shiftEta u hme hhe
  linarith

/-! ### 6. Target statement `NearLocalRegularity` and its four leaf obligations -/

/-- **Leaf 1 (`PartII-a:N05/1`) — local `H¹(s, q, η)` regularity of `χ T_ε b`**
(`the November 2 reference manuscript`,
lines 1789-1793): for every `b ∈ H`, the localised body output
`mulChi (measureH c) χ hm hB (Teps hν hε hc hP μ b)` has weak first derivatives in `(s, q, η)`
on `cellMeasure c` with `cellH1Norm ≤ C Γ^k ‖b‖`. -/
def BodyEpsLocalH1 : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
          ∀ b : HSpace c MeridC,
            ∃ u ds dq deta : Profile → MeridC,
              HasWeakCellH1 c σ H1 L1 (mulChi (measureH c) χ hm hB (Teps hν hε hc hP μ b))
                u ds dq deta ∧
              cellH1Norm c u ds dq deta ≤ C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖b‖

/-- **Leaf 2 (`PartII-a:N05/2`) — local `H¹(s, q, η)` regularity of `χ T_0 b`**
(`the November 2 reference manuscript`,
lines 1794-1799): for every `b ∈ H`, the localised flat body output
`mulChi (measureH c) χ hm hB (T0flat hc ν μ b)` has weak first derivatives in `(s, q, η)` on
`cellMeasure c` with `cellH1Norm ≤ C Γ^k ‖b‖`. -/
def BodyFlatLocalH1 : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ), 0 < ν → ∀ (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ b : HSpace c MeridC,
          ∃ u ds dq deta : Profile → MeridC,
            HasWeakCellH1 c σ H1 L1 (mulChi (measureH c) χ hm hB (T0flat hc ν μ b))
              u ds dq deta ∧
            cellH1Norm c u ds dq deta ≤ C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖b‖

/-- **Leaf 3 (`PartII-a:N05/3`) — local `H^{1/4}(s, q, η)` regularity of `χ S_ε F`**
(`near:local-smoothing`, `the November 2 reference manuscript`,
lines 1752-1756, 1765-1788): for any stress map `Seps` of
`Teps hν hε hc hP μ` and every `F ∈ H_T`, the localised output
`mulChi (measureH c) χ hm hB (Seps F)` has Gagliardo `H^{1/4}(s, q, η)` norm at most
`C Γ^k ‖F‖`. -/
def StressEpsLocalH14 : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
          ∀ Seps : HTSpace c →L[ℂ] HSpace c MeridC,
            IsStressMap c ε (Teps hν hε hc hP μ) Seps →
            ∀ F : HTSpace c,
              ∃ u : Profile → MeridC,
                HasCellH14 c σ H1 L1 (mulChi (measureH c) χ hm hB (Seps F)) u ∧
                cellH14Norm c u ≤ C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖F‖

/-- **Leaf 4 (`PartII-a:N05/4`) — local `H^{1/4}(s, q, η)` regularity of `χ S_0 F`**
(`the November 2 reference manuscript`,
lines 1757-1764, 1785-1788): for any stress map `S0` of `T0flat hc ν μ` and every
`F ∈ H_T`, the localised output `mulChi (measureH c) χ hm hB (S0 F)` has Gagliardo
`H^{1/4}(s, q, η)` norm at most `C Γ^k ‖F‖`. -/
def StressFlatLocalH14 : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ), 0 < ν → ∀ (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ S0 : HTSpace c →L[ℂ] HSpace c MeridC,
          IsStressMap c 0 (T0flat hc ν μ) S0 →
          ∀ F : HTSpace c,
            ∃ u : Profile → MeridC,
              HasCellH14 c σ H1 L1 (mulChi (measureH c) χ hm hB (S0 F)) u ∧
              cellH14Norm c u ≤ C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖F‖

/-- **Uniform local regularity of the outputs (`PartII-a:N05`, source lines 1751-1799)**:
for `T ∈ {Teps, T0flat}` and all `b ∈ H`, the localised output `mulChi χ (T b)` has
`H¹(s, q, η)`-norm `≤ C Γ^k ‖b‖`, and for `S ∈ {Seps, S0}` and all `F ∈ H_T`, the localised
output `mulChi χ (S F)` has `H^{1/4}(s, q, η)`-norm `≤ C Γ^k ‖F‖`. -/
def NearLocalRegularity : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
          (∀ b : HSpace c MeridC,
            (∃ u ds dq deta : Profile → MeridC,
              HasWeakCellH1 c σ H1 L1 (mulChi (measureH c) χ hm hB (Teps hν hε hc hP μ b))
                u ds dq deta ∧
              cellH1Norm c u ds dq deta ≤ C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖b‖) ∧
            (∃ u ds dq deta : Profile → MeridC,
              HasWeakCellH1 c σ H1 L1 (mulChi (measureH c) χ hm hB (T0flat hc ν μ b))
                u ds dq deta ∧
              cellH1Norm c u ds dq deta ≤ C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖b‖)) ∧
          (∀ Seps S0 : HTSpace c →L[ℂ] HSpace c MeridC,
            IsStressMap c ε (Teps hν hε hc hP μ) Seps →
            IsStressMap c 0 (T0flat hc ν μ) S0 →
            ∀ F : HTSpace c,
              (∃ u : Profile → MeridC,
                HasCellH14 c σ H1 L1 (mulChi (measureH c) χ hm hB (Seps F)) u ∧
                cellH14Norm c u ≤ C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖F‖) ∧
              (∃ u : Profile → MeridC,
                HasCellH14 c σ H1 L1 (mulChi (measureH c) χ hm hB (S0 F)) u ∧
                cellH14Norm c u ≤ C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖F‖))

private theorem gamma_one_le {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) : 1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  unfold Gamma GammaBox
  have : 0 < ν⁻¹ := inv_pos.2 hν
  have : 0 < c⁻¹ := inv_pos.2 hc
  have : 0 < σ⁻¹ := inv_pos.2 hσ
  have : 0 < γs⁻¹ := inv_pos.2 hγ
  linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]

/-- **Assembly of `NearLocalRegularity` from the four leaf obligations.** -/
theorem nearLocalRegularity_of (hT1 : BodyEpsLocalH1) (hT0 : BodyFlatLocalH1)
    (hS1 : StressEpsLocalH14) (hS0 : StressFlatLocalH14) : NearLocalRegularity := by
  obtain ⟨k₁, C₁, hC₁, h1⟩ := hT1
  obtain ⟨k₂, C₂, hC₂, h2⟩ := hT0
  obtain ⟨k₃, C₃, hC₃, h3⟩ := hS1
  obtain ⟨k₄, C₄, hC₄, h4⟩ := hS0
  set K := max (max k₁ k₂) (max k₃ k₄)
  set C := C₁ + C₂ + C₃ + C₄
  refine ⟨K, C, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB ε hε hε1 P _ hP hP1 μ hμM hμγ
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 :=
    gamma_one_le χ χ1 hν hc hσ hσH hL1 hγ hM0
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hk₁ : k₁ ≤ K := (le_max_left k₁ k₂).trans (le_max_left _ _)
  have hk₂ : k₂ ≤ K := (le_max_right k₁ k₂).trans (le_max_left _ _)
  have hk₃ : k₃ ≤ K := (le_max_left k₃ k₄).trans (le_max_right _ _)
  have hk₄ : k₄ ≤ K := (le_max_right k₃ k₄).trans (le_max_right _ _)
  have hGK₁ : G ^ k₁ ≤ G ^ K := pow_le_pow_right₀ hG1 hk₁
  have hGK₂ : G ^ k₂ ≤ G ^ K := pow_le_pow_right₀ hG1 hk₂
  have hGK₃ : G ^ k₃ ≤ G ^ K := pow_le_pow_right₀ hG1 hk₃
  have hGK₄ : G ^ k₄ ≤ G ^ K := pow_le_pow_right₀ hG1 hk₄
  have hGK0 : 0 ≤ G ^ K := pow_nonneg (by linarith) K
  constructor
  · intro b
    have hb0 : 0 ≤ ‖b‖ := norm_nonneg b
    constructor
    · obtain ⟨u, ds, dq, deta, hw, hbd⟩ :=
        h1 ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB ε hε hε1 P hP hP1 μ hμM hμγ b
      refine ⟨u, ds, dq, deta, hw, hbd.trans ?_⟩
      calc C₁ * G ^ k₁ * ‖b‖ ≤ C₁ * G ^ K * ‖b‖ := by gcongr
        _ ≤ C * G ^ K * ‖b‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hGK0) hb0
          dsimp [C]; linarith
    · obtain ⟨u, ds, dq, deta, hw, hbd⟩ :=
        h2 ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB μ hμM hμγ b
      refine ⟨u, ds, dq, deta, hw, hbd.trans ?_⟩
      calc C₂ * G ^ k₂ * ‖b‖ ≤ C₂ * G ^ K * ‖b‖ := by gcongr
        _ ≤ C * G ^ K * ‖b‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hGK0) hb0
          dsimp [C]; linarith
  · intro Seps S0 hSe hS0 F
    have hF0 : 0 ≤ ‖F‖ := norm_nonneg F
    constructor
    · obtain ⟨u, hw, hbd⟩ :=
        h3 ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB ε hε hε1 P hP hP1 μ hμM hμγ
          Seps hSe F
      refine ⟨u, hw, hbd.trans ?_⟩
      calc C₃ * G ^ k₃ * ‖F‖ ≤ C₃ * G ^ K * ‖F‖ := by gcongr
        _ ≤ C * G ^ K * ‖F‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hGK0) hF0
          dsimp [C]; linarith
    · obtain ⟨u, hw, hbd⟩ :=
        h4 ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB μ hμM hμγ S0 hS0 F
      refine ⟨u, hw, hbd.trans ?_⟩
      calc C₄ * G ^ k₄ * ‖F‖ ≤ C₄ * G ^ K * ‖F‖ := by gcongr
        _ ≤ C * G ^ K * ‖F‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hGK0) hF0
          dsimp [C]; linarith

end UnforcedLeray.Short.PartIIa
