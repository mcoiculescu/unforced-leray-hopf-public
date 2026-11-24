import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements
import UnforcedLeray.Short.PartIIb.Sub.B1
import UnforcedLeray.Short.PartIIb.Tasks.OrdRelUnique.TestElemLimit
import UnforcedLeray.Short.PartIIb.Tasks.OrdRelUnique.CutoffTailSmall
import UnforcedLeray.Short.PartIIa.Sub.F05
import UnforcedLeray.Units.B0412
import UnforcedLeray.Lib.LerayLp.Cutoff

/-!
# `uniformCutoffLimitPairing`: Hoelder pairing of the cut-off tail error

Proves `UniformCutoffLimitPairing` (`Statements.lean`), source lines 1446-1455.
The slice error is bounded by `max K 0 * ((1 - χ_{(n+1)/2}) (1+|y|)⁻²)`; its `L^{11/7}` norm
tends to zero by `IIb.cutoffTailSmall` applied to `F y = (1+|y|)⁻² e₀` along `R_n = (n+1)/2`.
Then `IIb.phasePairLimit_of IIb.testElemLimit` gives the pairing limit.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

theorem uniformCutoffLimitPairing :
    UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.UniformCutoffLimitPairing := by
  intro P hP Θ Θ' K hΘ hΘ' hbd d
  -- the exponent `q₀' = conjExp q₀ = 11/7`
  have hcj : (conjExp q0E).toReal = 11 / 7 := by
    have hq0gt : (1 : ℝ≥0∞) < q0E := one_lt_q0E
    have hq0ne : q0E ≠ ⊤ := q0E_ne_top
    rw [UnforcedLeray.Short.PartIIa.toReal_conjExp hq0gt hq0ne, q0E_toReal]
    norm_num
  have hq1 : (1 : ℝ≥0∞) ≤ conjExp q0E := UnforcedLeray.Short.IIb.fact_one_le_conjExp_q0E_B1.out
  have hqne : conjExp q0E ≠ ⊤ := conjExp_ne_top one_lt_q0E
  have hq0 : conjExp q0E ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  -- the power weight `(1+|y|)⁻²` lies in `L^{11/7}`
  have hpw : MemLp (fun y : Space => powWeight 2 y) (conjExp q0E) volume :=
    memLp_powWeight (by norm_num) hq0 (Or.inr (by rw [hcj]; norm_num))
  -- the tail test `F y = (1+|y|)⁻² e₀` is in `L^{11/7}`
  have hF : MemLp (fun y : Space => powWeight 2 y • coordinateVector (0 : Fin 3))
      (conjExp q0E) volume :=
    hpw.of_le ((hpw.aestronglyMeasurable).smul_const _)
      (Filter.Eventually.of_forall fun y => by
        simp [norm_smul, RieszLp.norm_coordinateVector])
  -- the cut-off error of `F` has the norm of the scalar tail
  have htail_eq : ∀ R : ℝ,
      eLpNorm (fun y : Space => powWeight 2 y • coordinateVector (0 : Fin 3)
          - cutoff R y • (powWeight 2 y • coordinateVector (0 : Fin 3)))
        (conjExp q0E) volume
        = eLpNorm (fun y : Space => (1 - cutoff R y) * powWeight 2 y) (conjExp q0E) volume := by
    intro R
    rw [← eLpNorm_norm]
    congr 1
    funext y
    have h0 := cutoff_nonneg R y
    have h1 := cutoff_le_one R y
    rw [show powWeight 2 y • coordinateVector (0 : Fin 3)
          - cutoff R y • (powWeight 2 y • coordinateVector (0 : Fin 3))
        = ((1 - cutoff R y) * powWeight 2 y) • coordinateVector (0 : Fin 3) by module]
    rw [norm_smul, RieszLp.norm_coordinateVector, mul_one,
      Real.norm_of_nonneg (mul_nonneg (by linarith) (powWeight_nonneg 2 y))]
  -- the tail tends to zero along all `R`
  have hTail : Tendsto
      (fun R : ℝ => eLpNorm (fun y : Space => (1 - cutoff R y) * powWeight 2 y)
        (conjExp q0E) volume) atTop (𝓝 0) := by
    have h := UnforcedLeray.Short.IIb.cutoffTailSmall
      (fun y : Space => powWeight 2 y • coordinateVector (0 : Fin 3)) hF
    exact Tendsto.congr (fun R => htail_eq R) h
  -- along `R_n = (n+1)/2`
  have hRn : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / 2) atTop atTop := by
    apply Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hTn : Tendsto
      (fun n : ℕ => eLpNorm (fun y : Space => (1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y)
        (conjExp q0E) volume) atTop (𝓝 0) :=
    hTail.comp hRn
  -- pointwise slice bound, with the constant `max K 0`
  have hdiff : ∀ (n : ℕ) (τ : ℝ),
      eLpNorm (fun y : Space => Θ n (τ, y) - Θ' (τ, y)) (conjExp q0E) volume
        ≤ ‖max K 0‖ₑ * eLpNorm
            (fun y : Space => (1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y)
            (conjExp q0E) volume := by
    intro n τ
    have hpt : ∀ y : Space, ‖Θ n (τ, y) - Θ' (τ, y)‖
        ≤ max K 0 * ((1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y) := by
      intro y
      have ha : 0 ≤ (1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y :=
        mul_nonneg (by linarith [cutoff_le_one (((n : ℝ) + 1) / 2) y]) (powWeight_nonneg 2 y)
      calc ‖Θ n (τ, y) - Θ' (τ, y)‖
          ≤ K * ((1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y) := hbd n τ y
        _ ≤ max K 0 * ((1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y) :=
            mul_le_mul_of_nonneg_right (le_max_left K 0) ha
    calc eLpNorm (fun y : Space => Θ n (τ, y) - Θ' (τ, y)) (conjExp q0E) volume
        ≤ eLpNorm (fun y : Space => max K 0 * ((1 - cutoff (((n : ℝ) + 1) / 2) y)
            * powWeight 2 y)) (conjExp q0E) volume := eLpNorm_mono_real hpt
      _ ≤ ‖max K 0‖ₑ * eLpNorm (fun y : Space => (1 - cutoff (((n : ℝ) + 1) / 2) y)
            * powWeight 2 y) (conjExp q0E) volume := by
            have := eLpNorm_const_smul_le (c := max K 0)
              (f := fun y : Space => (1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y)
              (p := conjExp q0E) (μ := volume)
            simpa [Pi.smul_def, smul_eq_mul] using this
  -- uniform bound: the tail is dominated by the `L^{11/7}` norm of `(1+|y|)⁻²`
  have hM : eLpNorm (fun y : Space => powWeight 2 y) (conjExp q0E) volume < ⊤ :=
    hpw.eLpNorm_lt_top
  have hamono : ∀ (n : ℕ),
      eLpNorm (fun y : Space => (1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y)
        (conjExp q0E) volume ≤ eLpNorm (fun y : Space => powWeight 2 y) (conjExp q0E) volume := by
    intro n
    refine eLpNorm_mono_real (fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (by linarith [cutoff_le_one (((n : ℝ) + 1) / 2) y])
      (powWeight_nonneg 2 y))]
    exact mul_le_of_le_one_left (powWeight_nonneg 2 y)
      (by linarith [cutoff_nonneg (((n : ℝ) + 1) / 2) y])
  have hB : ‖max K 0‖ₑ * eLpNorm (fun y : Space => powWeight 2 y) (conjExp q0E) volume ≠ ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top hM.ne
  have hbdC : ∃ C : ℝ, ∀ n : ℕ, ∀ τ ∈ Icc (0 : ℝ) P,
      eLpNorm (fun y : Space => Θ n (τ, y) - Θ' (τ, y)) (conjExp q0E) volume
        ≤ ENNReal.ofReal C := by
    refine ⟨(‖max K 0‖ₑ * eLpNorm (fun y : Space => powWeight 2 y) (conjExp q0E) volume).toReal,
      fun n τ _ => ?_⟩
    rw [ENNReal.ofReal_toReal hB]
    have hn := hamono n
    exact (hdiff n τ).trans (by gcongr)
  -- convergence for each phase
  have hlim : ∀ τ ∈ Icc (0 : ℝ) P, Tendsto
      (fun n : ℕ => eLpNorm (fun y : Space => Θ n (τ, y) - Θ' (τ, y)) (conjExp q0E) volume)
      atTop (𝓝 0) := by
    intro τ _
    have hc : ‖max K 0‖ₑ ≠ ⊤ := enorm_ne_top
    have hup := ENNReal.Tendsto.const_mul hTn (Or.inr hc)
    rw [mul_zero] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => bot_le) (fun n => hdiff n τ)
  exact UnforcedLeray.Short.IIb.phasePairLimit_of UnforcedLeray.Short.IIb.testElemLimit P Θ Θ'
    (fun n => (hΘ n).isSliceTest (conjExp q0E)) hΘ' hlim hbdC d

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
