import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.MainLeibniz.SmoothV

/-!
# Transition-annulus Leibniz decomposition (`YBWidth.sepCommMainLeibniz`)

Proof of `PartIII-b:C/rep/8/1/1/2/5/2/1/1`.
Source `the November 2 reference manuscript`
lines 3700-3712, 4195-4215, 5427-5432.

Combines:
1. `fderiv_commMain_sub_le` (`MainLeibniz/CoeffDeriv.lean`): uniform Leibniz derivative bound for
   `commMain` on the transition annulus `ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4`;
2. `fderiv_comm_eq_add_of_decay` (`MainLeibniz/Split.lean`): pointwise derivative identity
   `fderiv ℝ (comm ν μ R χy Z τ) y = fderiv ℝ (commMain ν R χy Z τ) y + fderiv ℝ (commPsi ν μ R χy Z τ) y`
   for time-independent `C^∞` fields with `O(ϱ^{-4})` far-field derivative decay;
3. `srcX0_meanLift_timeIndep`, `srcX0_meanLift_contDiffOn`, `srcX0_meanLift_decay`
   (`MainLeibniz/SmoothW.lean`): smoothness and decay of `Z₁ = srcX0 ν μ (thinSource ε (meanLift G))`;
4. `newtonX0_contDiffOn`, `newtonX0_decay` (`MainLeibniz/SmoothV.lean`): smoothness and decay of
   `Z₂ = newtonX0 ε μ G`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIIa

namespace YBWidth

open YBComm PhasePrim

/-- **Transition-annulus Leibniz derivative inequality** (`PartIII-b:C/rep/8/1/1/2/5/2/1/1`):
on the transition annulus `ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4`, at `y = ε⁻¹ • xo`,
`‖fderiv (comm Z₁) y - fderiv (comm Z₂) y‖ ≤ C₀ * commMainMaj ν ε r Z₁ Z₂ τ y + ‖fderiv (commPsi Z₁) y - fderiv (commPsi Z₂) y‖`. -/
theorem sepCommMainLeibniz : SepCommMainLeibniz := by
  intro χy hχ
  obtain ⟨C₀, hC₀, hMain⟩ := fderiv_commMain_sub_le hχ
  refine ⟨C₀, hC₀, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 _hμ1 G hGm hGs hwint τ xo hxo1 hxo2 Z₁ Z₂ y r
  set ρo := Real.sqrt (5 * ν / 6)
  have hρo : 0 ≤ ρo := Real.sqrt_nonneg _
  have hρ_lt : ρo < r :=
    lt_of_lt_of_le (Real.sqrt_lt_sqrt (by positivity) (by linarith)) (Real.sqrt_le_sqrt hxo1)
  have hr₀ : 0 ≤ ρo / ε := div_nonneg hρo hε.le
  have hy_rho : ϱ y = ε⁻¹ * r := by
    change ϱ (ε⁻¹ • xo) = ε⁻¹ * r
    rw [ϱ_smul, abs_of_pos (inv_pos.2 hε)]
    rfl
  have hy : ρo / ε < ϱ y := by
    rw [hy_rho, div_eq_inv_mul]
    exact mul_lt_mul_of_pos_left hρ_lt (inv_pos.2 hε)
  have hμ : -(1 / 4) < μ := by linarith
  have hmeas : Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2) := by
    unfold IIIa.tensorNorm
    exact Measurable.sqrt (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => (hGm i j).pow_const 2)
  have hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume := by
    refine Integrable.mono' hwint hmeas.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_of_nonneg (tn_nonneg _)]
    exact le_mul_of_one_le_left (tn_nonneg _) (by linarith [abs_nonneg w.2])
  have hW1_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Z₁ τ) {y' : Space | ρo / ε < ϱ y'} :=
    srcX0_meanLift_contDiffOn hν hc hε hμ hρo G hGm hGs hint τ
  have hW1_dec : ∀ n : ℕ, ∃ C : ℝ, ∀ y' : Space, 2 * (ρo / ε) + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ n (Z₁ τ) y'‖ ≤ C * (ϱ y' ^ 4)⁻¹ :=
    srcX0_meanLift_decay hν hc hε hμ hρo G hGm hGs hint τ
  have hW2_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Z₂ τ) {y' : Space | ρo / ε < ϱ y'} :=
    newtonX0_contDiffOn hε hμ hρo G hGm hGs hint τ
  have hW2_dec : ∀ n : ℕ, ∃ C : ℝ, ∀ y' : Space, 2 * (ρo / ε) + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ n (Z₂ τ) y'‖ ≤ C * (ϱ y' ^ 4)⁻¹ :=
    newtonX0_decay hε hμ hρo G hGm hGs hint τ
  have hZ1_eq : Z₁ = fun _ => Z₁ τ := funext fun t => srcX0_meanLift_timeIndep ν ε μ G t τ
  have hZ2_eq : Z₂ = fun _ => Z₂ τ := rfl
  have hsplit1 : fderiv ℝ (comm ν μ ε⁻¹ χy Z₁ τ) y =
      fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y + fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y := by
    conv_lhs => rw [hZ1_eq]
    conv_rhs => rw [hZ1_eq]
    exact fderiv_comm_eq_add_of_decay hχ hr₀ ν μ ε⁻¹ (Z₁ τ) hW1_cd hW1_dec τ hy
  have hsplit2 : fderiv ℝ (comm ν μ ε⁻¹ χy Z₂ τ) y =
      fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y + fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y :=
    fderiv_comm_eq_add_of_decay hχ hr₀ ν μ ε⁻¹ (Z₂ τ) hW2_cd hW2_dec τ hy
  have hUo : IsOpen {y' : Space | ρo / ε < ϱ y'} := isOpen_lt continuous_const continuous_ϱ
  have hZ1_cd2 : ContDiffAt ℝ 2 (Z₁ τ) y :=
    (hW1_cd.contDiffAt (hUo.mem_nhds hy)).of_le (by simp)
  have hZ2_cd2 : ContDiffAt ℝ 2 (Z₂ τ) y :=
    (hW2_cd.contDiffAt (hUo.mem_nhds hy)).of_le (by simp)
  have hb_main := hMain ν ε hν hν1 hε hε1 Z₁ Z₂ τ xo hxo1 hxo2 hZ1_cd2 hZ2_cd2
  rw [hsplit1, hsplit2]
  have halg : (fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y + fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y) -
      (fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y + fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y) =
      (fderiv ℝ (commMain ν ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commMain ν ε⁻¹ χy Z₂ τ) y) +
      (fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y) := by abel
  rw [halg]
  exact (norm_add_le _ _).trans (add_le_add hb_main le_rfl)

end YBWidth

end UnforcedLeray.Short.PartIIIb.Concrete

end
