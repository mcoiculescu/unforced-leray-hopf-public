import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.CommDerivSplit.TimeReg
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MomentSplit

/-!
# `YBPhase.commDerivSplit` (`PartIII-b:C/rep/8/1/1/2/5/1/1/1`)

Source `the November 2 reference manuscript`
lines 3700-3712, 4195-4215, 5427-5432.

Proves `YBPhase.CommDerivSplit`: at a young receiver `y = ε⁻¹ • xo` on the transition annulus
`ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4`, the commutator `comm = [D_{μ+1}, 𝒞_y]` splits on a
neighborhood of `y` into `commMain + commPsi` for both `Z₁ = srcX0 ν μ (thinSource ε F)` and
`Z₂ = srcX0 ν μ (thinSource ε (meanLift (phaseMean c F)))`, `commPsi` is differentiable at `y`,
and `‖fderiv ℝ (comm ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (comm ν μ ε⁻¹ χy Z₂ τ) y‖ₑ` is bounded by the
weighted order-`0,1,2` differences of `Z₁ - Z₂` plus
`‖fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₁ τ) y - fderiv ℝ (commPsi ν μ ε⁻¹ χy Z₂ τ) y‖ₑ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open YBComm YBPhase FarLeafOrg

/-- **`YBPhase.commDerivSplit`** (`PartIII-b:C/rep/8/1/1/2/5/1/1/1`, source 3700-3712,
4195-4215, 5427-5432). -/
theorem YBPhase.commDerivSplit : YBPhase.CommDerivSplit := by
  intro χy hχ
  obtain ⟨C₀, hC₀0, hmain_sub⟩ := fderiv_commMain_sub_le hχ
  refine ⟨max C₀ 1, by positivity,
    fun ν c ε μ hν hν1 hc hε hε1 hμ _hμ4 F hmeas hper hsupp hN xo hxo1 hxo2 τ => ?_⟩
  set ρo : ℝ := Real.sqrt (5 * ν / 6)
  have hρo : 0 ≤ ρo := Real.sqrt_nonneg _
  have hμ' : -(1 / 4) < μ := by linarith
  have hth₁ : ThinHyp c ρo F := ⟨hmeas, hper, hsupp⟩
  obtain ⟨hm₁, _⟩ := IIIa.sepMomentSplit c hc F hmeas
  have hN₂ : IIIa.thinMoment c (IIIa.meanLift (IIIa.phaseMean c F)) ≠ ⊤ :=
    ne_top_of_le_ne_top hN hm₁
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.phaseMean c F w.1 w.2 i j :=
    IIIa.phaseMean_measurable c F hmeas
  have hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → IIIa.phaseMean c F x' Y = 0 := by
    intro x' Y h
    funext i j
    simp [IIIa.phaseMean, hsupp x' Y _ h]
  have hth₂ : ThinHyp c ρo (IIIa.meanLift (IIIa.phaseMean c F)) :=
    ⟨fun i j => (hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop),
     fun _ _ _ => rfl,
     fun x' Y _ h => hGs x' Y h⟩
  set y : Space := ε⁻¹ • xo
  set r : ℝ := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hy : ρo / ε < ϱ y := by
    have hϱ_y : ϱ y = ε⁻¹ * r := L4_varrho_smul ε⁻¹ (inv_nonneg.2 hε.le) xo
    have hr_lt : ρo < r :=
      lt_of_lt_of_le (Real.sqrt_lt_sqrt (by positivity) (by linarith)) (Real.sqrt_le_sqrt hxo1)
    rw [hϱ_y, div_eq_inv_mul]
    exact mul_lt_mul_of_pos_left hr_lt (inv_pos.2 hε)
  set U : Set Space := {y' : Space | ρo / ε < ϱ y'}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  set Z₁ : ℝ → Space → Space := srcX0 ν μ (IIIa.thinSource ε F)
  set Z₂ : ℝ → Space → Space := srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F)))
  have hZ₁ : ContDiffAt ℝ 2 (Z₁ τ) y :=
    ((thin_X0_contDiffOn_top hν hμ' hε hc hρo hth₁ hN τ).of_le (by simp)).contDiffAt
      (hU.mem_nhds hy)
  have hZ₂ : ContDiffAt ℝ 2 (Z₂ τ) y :=
    ((thin_X0_contDiffOn_top hν hμ' hε hc hρo hth₂ hN₂ τ).of_le (by simp)).contDiffAt
      (hU.mem_nhds hy)
  obtain ⟨hM₁, hM₂, hMain⟩ := hmain_sub ν ε hν hν1 hε hε1 Z₁ Z₂ τ xo hxo1 hxo2 hZ₁ hZ₂
  have heq₁ := thin_comm_eq_add_nhds (R := ε⁻¹) hχ hν hμ' hε hc hρo hth₁ hN τ hy
  have heq₂ := thin_comm_eq_add_nhds (R := ε⁻¹) hχ hν hμ' hε hc hρo hth₂ hN₂ τ hy
  have hdψ₁ := thin_commPsi_diffAt (R := ε⁻¹) hχ hν hμ' hε hc hρo hth₁ hN τ hy
  have hdψ₂ := thin_commPsi_diffAt (R := ε⁻¹) hχ hν hμ' hε hc hρo hth₂ hN₂ τ hy
  exact fderiv_comm_sub_enorm_le_of_reg hC₀0 hν hε hxo1 hM₁ hM₂ hdψ₁ hdψ₂ heq₁ heq₂ hMain

end UnforcedLeray.Short.PartIIIb.Concrete

end
