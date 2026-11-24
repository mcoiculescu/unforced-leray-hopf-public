import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.AMuInAff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.AMu

/-!
# Clause 2 of `FlatLimit`: `‖a_μ‖_𝒜 ≤ C` uniformly in `μ > 0` (source 4709-4730, 4833)
-/

set_option autoImplicit false

noncomputable section

open Set Real
open UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `affNorm` of `a_μ` is at most `Σ_{j≤6}(5/2)^j |D₀| / (μ+5/2)`. -/
theorem affNorm_aMuFun_le (as μ : ℝ) (has : 0 ≤ as) (hμ : 0 < μ) :
    affNorm as (aMuFun μ) ≤ (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
        (frob (fun i j => Dzero i j) / (μ + 5 / 2)) := by
  have hμ2 : 0 < μ + 5 / 2 := by linarith
  unfold affNorm
  apply csSup_le ((nonempty_Ioi (a := (0 : ℝ))).image _)
  rintro _ ⟨s, hs, rfl⟩
  have hs : 0 < s := hs
  have hterm : ∀ j ∈ Finset.range 7, frob (sDerivIter j (aMuFun μ) s) =
      (5 / 2 : ℝ) ^ j * (s ^ (5 / 2 : ℝ) / (μ + 5 / 2)) * frob (fun i j => Dzero i j) := by
    intro j _
    rw [sDerivIter_aMuFun μ j s hs, frobSmulAux,
      abs_of_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
        (div_nonneg (Real.rpow_nonneg hs.le _) hμ2.le))]
  have hS : affSum 6 (aMuFun μ) s = (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
      (s ^ (5 / 2 : ℝ) / (μ + 5 / 2) * frob (fun i j => Dzero i j)) := by
    unfold affSum
    rw [Finset.sum_congr rfl hterm, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hq : s ^ (-(5 / 2 : ℝ)) * (s ^ (5 / 2 : ℝ) / (μ + 5 / 2) * frob (fun i j => Dzero i j))
      = frob (fun i j => Dzero i j) / (μ + 5 / 2) := by
    have hp : s ^ (5 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
    rw [Real.rpow_neg hs.le]
    field_simp
  have hT : affTerm as 6 (aMuFun μ) s = Real.exp (-as * s) *
      ((∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) * (frob (fun i j => Dzero i j) / (μ + 5 / 2))) := by
    unfold affTerm
    rw [hS]
    linear_combination (Real.exp (-as * s) * (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j)) * hq
  have hK : 0 ≤ (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
      (frob (fun i j => Dzero i j) / (μ + 5 / 2)) :=
    mul_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg (by norm_num) _)
      (div_nonneg (Real.sqrt_nonneg _) hμ2.le)
  have he : Real.exp (-as * s) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg has hs.le]
  rw [hT]
  exact mul_le_of_le_one_left hK he

/-- Uniform bound of the pinned `a_μ` in `𝒜`. -/
theorem norm_aMuOp_le (K : ReturnConsts) (has : 0 ≤ K.as) {μ : ℝ} (hμ : 0 < μ) :
    ‖aMuOp K μ‖ ≤ (∑ j ∈ Finset.range 7, (5 / 2 : ℝ) ^ j) *
        (frob (fun i j => Dzero i j) / (5 / 2)) := by
  rw [← affNorm_affIota, affIota_aMuOp has hμ]
  refine (affNorm_aMuFun_le K.as μ has hμ).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun j _ => pow_nonneg (by norm_num) _)
  apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) (by linarith)

end UnforcedLeray.Short.PartIIIb.Concrete
