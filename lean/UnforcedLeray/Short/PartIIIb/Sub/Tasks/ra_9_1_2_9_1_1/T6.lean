import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.Defs

/-!


Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079, 4963-4985.

The summand `hpSummandM` is linear in the entries of `A^y`: `merApply M w = Σ_{a,b} M_{mi a, mi b}
(comp2 w b) e_a`, the derivative `fderiv` of `V_j` in `x` is a continuous linear map, and `toMer`
is additive and homogeneous.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

private lemma t6_toMer_sub (a b : ℝ × ℝ) : toMer (a - b) = toMer a - toMer b := by
  ext i; fin_cases i <;> simp [toMer]

private lemma t6_toMer_smul (r : ℝ) (a : ℝ × ℝ) : toMer (r • a) = r • toMer a := by
  ext i; fin_cases i <;> simp [toMer]

private lemma t6_toMer_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ) :
    toMer (∑ i ∈ s, f i) = ∑ i ∈ s, toMer (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; ext i; fin_cases i <;> simp [toMer]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [← ih]
    ext i; fin_cases i <;> simp [toMer]

/-- Expansion of `merApply` on the meridional basis. -/
private lemma t6_merApply (M : Mat3) (w : ℝ × ℝ) :
    merApply M w = ∑ a : Fin 2, ∑ b : Fin 2, (M (mi a) (mi b) * comp2 w b) • ei a := by
  refine Prod.ext ?_ ?_ <;> simp [merApply, mi, ei, comp2, Fin.sum_univ_two]

/-- A continuous linear map applied to `merApply M w`. -/
private lemma t6_clm_merApply (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (M : Mat3) (w : ℝ × ℝ) :
    L (merApply M w) = ∑ a : Fin 2, ∑ b : Fin 2, (M (mi a) (mi b) * comp2 w b) • L (ei a) := by
  rw [t6_merApply, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_smul]

/-- Sums of `c • toMer (F)` pulled back through `toMer`. -/
private lemma t6_sum_toMer (F : Fin 2 → Fin 2 → ℝ × ℝ) (c : Fin 2 → Fin 2 → ℝ) :
    ∑ a : Fin 2, ∑ b : Fin 2, c a b • toMer (F a b)
      = toMer (∑ a : Fin 2, ∑ b : Fin 2, c a b • F a b) := by
  simp only [t6_toMer_sum, t6_toMer_smul]

theorem hpSummandExpand : HpSummandExpand := by
  intro ν χf A j
  funext p
  simp only [hpSummandM, hpGaussM]
  rw [t6_clm_merApply]
  simp only [t6_merApply]
  simp only [t6_toMer_sub, t6_toMer_sum, t6_toMer_smul, smul_sub, Finset.sum_sub_distrib, smul_smul]

end UnforcedLeray.Short.PartIIIb.Concrete
