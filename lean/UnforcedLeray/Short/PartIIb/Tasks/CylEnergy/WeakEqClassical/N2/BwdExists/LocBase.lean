import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1.Route

/-!
# Part II-b, task `PartII-b:T22/2/3/1/4` (`LocBase`): the Picard class is `LocCk 2` on every band

Source: `the November 2 reference manuscript` lines 2100-2105.  The Picard class
`PicClass c 0 T B u` (from `DuhamelSol.cls`) gives `C²` slices, the joint continuity of `u`, of
`∂_j u` and of `∂_i ∂_j u`, and `W2 · cosh ≤ B`.  Every word of length `≤ 2` is bounded by `W2`,
hence by `B`, and the band restriction is only a restriction of these continuity statements.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.BwdRoute

open CylPDE

/-- `W2 g x ≤ B` from `W2 g x * cosh x₂ ≤ B`. -/
theorem lb_W2_le {g : Pl → ℝ} {x : Pl} {B : ℝ} (h : W2 g x * Real.cosh x.2 ≤ B) :
    W2 g x ≤ B := by
  have h0 : 0 ≤ W2 g x := by unfold W2; positivity
  exact le_trans (le_mul_of_one_le_right h0 (Real.one_le_cosh _)) h

/-- `|∂_j g x| ≤ W2 g x`. -/
theorem lb_abs_pd1 (j : Fin 2) (g : Pl → ℝ) (x : Pl) : |B0579.pd j g x| ≤ W2 g x := by
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  unfold W2
  rcases hj with rfl | rfl <;>
    linarith [abs_nonneg (g x), abs_nonneg (B0579.pd 0 g x), abs_nonneg (B0579.pd 1 g x),
      abs_nonneg (B0579.pd 0 (B0579.pd 0 g) x), abs_nonneg (B0579.pd 0 (B0579.pd 1 g) x),
      abs_nonneg (B0579.pd 1 (B0579.pd 0 g) x), abs_nonneg (B0579.pd 1 (B0579.pd 1 g) x)]

/-- `|∂_i ∂_j g x| ≤ W2 g x`. -/
theorem lb_abs_pd2 (i j : Fin 2) (g : Pl → ℝ) (x : Pl) :
    |B0579.pd i (B0579.pd j g) x| ≤ W2 g x := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  unfold W2
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    linarith [abs_nonneg (g x), abs_nonneg (B0579.pd 0 g x), abs_nonneg (B0579.pd 1 g x),
      abs_nonneg (B0579.pd 0 (B0579.pd 0 g) x), abs_nonneg (B0579.pd 0 (B0579.pd 1 g) x),
      abs_nonneg (B0579.pd 1 (B0579.pd 0 g) x), abs_nonneg (B0579.pd 1 (B0579.pd 1 g) x)]

/-- **Leaf `T22/2/3/1/4`** (SP 2100-2105): the Picard class of `DuhamelSol` is `LocCk 2` on every
band. -/
theorem _root_.locBase : UnforcedLeray.Short.IIb.BwdRoute.LocBase := by
  intro c ν T w f u hd ρ
  obtain ⟨B, hB⟩ := hd.mild.cls
  refine ⟨fun σ hσ => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · have h := (hB.c2 σ hσ).contDiffOn.mono (subset_univ (band ρ))
    exact_mod_cast h
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · exact hB.cont0.mono (Set.prod_mono subset_rfl (subset_univ _))
    · exact (hB.cont1 i).mono (Set.prod_mono subset_rfl (subset_univ _))
    · exact (hB.cont2 i j).mono (Set.prod_mono subset_rfl (subset_univ _))
    · exfalso
      have h3 : (i :: j :: k :: l).length = l.length + 1 + 1 + 1 := rfl
      omega
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · refine ⟨B, fun σ hσ x _ => ?_⟩
      exact (abs_le_W2 _ _).trans (lb_W2_le (hB.bound σ hσ x))
    · refine ⟨B, fun σ hσ x _ => ?_⟩
      exact (lb_abs_pd1 i _ x).trans (lb_W2_le (hB.bound σ hσ x))
    · refine ⟨B, fun σ hσ x _ => ?_⟩
      exact (lb_abs_pd2 i j _ x).trans (lb_W2_le (hB.bound σ hσ x))
    · exfalso
      have h3 : (i :: j :: k :: l).length = l.length + 1 + 1 + 1 := rfl
      omega

end UnforcedLeray.Short.IIb.BwdRoute

#print axioms locBase
