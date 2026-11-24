import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_15

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

namespace PicContAux

lemma c2_diff {g : Pl → ℝ} (hg : ContDiff ℝ 2 g) : Differentiable ℝ g :=
  hg.differentiable (by norm_num)

lemma diff_pd {g : Pl → ℝ} (hg : ContDiff ℝ 2 g) (j : Fin 2) :
    Differentiable ℝ (B0579.pd j g) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  intro y
  unfold B0579.pd
  exact ((h1.differentiable (by norm_num)) y).clm_apply (differentiableAt_const _)

lemma pd_sub' {A B : Pl → ℝ} (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (j : Fin 2) (x : Pl) :
    B0579.pd j (fun y => A y - B y) x = B0579.pd j A x - B0579.pd j B x := by
  unfold B0579.pd
  show (fderiv ℝ (A - B) x) (B0579.dir j) = _
  rw [fderiv_sub (hA x) (hB x)]
  rfl

lemma pd_pd_sub {A B : Pl → ℝ} (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) (i j : Fin 2)
    (x : Pl) :
    B0579.pd i (B0579.pd j (fun y => A y - B y)) x
      = B0579.pd i (B0579.pd j A) x - B0579.pd i (B0579.pd j B) x := by
  have h : B0579.pd j (fun y => A y - B y) = fun y => B0579.pd j A y - B0579.pd j B y := by
    funext y
    exact pd_sub' (c2_diff hA) (c2_diff hB) j y
  rw [h]
  exact pd_sub' (diff_pd hA j) (diff_pd hB j) i x

/-- The seven weighted functionals of `W2`, indexed by `Fin 7`. -/
def Q (F : Pl → ℝ) (x : Pl) : Fin 7 → ℝ :=
  ![F x, B0579.pd 0 F x, B0579.pd 1 F x, B0579.pd 0 (B0579.pd 0 F) x,
    B0579.pd 0 (B0579.pd 1 F) x, B0579.pd 1 (B0579.pd 0 F) x, B0579.pd 1 (B0579.pd 1 F) x]

lemma W2_eq_sum (F : Pl → ℝ) (x : Pl) : W2 F x = ∑ t, |Q F x t| := by
  rw [Fin.sum_univ_seven]
  unfold W2
  simp [Q]

lemma W2_nonneg (F : Pl → ℝ) (x : Pl) : 0 ≤ W2 F x := by
  rw [W2_eq_sum]
  exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

lemma abs_Q_le (F : Pl → ℝ) (x : Pl) (t : Fin 7) : |Q F x t| ≤ W2 F x := by
  rw [W2_eq_sum]
  exact Finset.single_le_sum (f := fun t => |Q F x t|) (fun i _ => abs_nonneg _)
    (Finset.mem_univ t)

lemma abs_pd_le (G : Pl → ℝ) (x : Pl) (j : Fin 2) : |B0579.pd j G x| ≤ W2 G x := by
  fin_cases j
  · exact abs_Q_le G x 1
  · exact abs_Q_le G x 2

lemma abs_pd2_le (G : Pl → ℝ) (x : Pl) (i j : Fin 2) :
    |B0579.pd i (B0579.pd j G) x| ≤ W2 G x := by
  fin_cases i <;> fin_cases j
  · exact abs_Q_le G x 3
  · exact abs_Q_le G x 4
  · exact abs_Q_le G x 5
  · exact abs_Q_le G x 6

lemma abs_pd_sub_le {A B : Pl → ℝ} (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) (j : Fin 2)
    (x : Pl) : |B0579.pd j A x - B0579.pd j B x| ≤ W2 (fun y => A y - B y) x := by
  rw [← pd_sub' (c2_diff hA) (c2_diff hB) j x]
  exact abs_pd_le _ x j

lemma abs_pd2_sub_le {A B : Pl → ℝ} (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) (i j : Fin 2)
    (x : Pl) :
    |B0579.pd i (B0579.pd j A) x - B0579.pd i (B0579.pd j B) x| ≤ W2 (fun y => A y - B y) x := by
  rw [← pd_pd_sub hA hB i j x]
  exact abs_pd2_le _ x i j

end PicContAux

open PicContAux

/-- **Leaf 2 (`/15/2`).** Periodicity and joint continuity of the limit and of its derivative
series. -/
theorem picLimCont_proof : UnforcedLeray.Short.IIb.CylPDE.PicLimCont := by
  intro c ν s T v f U B ε H
  obtain ⟨hc, hν, hs, hsT, hv, hf, hU, hU0, hUs, hε, hdiff⟩ := H
  have hdiffW : ∀ k, ∀ σ ∈ Icc s T, ∀ x : Pl,
      W2 (fun y => U (k + 1) σ y - U k σ y) x ≤ ε k := by
    intro k σ hσ x
    have h1 := hdiff k σ hσ x
    have h2 := W2_nonneg (fun y => U (k + 1) σ y - U k σ y) x
    have h3 := Real.one_le_cosh x.2
    calc W2 (fun y => U (k + 1) σ y - U k σ y) x
        ≤ W2 (fun y => U (k + 1) σ y - U k σ y) x * Real.cosh x.2 :=
          le_mul_of_one_le_right h2 h3
      _ ≤ ε k := h1
  have per : ∀ n, ∀ σ ∈ Icc s T, ∀ x : Pl, U n σ (x.1 + c, x.2) = U n σ x :=
    fun n σ hσ x => (hU n).periodic σ hσ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ hσ x
    unfold picLim
    rw [per 0 σ hσ x]
    congr 1
    refine tsum_congr (fun n => ?_)
    rw [per (n + 1) σ hσ x, per n σ hσ x]
  · have hsum : ContinuousOn (fun z : ℝ × Pl => ∑' n, (U (n + 1) z.1 z.2 - U n z.1 z.2))
        (Icc s T ×ˢ univ) := by
      refine continuousOn_tsum (u := ε)
        (f := fun n (z : ℝ × Pl) => U (n + 1) z.1 z.2 - U n z.1 z.2)
        (fun n => (hU (n + 1)).cont0.sub (hU n).cont0) hε (fun n z hz => ?_)
      rw [Real.norm_eq_abs]
      have hb := abs_Q_le (fun y => U (n + 1) z.1 y - U n z.1 y) z.2 0
      have hw := hdiffW n z.1 hz.1 z.2
      exact le_trans hb hw
    exact (hU 0).cont0.add hsum
  · intro j
    have hsum : ContinuousOn
        (fun z : ℝ × Pl => ∑' n, (B0579.pd j (U (n + 1) z.1) z.2 - B0579.pd j (U n z.1) z.2))
        (Icc s T ×ˢ univ) := by
      refine continuousOn_tsum (u := ε)
        (f := fun n (z : ℝ × Pl) => B0579.pd j (U (n + 1) z.1) z.2 - B0579.pd j (U n z.1) z.2)
        (fun n => ((hU (n + 1)).cont1 j).sub ((hU n).cont1 j)) hε (fun n z hz => ?_)
      rw [Real.norm_eq_abs]
      have hb := abs_pd_sub_le ((hU (n + 1)).c2 z.1 hz.1) ((hU n).c2 z.1 hz.1) j z.2
      have hw := hdiffW n z.1 hz.1 z.2
      exact le_trans hb hw
    exact ((hU 0).cont1 j).add hsum
  · intro i j
    have hsum : ContinuousOn
        (fun z : ℝ × Pl => ∑' n, (B0579.pd i (B0579.pd j (U (n + 1) z.1)) z.2
          - B0579.pd i (B0579.pd j (U n z.1)) z.2))
        (Icc s T ×ˢ univ) := by
      refine continuousOn_tsum (u := ε)
        (f := fun n (z : ℝ × Pl) => B0579.pd i (B0579.pd j (U (n + 1) z.1)) z.2
          - B0579.pd i (B0579.pd j (U n z.1)) z.2)
        (fun n => ((hU (n + 1)).cont2 i j).sub ((hU n).cont2 i j)) hε (fun n z hz => ?_)
      rw [Real.norm_eq_abs]
      have hb := abs_pd2_sub_le ((hU (n + 1)).c2 z.1 hz.1) ((hU n).c2 z.1 hz.1) i j z.2
      have hw := hdiffW n z.1 hz.1 z.2
      exact le_trans hb hw
    exact ((hU 0).cont2 i j).add hsum

end CylPDE

end UnforcedLeray.Short.IIb
