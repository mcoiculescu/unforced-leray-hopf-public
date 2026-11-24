import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_15

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

namespace PicSizeAux

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

lemma Q_sub {A B : Pl → ℝ} (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) (x : Pl) (t : Fin 7) :
    Q (fun y => A y - B y) x t = Q A x t - Q B x t := by
  fin_cases t
  · rfl
  · exact pd_sub' (c2_diff hA) (c2_diff hB) 0 x
  · exact pd_sub' (c2_diff hA) (c2_diff hB) 1 x
  · exact pd_pd_sub hA hB 0 0 x
  · exact pd_pd_sub hA hB 0 1 x
  · exact pd_pd_sub hA hB 1 0 x
  · exact pd_pd_sub hA hB 1 1 x

lemma tel_Q (u e : ℕ → ℝ) (he : Summable e) (hb : ∀ k, |u (k + 1) - u k| ≤ e k) (n : ℕ) :
    ∑' m, (u (m + n + 1) - u (m + n)) = (∑' k, (u (k + 1) - u k)) - (u n - u 0) := by
  have hsum : Summable (fun k => u (k + 1) - u k) :=
    Summable.of_norm_bounded he (fun k => by rw [Real.norm_eq_abs]; exact hb k)
  have h1 := Summable.sum_add_tsum_nat_add (f := fun k => u (k + 1) - u k) n hsum
  have h2 := Finset.sum_range_sub u n
  try dsimp only at h1
  linarith

lemma sum_abs_tsum_le (E : ℕ → Fin 7 → ℝ) (e : ℕ → ℝ) (he : Summable e)
    (hE : ∀ k t, |E k t| ≤ e k) :
    (∑ t, |∑' k, E k t|) ≤ ∑' k, ∑ t, |E k t| ∧ Summable (fun k => ∑ t, |E k t|) := by
  have hsabs : ∀ t, Summable (fun k => |E k t|) := fun t =>
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => hE k t) he
  have hS : Summable (fun k => ∑ t, |E k t|) := summable_sum (fun t _ => hsabs t)
  refine ⟨?_, hS⟩
  have hnorm : ∀ t, Summable (fun k => ‖E k t‖) := fun t => by
    simpa [Real.norm_eq_abs] using hsabs t
  calc (∑ t, |∑' k, E k t|) ≤ ∑ t, ∑' k, |E k t| := by
        apply Finset.sum_le_sum
        intro t _
        have := norm_tsum_le_tsum_norm (hnorm t)
        simpa [Real.norm_eq_abs] using this
    _ = ∑' k, ∑ t, |E k t| :=
        (Summable.tsum_finsetSum (f := fun t k => |E k t|) (fun t _ => hsabs t)).symm

end PicSizeAux

open PicSizeAux

/-- **Leaf 3 (`/15/3`).** Size of the limit and of its distance to `U n`, from the derivative
identities `DerivConcl`: each of the seven functionals `Q` of `picLim - U n` is the tail of the
telescoped differences, and `W2` is bounded by the sum over the tail of the `W2` increments. -/
theorem picLimSize_proof : UnforcedLeray.Short.IIb.CylPDE.PicLimSize := by
  intro c ν s T v f U B ε H hD
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
  have hQd : ∀ k, ∀ σ ∈ Icc s T, ∀ x : Pl, ∀ t : Fin 7,
      |Q (U (k + 1) σ) x t - Q (U k σ) x t| ≤ ε k := by
    intro k σ hσ x t
    rw [← Q_sub ((hU (k + 1)).c2 σ hσ) ((hU k).c2 σ hσ) x t]
    exact (abs_Q_le _ x t).trans (hdiffW k σ hσ x)
  have hQlim : ∀ σ ∈ Icc s T, ∀ x : Pl, ∀ t : Fin 7,
      Q (picLim U σ) x t = Q (U 0 σ) x t + ∑' k, (Q (U (k + 1) σ) x t - Q (U k σ) x t) := by
    intro σ hσ x t
    fin_cases t
    · rfl
    · exact (hD σ hσ).2.1 0 x
    · exact (hD σ hσ).2.1 1 x
    · exact (hD σ hσ).2.2 0 0 x
    · exact (hD σ hσ).2.2 0 1 x
    · exact (hD σ hσ).2.2 1 0 x
    · exact (hD σ hσ).2.2 1 1 x
  have htail : ∀ n, ∀ σ ∈ Icc s T, ∀ x : Pl,
      W2 (fun y => picLim U σ y - U n σ y) x * Real.cosh x.2 ≤ picTail ε n := by
    intro n σ hσ x
    have hQg : ∀ t : Fin 7, Q (fun y => picLim U σ y - U n σ y) x t
        = ∑' m, (Q (U (m + n + 1) σ) x t - Q (U (m + n) σ) x t) := by
      intro t
      rw [Q_sub (hD σ hσ).1 ((hU n).c2 σ hσ) x t, hQlim σ hσ x t]
      have := tel_Q (fun k => Q (U k σ) x t) (fun k => ε k) hε
        (fun k => hQd k σ hσ x t) n
      try dsimp only at this
      linarith
    have hW : W2 (fun y => picLim U σ y - U n σ y) x
        = ∑ t, |∑' m, (Q (U (m + n + 1) σ) x t - Q (U (m + n) σ) x t)| := by
      rw [W2_eq_sum]
      exact Finset.sum_congr rfl (fun t _ => by rw [hQg t])
    obtain ⟨hlow, hS⟩ := sum_abs_tsum_le
      (fun m t => Q (U (m + n + 1) σ) x t - Q (U (m + n) σ) x t) (fun m => ε (m + n))
      ((summable_nat_add_iff n).mpr hε) (fun m t => hQd (m + n) σ hσ x t)
    have hWm : ∀ m, ∑ t, |Q (U (m + n + 1) σ) x t - Q (U (m + n) σ) x t|
        = W2 (fun y => U (m + n + 1) σ y - U (m + n) σ y) x := by
      intro m
      rw [W2_eq_sum]
      exact Finset.sum_congr rfl (fun t _ => by
        rw [Q_sub ((hU (m + n + 1)).c2 σ hσ) ((hU (m + n)).c2 σ hσ) x t])
    have hεn : Summable (fun m => ε (m + n)) := (summable_nat_add_iff n).mpr hε
    have hWle : ∀ m, W2 (fun y => U (m + n + 1) σ y - U (m + n) σ y) x ≤ ε (m + n) :=
      fun m => hdiffW (m + n) σ hσ x
    have hWs : Summable (fun m => W2 (fun y => U (m + n + 1) σ y - U (m + n) σ y) x) :=
      Summable.of_nonneg_of_le (fun m => W2_nonneg _ _) hWle hεn
    have hW2le : W2 (fun y => picLim U σ y - U n σ y) x
        ≤ ∑' m, W2 (fun y => U (m + n + 1) σ y - U (m + n) σ y) x := by
      rw [hW]
      calc ∑ t, |∑' m, (Q (U (m + n + 1) σ) x t - Q (U (m + n) σ) x t)|
          ≤ ∑' k, ∑ t, |Q (U (k + n + 1) σ) x t - Q (U (k + n) σ) x t| := hlow
        _ = ∑' m, W2 (fun y => U (m + n + 1) σ y - U (m + n) σ y) x :=
          tsum_congr hWm
    have hcosh : 0 ≤ Real.cosh x.2 := (Real.cosh_pos _).le
    have hWle' : ∀ m, W2 (fun y => U (m + n + 1) σ y - U (m + n) σ y) x * Real.cosh x.2
        ≤ ε (m + n) := fun m => hdiff (m + n) σ hσ x
    have hWC : Summable (fun m => W2 (fun y => U (m + n + 1) σ y - U (m + n) σ y) x
        * Real.cosh x.2) :=
      Summable.of_nonneg_of_le (fun m => mul_nonneg (W2_nonneg _ _) hcosh)
        (fun m => hWle' m) hεn
    calc W2 (fun y => picLim U σ y - U n σ y) x * Real.cosh x.2
        ≤ (∑' m, W2 (fun y => U (m + n + 1) σ y - U (m + n) σ y) x) * Real.cosh x.2 :=
          mul_le_mul_of_nonneg_right hW2le hcosh
      _ = ∑' m, W2 (fun y => U (m + n + 1) σ y - U (m + n) σ y) x * Real.cosh x.2 :=
          (tsum_mul_right).symm
      _ ≤ ∑' m, ε (m + n) := Summable.tsum_le_tsum (fun m => hWle' m) hWC hεn
      _ = picTail ε n := rfl
  have hfirst : ∀ σ ∈ Icc s T, ∀ x : Pl,
      W2 (picLim U σ) x * Real.cosh x.2 ≤ B + ∑' k, ε k := by
    intro σ hσ x
    have htri : W2 (picLim U σ) x
        ≤ W2 (U 0 σ) x + W2 (fun y => picLim U σ y - U 0 σ y) x := by
      rw [W2_eq_sum, W2_eq_sum, W2_eq_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro t _
      have h := Q_sub (hD σ hσ).1 ((hU 0).c2 σ hσ) x t
      have e : Q (picLim U σ) x t
          = Q (U 0 σ) x t + Q (fun y => picLim U σ y - U 0 σ y) x t := by
        rw [h]; ring
      rw [e]
      exact abs_add_le _ _
    have hb0 := (hU 0).bound σ hσ x
    have hg0 := htail 0 σ hσ x
    have hpt : picTail ε 0 = ∑' k, ε k := by simp [picTail]
    have hcosh : 0 ≤ Real.cosh x.2 := (Real.cosh_pos _).le
    calc W2 (picLim U σ) x * Real.cosh x.2
        ≤ (W2 (U 0 σ) x + W2 (fun y => picLim U σ y - U 0 σ y) x) * Real.cosh x.2 :=
          mul_le_mul_of_nonneg_right htri hcosh
      _ = W2 (U 0 σ) x * Real.cosh x.2 + W2 (fun y => picLim U σ y - U 0 σ y) x
            * Real.cosh x.2 := by ring
      _ ≤ B + picTail ε 0 := add_le_add hb0 hg0
      _ = B + ∑' k, ε k := by rw [hpt]
  exact ⟨hfirst, htail⟩

end CylPDE

end UnforcedLeray.Short.IIb
