import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/10` (`MollLimit`): domination of `R_k`

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. On a good slice, `|R_k(s)| ≤ N_F(s) + N(s)` (`LMMollDomR`), where
`R_k = ∫_cell Re⟨F, ∇J_k² b⟩`. Pointwise `|Re a Re d + Im a Im d| ≤ |a|² + |d|²`; then
`∂_j (J_k² b)_i = (J_k² G_{·j})_i` (`lmMoll_pd2_eq`), `contr` applied twice columnwise.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `tnorm2 T ^ 2 = ∑ i ∑ j ‖T i j‖²`. -/
lemma domR_tnorm2_sq (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 T ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))

/-- For `f ∈ L²(cell)`, `x ↦ ∑ i ‖f x i‖²` is integrable on the cell. -/
lemma domR_integrable_sum {c : ℝ} {f : LMSpField} (hf : LMCellL2 c f) :
    Integrable (fun x => ∑ i : Fin 2, ‖f x i‖ ^ 2) (volume.restrict (B0579.cell c)) := by
  refine integrable_finsetSum Finset.univ (fun i _ => ?_)
  exact (memLp_two_iff_integrable_sq_norm (hf i).aestronglyMeasurable).mp (hf i)

/-- For `f ∈ L²(cell)` and each `i`, `x ↦ ‖f x i‖²` is integrable on the cell. -/
lemma domR_integrable_entry {c : ℝ} {f : LMSpField} (hf : LMCellL2 c f) (i : Fin 2) :
    Integrable (fun x => ‖f x i‖ ^ 2) (volume.restrict (B0579.cell c)) :=
  (memLp_two_iff_integrable_sq_norm (hf i).aestronglyMeasurable).mp (hf i)

/-- `|Re a Re d + Im a Im d| ≤ |a|² + |d|²`. -/
lemma domR_re_im_bound (a d : ℂ) : |a.re * d.re + a.im * d.im| ≤ ‖a‖ ^ 2 + ‖d‖ ^ 2 := by
  have ha : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hd : ‖d‖ ^ 2 = d.re ^ 2 + d.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [ha, hd, abs_le]
  constructor <;> nlinarith [sq_nonneg (a.re - d.re), sq_nonneg (a.im - d.im),
    sq_nonneg (a.re + d.re), sq_nonneg (a.im + d.im), sq_nonneg a.re, sq_nonneg a.im,
    sq_nonneg d.re, sq_nonneg d.im]

/-- **Domination of `R_k`**: on a good slice, `|R_k(s)| ≤ N_F(s) + N(s)` (with `S` the smooth weak
derivative property, which gives `∂_j J_k(J_k b) = J_k² G`). -/
theorem lmMollDomR (hS : LMSmoothWeakPd) : LMMollDomR := by
  intro c ν μ F b G hD J hJ s hs hgs k
  unfold LMGoodSlice at hgs
  obtain ⟨hb, hcol, hFc⟩ := hgs
  have hA2 : ∀ (x : ℝ × ℝ) (i j : Fin 2),
      LMPd j (fun y => J k (LMMollU J b k s) y i) x = J k (J k (fun y i' => G (s, y) i' j)) x i :=
    fun x i j => lmMoll_pd2_eq (f := fun y => b (s, y)) (g := fun j y i => G (s, y) i j) hS
      hD.pos_c hJ hb hcol (fun i' j' => hD.sol.weakGrad s hs i' j') k i j x
  have hR : LMMollR c J F b k s = ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (J k (J k (fun y i' => G (s, y) i' j)) x i).re +
        (F (s, x) i j).im * (J k (J k (fun y i' => G (s, y) i' j)) x i).im) := by
    unfold LMMollR
    simp only [hA2]
  have hF1 : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖F (s, x) i j‖ ^ 2)
      (volume.restrict (B0579.cell c)) := by
    refine integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => ?_))
    exact domR_integrable_entry (hFc j) i
  have hX2 : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2,
      ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2) (volume.restrict (B0579.cell c)) := by
    refine integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => ?_))
    exact domR_integrable_entry (hJ.memL2 k _ (hJ.memL2 k _ (hcol j))) i
  have hG2 : ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2 ≤ energyN c G s := by
    have hI : ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
        ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2
        = ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2,
          ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2 :=
      integral_congr_ae (ae_of_all _ (fun x => Finset.sum_comm))
    have hL : ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2,
        ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2
        = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
          ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2 :=
      integral_finsetSum Finset.univ (fun j _ =>
        domR_integrable_sum (hJ.memL2 k _ (hJ.memL2 k _ (hcol j))))
    have hbd : ∀ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2
        ≤ ∫ x in B0579.cell c, ∑ i : Fin 2, ‖G (s, x) i j‖ ^ 2 :=
      fun j => (hJ.contr k _ (hJ.memL2 k _ (hcol j))).trans (hJ.contr k _ (hcol j))
    have hRHS : energyN c G s = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖G (s, x) i j‖ ^ 2 := by
      have hI' : ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2, ‖G (s, x) i j‖ ^ 2
          = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2, ‖G (s, x) i j‖ ^ 2 :=
        integral_finsetSum Finset.univ (fun j _ => domR_integrable_sum (hcol j))
      unfold energyN
      simp only [domR_tnorm2_sq]
      rw [← hI']
      exact integral_congr_ae (ae_of_all _ (fun x => Finset.sum_comm))
    rw [hI, hL, hRHS]
    exact Finset.sum_le_sum (fun j _ => hbd j)
  have hFE : energyN c F s = ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2, ‖F (s, x) i j‖ ^ 2 := by
    unfold energyN
    simp only [domR_tnorm2_sq]
  have hpt : ∀ x : ℝ × ℝ, |∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (J k (J k (fun y i' => G (s, y) i' j)) x i).re +
        (F (s, x) i j).im * (J k (J k (fun y i' => G (s, y) i' j)) x i).im)|
      ≤ ∑ i : Fin 2, ∑ j : Fin 2, (‖F (s, x) i j‖ ^ 2 +
          ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2) := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    exact domR_re_im_bound _ _
  have hbound : |∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (J k (J k (fun y i' => G (s, y) i' j)) x i).re +
        (F (s, x) i j).im * (J k (J k (fun y i' => G (s, y) i' j)) x i).im)|
      ≤ ∫ x in B0579.cell c, (∑ i : Fin 2, ∑ j : Fin 2, ‖F (s, x) i j‖ ^ 2 +
          ∑ i : Fin 2, ∑ j : Fin 2, ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2) := by
    refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
      (ae_of_all _ (fun x => abs_nonneg _)) (hF1.add hX2) (ae_of_all _ (fun x => ?_)))
    exact (hpt x).trans (le_of_eq (by simp only [Finset.sum_add_distrib]))
  rw [integral_add hF1 hX2, ← hFE] at hbound
  rw [hR]
  linarith [hG2]

end UnforcedLeray.Short.IIIa
