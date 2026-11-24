import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.Defs
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.T3
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.T4
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T7
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T8
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T11
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T12
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_2.Calc3

/-!
# `psiSummandBound` (task `PartIII-b:C/asrc/ra/9/1/2/9/2/1/6`)

Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079, 4979.

Scalar mirror of `hpSummandBound` (Hp task 12). The summand is `Σ_{a,b} A^y_{mi a, mi b}(s) · psiGauss a b`
(`psiSummandExpand`), a sum of four products of a `C⁴` function of `s` with a scalar `C⁴` function on
`UChart`. Each word of the summand is linear over this sum (`wordW_add`), and each product obeys the
scalar Leibniz bound `t6_scalar_leibniz`, obtained from the Merid-valued `wordW_smul_bound` by embedding
scalars with the linear map `Lth` (`wordW_clm`, `norm_Lth`). The entries of `A^y` vanish for `νs ≥ 11/10`
(`ayEntryBound`), so the term is zero there; for `νs ≤ 11/10` the Gaussian words use `psiGaussWordBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `psiGauss` is `C⁴` on `UChart` for `ν > 0` (copy of `psiGaussSmooth_pos`, task 5). -/
lemma t6_psiGaussSmooth (ν : ℝ) (hν : 0 < ν) (j : ℤ) (a b : Fin 2) :
    ContDiffOn ℝ 4 (psiSummandGauss ν j a b) UChart := by
  have hA : ∀ p ∈ UChart, 1 + ν * p.1 ≠ 0 := by
    intro p hp
    have : 0 < p.1 := hp.1
    positivity
  unfold psiSummandGauss
  fin_cases a <;> fin_cases b <;>
  · simp [comp2, xj, sq2, ageA, cOf]
    fun_prop (disch := (intro x hx; have h := hA x hx; simp [h]))

/-- The `(a,b)`-th product term of the summand, as a chart function. -/
def t6F (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (a b : Fin 2) : Chart → ℝ :=
  fun p => Ay ν χf A p.1 (mi a) (mi b) * psiSummandGauss ν j a b p

/-- Scalar Leibniz bound: a product of a `C⁴` function of `s` with a scalar `C⁴` function on `UChart`,
obtained from `wordW_smul_bound` through the linear embedding `Lth : ℝ → Merid`. -/
lemma t6_scalar_leibniz (a : ℝ → ℝ) (g : Chart → ℝ) (ha : ContDiffOn ℝ 4 a (Set.Ioi 0))
    (hg : ContDiffOn ℝ 4 g UChart) (w : List (Fin 3)) (hw : w ∈ budgetWords) (q : Chart)
    (hq : q ∈ UChart) :
    |wordW w (fun p : Chart => a p.1 * g p) q| ≤ 16 * (∑ i ∈ Finset.range 5, |sDerivIterR i a q.1|) *
      ∑ w' ∈ budgetWords, |wordW w' g q| := by
  have hlen : w.length ≤ 4 := wsb_mem_budget_iff.mp hw
  have hA : ContDiffOn ℝ 4 (fun p : Chart => a p.1) UChart :=
    ha.comp contDiffOn_fst (fun p hp => hp.1)
  have hprod : ContDiffOn ℝ 4 (fun p : Chart => a p.1 * g p) UChart := hA.mul hg
  have hprodW : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) (fun p : Chart => a p.1 * g p) UChart :=
    hprod.of_le (by exact_mod_cast hlen)
  have hgW : ∀ w' ∈ budgetWords, ContDiffOn ℝ ((w'.length : ℕ) : WithTop ℕ∞) g UChart :=
    fun w' hw' => hg.of_le (by exact_mod_cast wsb_mem_budget_iff.mp hw')
  have hG : ContDiffOn ℝ 4 (fun p : Chart => Lth (g p)) UChart :=
    Lth.contDiff.comp_contDiffOn hg
  have hsm : ‖wordW w (fun p : Chart => a p.1 • Lth (g p)) q‖
      ≤ 16 * (∑ i ∈ Finset.range 5, |sDerivIterR i a q.1|) *
        ∑ w' ∈ budgetWords, ‖wordW w' (fun p : Chart => Lth (g p)) q‖ :=
    wordW_smul_bound a (fun p : Chart => Lth (g p)) ha hG w hw q hq
  have hfun : (fun p : Chart => a p.1 • Lth (g p)) = fun p : Chart => Lth (a p.1 * g p) := by
    funext p
    rw [← map_smul, smul_eq_mul]
  have e1 : wordW w (fun p : Chart => Lth (a p.1 * g p)) q
      = Lth (wordW w (fun p : Chart => a p.1 * g p) q) :=
    wordW_clm Lth w hprodW q hq
  have e2 : ∀ w' ∈ budgetWords, wordW w' (fun p : Chart => Lth (g p)) q = Lth (wordW w' g q) :=
    fun w' hw' => wordW_clm Lth w' (hgW w' hw') q hq
  have hS : ∑ w' ∈ budgetWords, ‖wordW w' (fun p : Chart => Lth (g p)) q‖
      = ∑ w' ∈ budgetWords, |wordW w' g q| :=
    Finset.sum_congr rfl (fun w' hw' => by rw [e2 w' hw', norm_Lth])
  have hL : |wordW w (fun p : Chart => a p.1 * g p) q|
      = ‖wordW w (fun p : Chart => a p.1 • Lth (g p)) q‖ := by
    rw [hfun, e1, norm_Lth]
  rw [hL, ← hS]
  exact hsm

/-- Four-term additivity of words on `UChart`. -/
lemma t6_wordW_four (w : List (Fin 3)) (F1 F2 F3 F4 : Chart → ℝ) (hw : w.length ≤ 4)
    (h1 : ContDiffOn ℝ 4 F1 UChart) (h2 : ContDiffOn ℝ 4 F2 UChart)
    (h3 : ContDiffOn ℝ 4 F3 UChart) (h4 : ContDiffOn ℝ 4 F4 UChart) (q : Chart) (hq : q ∈ UChart) :
    wordW w (F1 + F2 + F3 + F4) q
      = wordW w F1 q + wordW w F2 q + wordW w F3 q + wordW w F4 q := by
  have c : ∀ F : Chart → ℝ, ContDiffOn ℝ 4 F UChart →
      ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) F UChart :=
    fun F hF => hF.of_le (by exact_mod_cast hw)
  have c12 : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) (F1 + F2) UChart :=
    (c F1 h1).add (c F2 h2)
  have c123 : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) (F1 + F2 + F3) UChart :=
    c12.add (c F3 h3)
  rw [wordW_add w c123 (c F4 h4) q hq, wordW_add w c12 (c F3 h3) q hq,
    wordW_add w (c F1 h1) (c F2 h2) q hq]

/-- Word bound for one product term `A^y_{ab}(s) · psiGauss a b`. -/
lemma t6_term_bound (as : ℝ) (χf : ℝ → ℝ) (Cg : ℝ) (mg : ℕ) (hCg : 0 ≤ Cg)
    (hG : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 0 < s → ν * s ≤ 11 / 10 → ∀ w ∈ budgetWords,
      ∀ (a b : Fin 2) (x : ℝ × ℝ) (j : ℤ),
        |wordW w (psiSummandGauss ν j a b) (s, x)| ≤ Cg * envTerm mg ν j (s, x))
    (hχ : IsSourceCutoffC χf) (ν : ℝ) (hν : 0 < ν) (A : ℝ → Mat3) (hA : IsAffElem as A)
    (s : ℝ) (hs : 0 < s) (w : List (Fin 3)) (hw : w ∈ budgetWords) (x : ℝ × ℝ) (j : ℤ)
    (a b : Fin 2) :
    |wordW w (t6F ν χf A j a b) (s, x)|
      ≤ 80 * (budgetWords.card : ℝ) * Cg * affM ν χf A * s ^ (5 / 2 : ℝ) * envTerm mg ν j (s, x) := by
  have hq : (s, x) ∈ UChart := ⟨hs, Set.mem_univ _⟩
  have hAy6 : ContDiffOn ℝ 6 (Ay ν χf A) (Ioi 0) := t12_Ay6 as χf hχ ν A hA
  have hsm : |wordW w (fun p : Chart => Ay ν χf A p.1 (mi a) (mi b) * psiSummandGauss ν j a b p) (s, x)|
      ≤ 16 * (∑ i ∈ Finset.range 5, |sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s|) *
        ∑ w' ∈ budgetWords, |wordW w' (psiSummandGauss ν j a b) (s, x)| :=
    t6_scalar_leibniz (fun t => Ay ν χf A t (mi a) (mi b)) (psiSummandGauss ν j a b)
      (ayEntrySmooth as χf hχ ν hν A hA (mi a) (mi b)) (t6_psiGaussSmooth ν hν j a b) w hw (s, x) hq
  have hE : 0 ≤ envTerm mg ν j (s, x) := by unfold envTerm; positivity
  have hM : 0 ≤ affM ν χf A := t12_affM_nonneg ν χf A
  have hRHS : 0 ≤ 80 * (budgetWords.card : ℝ) * Cg * affM ν χf A * s ^ (5 / 2 : ℝ)
      * envTerm mg ν j (s, x) := by
    have h80 : (0 : ℝ) ≤ 80 * (budgetWords.card : ℝ) :=
      mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h80 hCg) hM)
      (Real.rpow_nonneg hs.le _)) hE
  have hent : ∀ i ∈ Finset.range 5, sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s
      = sDerivIter i (Ay ν χf A) s (mi a) (mi b) := by
    intro i hi
    have hi5 : i < 5 := Finset.mem_range.mp hi
    exact t12_entry_rel (Ay ν χf A) hAy6 (mi a) (mi b) i (by omega) (Set.mem_Ioi.mpr hs)
  by_cases h : (11 / 10 : ℝ) ≤ ν * s
  · have hz : ∀ i ∈ Finset.range 5,
        |sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s| = 0 := by
      intro i hi
      have hi5 : i < 5 := Finset.mem_range.mp hi
      rw [hent i hi, (ayEntryBound as χf hχ ν hν A hA s hs i (by omega) (mi a) (mi b)).2 h, abs_zero]
    have hsum0 : ∑ i ∈ Finset.range 5,
        |sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s| = 0 :=
      Finset.sum_eq_zero hz
    rw [hsum0, mul_zero, zero_mul] at hsm
    exact hsm.trans hRHS
  · have hle : ν * s ≤ 11 / 10 := le_of_lt (not_le.mp h)
    have hS : ∑ w' ∈ budgetWords, |wordW w' (psiSummandGauss ν j a b) (s, x)| ≤
        (budgetWords.card : ℝ) * (Cg * envTerm mg ν j (s, x)) := by
      calc ∑ w' ∈ budgetWords, |wordW w' (psiSummandGauss ν j a b) (s, x)|
          ≤ ∑ w' ∈ budgetWords, Cg * envTerm mg ν j (s, x) :=
            Finset.sum_le_sum (fun w' hw' => hG ν hν s hs hle w' hw' a b x j)
        _ = (budgetWords.card : ℝ) * (Cg * envTerm mg ν j (s, x)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hC1 : ∑ i ∈ Finset.range 5, |sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s|
        ≤ 5 * (affM ν χf A * s ^ (5 / 2 : ℝ)) := by
      calc ∑ i ∈ Finset.range 5, |sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s|
          ≤ ∑ i ∈ Finset.range 5, (affM ν χf A * s ^ (5 / 2 : ℝ)) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi5 : i < 5 := Finset.mem_range.mp hi
            rw [hent i hi]
            exact (ayEntryBound as χf hχ ν hν A hA s hs i (by omega) (mi a) (mi b)).1
        _ = 5 * (affM ν χf A * s ^ (5 / 2 : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
    have hSnn : 0 ≤ ∑ w' ∈ budgetWords, |wordW w' (psiSummandGauss ν j a b) (s, x)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hX : 0 ≤ affM ν χf A * s ^ (5 / 2 : ℝ) := mul_nonneg hM (Real.rpow_nonneg hs.le _)
    have h16 : (0 : ℝ) ≤ 16 * (5 * (affM ν χf A * s ^ (5 / 2 : ℝ))) :=
      mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hX)
    calc |wordW w (t6F ν χf A j a b) (s, x)|
        ≤ 16 * (∑ i ∈ Finset.range 5, |sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s|) *
          ∑ w' ∈ budgetWords, |wordW w' (psiSummandGauss ν j a b) (s, x)| := hsm
      _ ≤ 16 * (5 * (affM ν χf A * s ^ (5 / 2 : ℝ))) *
          ((budgetWords.card : ℝ) * (Cg * envTerm mg ν j (s, x))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hC1 (by norm_num)) hS hSnn h16
      _ = 80 * (budgetWords.card : ℝ) * Cg * affM ν χf A * s ^ (5 / 2 : ℝ)
          * envTerm mg ν j (s, x) := by ring

/-- Triangle inequality for four terms. -/
lemma t6_abs_four (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- **Summand bound** (source 5063-5071, 5076-5079): every word of length `≤ 4` on the lattice
summand `psiSummandM` is bounded by `C M(A) s^{5/2}` times the envelope, for all `s > 0`. -/
theorem psiSummandBound (as : ℝ) (χf : ℝ → ℝ) : PsiSummandBound as χf := by
  intro hχ
  obtain ⟨Cg, mg, hCg, hG⟩ := psiGaussWordBound
  refine ⟨320 * (budgetWords.card : ℝ) * Cg, mg, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hCg
  intro ν hν A hA s hs w hw x j
  have hq : (s, x) ∈ UChart := ⟨hs, Set.mem_univ _⟩
  have hlen : w.length ≤ 4 := wsb_mem_budget_iff.mp hw
  have hsmooth : ∀ a b : Fin 2, ContDiffOn ℝ 4 (t6F ν χf A j a b) UChart := by
    intro a b
    unfold t6F
    exact ((ayEntrySmooth as χf hχ ν hν A hA (mi a) (mi b)).comp contDiffOn_fst
      (fun p hp => hp.1)).mul (t6_psiGaussSmooth ν hν j a b)
  have hexp : ∀ p ∈ UChart, psiSummandM ν χf A j p
      = (t6F ν χf A j 0 0 + t6F ν χf A j 0 1 + t6F ν χf A j 1 0 + t6F ν χf A j 1 1) p := by
    intro p hp
    rw [psiSummandExpand ν hν χf A j p hp]
    simp only [Fin.sum_univ_two, Pi.add_apply, t6F]
    ring
  have hcong := wordW_congr w hexp (s, x) hq
  rw [hcong, t6_wordW_four w _ _ _ _ hlen (hsmooth 0 0) (hsmooth 0 1) (hsmooth 1 0)
    (hsmooth 1 1) (s, x) hq]
  refine (t6_abs_four _ _ _ _).trans ?_
  have b00 := t6_term_bound as χf Cg mg hCg hG hχ ν hν A hA s hs w hw x j 0 0
  have b01 := t6_term_bound as χf Cg mg hCg hG hχ ν hν A hA s hs w hw x j 0 1
  have b10 := t6_term_bound as χf Cg mg hCg hG hχ ν hν A hA s hs w hw x j 1 0
  have b11 := t6_term_bound as χf Cg mg hCg hG hχ ν hν A hA s hs w hw x j 1 1
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
