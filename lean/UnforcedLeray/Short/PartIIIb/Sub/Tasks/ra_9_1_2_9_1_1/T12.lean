import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T6
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T7
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T8
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T9.Final
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T10
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T11

/-!
# `hpSummandBound` (task `PartIII-b:C/asrc/ra/9/1/2/9/1/1/12`)

Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079, 4963-4985.

Combination of the dependencies: the summand is the finite sum over `(a,b) ∈ {0,1}²` of
`A^y_{mi a, mi b}(s) · hpGaussM a b` (`hpSummandExpand`); each word is linear over this finite sum
on `UChart` (`t12_wordW_list`, via `wsb_opW_list`); each term obeys the Leibniz bound
`wordW_smul_bound` with the entry derivatives bounded by `ayEntryBound` (for `νs ≥ 11/10` they all
vanish, so the term is zero) and the Gaussian words bounded by `gaussWordBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The four index pairs `(a,b) ∈ {0,1}²`. -/
def t12L : List (Fin 2 × Fin 2) := [(0, 0), (0, 1), (1, 0), (1, 1)]

lemma t12_affM_nonneg (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) : 0 ≤ affM ν χ A := by
  unfold affM
  apply Real.sSup_nonneg
  rintro _ ⟨t, ht, rfl⟩
  show 0 ≤ t ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χ A) t
  refine mul_nonneg (Real.rpow_nonneg (le_of_lt ht.1) _) ?_
  unfold affSum
  exact Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _

lemma t12_Ay6 (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν : ℝ) (A : ℝ → Mat3)
    (hA : IsAffElem as A) : ContDiffOn ℝ 6 (Ay ν χf A) (Ioi 0) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => χf (ν * t)) :=
    hχ.smooth.comp (contDiff_const.mul contDiff_id)
  have hcut : ContDiffOn ℝ 6 (fun t : ℝ => χf (ν * t)) (Ioi 0) :=
    hc.contDiffOn.of_le (by norm_num)
  unfold Ay
  exact hcut.smul hA.smooth

/-- Entries of the `k`-th `s∂_s` iterate of a matrix function are the `k`-th iterates of the entry
(`f` is `C^6` on `(0,∞)`, `k ≤ 5`). -/
lemma t12_entry_rel (f : ℝ → Mat3) (hf : ContDiffOn ℝ 6 f (Ioi 0)) (i j : Fin 3) :
    ∀ k : ℕ, k ≤ 5 → EqOn (sDerivIterR k (fun t => f t i j)) (fun t => sDerivIter k f t i j)
      (Ioi 0) := by
  intro k
  induction k with
  | zero => intro _ t _; rfl
  | succ k ih =>
    intro hk t ht
    have ht' : 0 < t := Set.mem_Ioi.mp ht
    have hf' : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f (Ioi 0) :=
      hf.of_le (by exact_mod_cast (show k + 1 ≤ 6 by omega))
    have hc := sDerivIter_contDiffOn_aux f k 1 hf'
    have hdiff : DifferentiableAt ℝ (sDerivIter k f) t :=
      (hc.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds ht')
    have hEv : sDerivIterR k (fun t => f t i j) =ᶠ[𝓝 t] (fun u => sDerivIter k f u i j) :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht') (fun u hu => ih (by omega) hu)
    have hd1 : deriv (sDerivIterR k (fun t => f t i j)) t
        = deriv (fun u => sDerivIter k f u i j) t :=
      hEv.deriv_eq
    have hd2 : deriv (fun u => sDerivIter k f u i j) t = deriv (sDerivIter k f) t i j :=
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 hdiff.hasDerivAt i) j).deriv
    show t * deriv (sDerivIterR k (fun t => f t i j)) t = (t • deriv (sDerivIter k f) t) i j
    rw [hd1, hd2]
    rfl

/-- Conormal words are linear over a finite list sum of `C^4` functions on `UChart`. -/
lemma t12_wordW_list {ι : Type} (L : List ι) (F : ι → Chart → Merid)
    (hF : ∀ i ∈ L, ContDiffOn ℝ 4 (F i) UChart) :
    ∀ w : List (Fin 3), w.length ≤ 4 → ∀ q ∈ UChart,
      wordW w (fun p => (L.map fun i => F i p).sum) q = (L.map fun i => wordW w (F i) q).sum := by
  intro w
  induction w with
  | nil => intro _ q _; simp [wordW]
  | cons a w ih =>
    intro hlen q hq
    have hlen' : w.length ≤ 4 := by simp only [List.length_cons] at hlen; omega
    have hw3 : w.length ≤ 3 := by simp only [List.length_cons] at hlen; omega
    have hev : (fun p => wordW w (fun p => (L.map fun i => F i p).sum) p) =ᶠ[𝓝 q]
        (fun p => (L.map fun i => wordW w (F i) p).sum) := by
      filter_upwards [wsb_open.mem_nhds hq] with p hp
      exact ih hlen' p hp
    have hd : ∀ i ∈ L, DifferentiableAt ℝ (wordW w (F i)) q := by
      intro i hi
      have hc := wsb_wordW_cdo (F i) (hF i hi) w 1 (by omega)
      exact (hc.differentiableOn (by norm_num)).differentiableAt (wsb_open.mem_nhds hq)
    show opW a (fun p => wordW w (fun p => (L.map fun i => F i p).sum) p) q
      = (L.map fun i => opW a (wordW w (F i)) q).sum
    rw [wsb_opW_congr a hev]
    exact wsb_opW_list a (fun i => wordW w (F i)) q L hd

lemma t12_summand_smooth (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) (j : ℤ) (ab : Fin 2 × Fin 2) :
    ContDiffOn ℝ 4 (fun p : Chart => (Ay ν χf A p.1 (mi ab.1) (mi ab.2)) • hpGaussM ν j ab.1 ab.2 p)
      UChart := by
  have h1 : ContDiffOn ℝ 4 (fun p : Chart => Ay ν χf A p.1 (mi ab.1) (mi ab.2)) UChart :=
    (ayEntrySmooth as χf hχ ν hν A hA (mi ab.1) (mi ab.2)).comp contDiffOn_fst
      (fun p hp => hp.1)
  exact h1.smul (hpGaussSmooth_pos ν hν j ab.1 ab.2)

lemma t12_term_bound (as : ℝ) (χf : ℝ → ℝ) (Cg : ℝ) (mg : ℕ) (hCg : 0 ≤ Cg)
    (hG : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 0 < s → ν * s ≤ 11 / 10 → ∀ w ∈ budgetWords,
      ∀ (a b : Fin 2) (x : ℝ × ℝ) (j : ℤ),
        ‖wordW w (hpGaussM ν j a b) (s, x)‖ ≤ Cg * envTerm mg ν j (s, x))
    (hχ : IsSourceCutoffC χf) (ν : ℝ) (hν : 0 < ν) (A : ℝ → Mat3) (hA : IsAffElem as A)
    (s : ℝ) (hs : 0 < s) (w : List (Fin 3)) (hw : w ∈ budgetWords) (x : ℝ × ℝ) (j : ℤ)
    (a b : Fin 2) :
    ‖wordW w (fun p : Chart => (Ay ν χf A p.1 (mi a) (mi b)) • hpGaussM ν j a b p) (s, x)‖
      ≤ 80 * (budgetWords.card : ℝ) * Cg * affM ν χf A * s ^ (5 / 2 : ℝ) * envTerm mg ν j (s, x) := by
  have hq : (s, x) ∈ UChart := ⟨hs, Set.mem_univ _⟩
  have hsm : ‖wordW w (fun p : Chart => (Ay ν χf A p.1 (mi a) (mi b)) • hpGaussM ν j a b p) (s, x)‖
      ≤ 16 * (∑ i ∈ Finset.range 5, |sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s|) *
        ∑ w' ∈ budgetWords, ‖wordW w' (hpGaussM ν j a b) (s, x)‖ :=
    wordW_smul_bound (fun t => Ay ν χf A t (mi a) (mi b)) (hpGaussM ν j a b)
      (ayEntrySmooth as χf hχ ν hν A hA (mi a) (mi b)) (hpGaussSmooth_pos ν hν j a b) w hw
      (s, x) hq
  have hAy6 : ContDiffOn ℝ 6 (Ay ν χf A) (Ioi 0) := t12_Ay6 as χf hχ ν A hA
  have hE : 0 ≤ envTerm mg ν j (s, x) := by unfold envTerm; positivity
  have hM : 0 ≤ affM ν χf A := t12_affM_nonneg ν χf A
  have hX : 0 ≤ affM ν χf A * s ^ (5 / 2 : ℝ) := mul_nonneg hM (Real.rpow_nonneg hs.le _)
  have hRHS : 0 ≤ 80 * (budgetWords.card : ℝ) * Cg * affM ν χf A * s ^ (5 / 2 : ℝ)
      * envTerm mg ν j (s, x) := by
    have h80 : (0 : ℝ) ≤ 80 * (budgetWords.card : ℝ) :=
      mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h80 hCg) hM)
      (Real.rpow_nonneg hs.le _)) hE
  by_cases h : (11 / 10 : ℝ) ≤ ν * s
  · have hz : ∀ i ∈ Finset.range 5,
        sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s = 0 := by
      intro i hi
      have hi5 : i < 5 := Finset.mem_range.mp hi
      have key : sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s
          = sDerivIter i (Ay ν χf A) s (mi a) (mi b) :=
        t12_entry_rel (Ay ν χf A) hAy6 (mi a) (mi b) i (by omega) (Set.mem_Ioi.mpr hs)
      rw [key]
      exact (ayEntryBound as χf hχ ν hν A hA s hs i (by omega) (mi a) (mi b)).2 h
    have hsum0 : ∑ i ∈ Finset.range 5,
        |sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s| = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hz i hi, abs_zero])
    simp only [hsum0, mul_zero, zero_mul] at hsm
    exact hsm.trans hRHS
  · have hle : ν * s ≤ 11 / 10 := le_of_lt (not_le.mp h)
    have hS : ∑ w' ∈ budgetWords, ‖wordW w' (hpGaussM ν j a b) (s, x)‖ ≤
        (budgetWords.card : ℝ) * (Cg * envTerm mg ν j (s, x)) := by
      calc ∑ w' ∈ budgetWords, ‖wordW w' (hpGaussM ν j a b) (s, x)‖
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
            have key : sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s
                = sDerivIter i (Ay ν χf A) s (mi a) (mi b) :=
              t12_entry_rel (Ay ν χf A) hAy6 (mi a) (mi b) i (by omega) (Set.mem_Ioi.mpr hs)
            rw [key]
            exact (ayEntryBound as χf hχ ν hν A hA s hs i (by omega) (mi a) (mi b)).1
        _ = 5 * (affM ν χf A * s ^ (5 / 2 : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
    have hSnn : 0 ≤ ∑ w' ∈ budgetWords, ‖wordW w' (hpGaussM ν j a b) (s, x)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h16 : (0 : ℝ) ≤ 16 * (5 * (affM ν χf A * s ^ (5 / 2 : ℝ))) :=
      mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hX)
    calc ‖wordW w (fun p : Chart => (Ay ν χf A p.1 (mi a) (mi b)) • hpGaussM ν j a b p) (s, x)‖
        ≤ 16 * (∑ i ∈ Finset.range 5, |sDerivIterR i (fun t => Ay ν χf A t (mi a) (mi b)) s|) *
          ∑ w' ∈ budgetWords, ‖wordW w' (hpGaussM ν j a b) (s, x)‖ := hsm
      _ ≤ 16 * (5 * (affM ν χf A * s ^ (5 / 2 : ℝ))) *
          ((budgetWords.card : ℝ) * (Cg * envTerm mg ν j (s, x))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hC1 (by norm_num)) hS hSnn h16
      _ = 80 * (budgetWords.card : ℝ) * Cg * affM ν χf A * s ^ (5 / 2 : ℝ)
          * envTerm mg ν j (s, x) := by ring

/-- **Summand bound** (source 5063-5071, 5076-5079): every word of length `≤ 4` on the lattice
summand `hpSummandM` is bounded by `C M(A) s^{5/2}` times the envelope, for all `s > 0`. -/
theorem hpSummandBound (as : ℝ) (χf : ℝ → ℝ) : HpSummandBound as χf := by
  intro hχ
  obtain ⟨Cg, mg, hCg, hG⟩ := gaussWordBound
  refine ⟨320 * (budgetWords.card : ℝ) * Cg, mg, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hCg
  intro ν hν A hA s hs w hw x j
  have hq : (s, x) ∈ UChart := ⟨hs, Set.mem_univ _⟩
  have hlen : w.length ≤ 4 := wsb_mem_budget_iff.mp hw
  have hfun : hpSummandM ν χf A j = fun p : Chart =>
      (t12L.map fun ab : Fin 2 × Fin 2 =>
        (Ay ν χf A p.1 (mi ab.1) (mi ab.2)) • hpGaussM ν j ab.1 ab.2 p).sum := by
    rw [hpSummandExpand ν χf A j]
    funext p
    simp only [t12L, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Fin.sum_univ_two, add_zero]
    abel
  rw [hfun]
  rw [t12_wordW_list t12L
    (fun ab : Fin 2 × Fin 2 => fun p : Chart =>
      (Ay ν χf A p.1 (mi ab.1) (mi ab.2)) • hpGaussM ν j ab.1 ab.2 p)
    (fun ab _ => t12_summand_smooth as χf hχ ν hν A hA j ab) w hlen (s, x) hq]
  refine (wsb_norm_list_sum_le _ _
    (80 * (budgetWords.card : ℝ) * Cg * affM ν χf A * s ^ (5 / 2 : ℝ) * envTerm mg ν j (s, x))
    ?_).trans ?_
  · intro ab _
    exact t12_term_bound as χf Cg mg hCg hG hχ ν hν A hA s hs w hw x j ab.1 ab.2
  · have hl : ((t12L.length : ℕ) : ℝ) = 4 := by simp [t12L]
    rw [hl]
    apply le_of_eq
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
