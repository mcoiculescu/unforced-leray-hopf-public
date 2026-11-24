import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.Defs
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T9.Final

/-!
# `psiGaussWordBound` (task `PartIII-b:C/asrc/ra/9/1/2/9/2/1/4`)
Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079, 4979.
Scalar copy of `gaussWordBound` (`ra_9_1_2_9_1_1/T9/Final.lean`). The Gaussian part `psiGauss`
is a scalar function, so every conormal word of length `≤ 4` on it is a finite sum of Gaussian
monomials `gbG` (in `(a,u,v)`, `a = 1+νs`, `u = x₁ - jc`, `v = x₂`) with `α+β ≤ 11`, bounded by the
envelope `envTerm 11`. Reuses the monomial calculus `gbG`/`gbL`/`gbC`, the derivative lemmas
`gbC_opW_dir`, `gb_opW_congr` and the bound `gb_chart_bound` from the Hp chain.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Base monomials of `psiGauss` for `(a,b) = (0,0)`: `-2a⁻¹E - a⁻²u²E`. -/
def pgL00 : List GbMon := [⟨-2, 1, 0, 0⟩, ⟨-1, 2, 2, 0⟩]
/-- Base monomials of `psiGauss` for `(a,b) = (1,1)`: `-2a⁻¹E - a⁻²v²E`. -/
def pgL11 : List GbMon := [⟨-2, 1, 0, 0⟩, ⟨-1, 2, 0, 2⟩]
/-- Base monomials of `psiGauss` for `(a,b) = (0,1)` and `(1,0)`: `-a⁻²uvE`. -/
def pgL01 : List GbMon := [⟨-1, 2, 1, 1⟩]

lemma pg_base (a b : Fin 2) : ∃ L : List GbMon, (∀ mo ∈ L, mo.α + mo.β ≤ 2) ∧
    ∀ (ν : ℝ) (j : ℤ) (q : Chart), psiSummandGauss ν j a b q = gbC ν j L q := by
  fin_cases a <;> fin_cases b
  · refine ⟨pgL00, ?_, fun ν j q => ?_⟩
    · intro mo hmo
      simp only [pgL00, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmo
      rcases hmo with rfl | rfl <;> norm_num
    · simp [psiSummandGauss, gbC, gbL, gbG, pgL00, comp2, xj, sq2] <;> ring
  · refine ⟨pgL01, ?_, fun ν j q => ?_⟩
    · intro mo hmo
      simp only [pgL01, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmo
      rcases hmo with rfl <;> norm_num
    · simp [psiSummandGauss, gbC, gbL, gbG, pgL01, comp2, xj, sq2] <;> ring
  · refine ⟨pgL01, ?_, fun ν j q => ?_⟩
    · intro mo hmo
      simp only [pgL01, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmo
      rcases hmo with rfl <;> norm_num
    · simp [psiSummandGauss, gbC, gbL, gbG, pgL01, comp2, xj, sq2] <;> ring
  · refine ⟨pgL11, ?_, fun ν j q => ?_⟩
    · intro mo hmo
      simp only [pgL11, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmo
      rcases hmo with rfl | rfl <;> norm_num
    · simp [psiSummandGauss, gbC, gbL, gbG, pgL11, comp2, xj, sq2] <;> ring

/-- Monomial representation of `wordW w (psiSummandGauss ν j a b)` on `UChart`. -/
def PsiGbRep (a b : Fin 2) (w : List (Fin 3)) : Prop :=
  ∃ L : List GbMon, (∀ mo ∈ L, mo.α + mo.β ≤ 2 + 2 * w.length) ∧
    ∀ (ν : ℝ), 0 < ν → ∀ (j : ℤ), ∀ q ∈ UChart,
      wordW w (psiSummandGauss ν j a b) q = gbC ν j L q

lemma pg_rep_all (a b : Fin 2) : ∀ w : List (Fin 3), w.length ≤ 4 → PsiGbRep a b w := by
  intro w
  induction w with
  | nil =>
    intro _
    obtain ⟨L, hd, hrep⟩ := pg_base a b
    refine ⟨L, fun mo hmo => ?_, fun ν _ j q _ => ?_⟩
    · have := hd mo hmo
      simp only [List.length_nil]
      omega
    · exact hrep ν j q
  | cons x w ih =>
    intro hlen
    simp only [List.length_cons] at hlen
    obtain ⟨L, hd, hrep⟩ := ih (by omega)
    refine ⟨gbOpL (gbDir x) L, ?_, ?_⟩
    · intro mo hmo
      have := gbOpL_deg x L (2 + 2 * w.length) hd mo hmo
      simp only [List.length_cons]
      omega
    · intro ν hν j q hq
      show opW x (wordW w (psiSummandGauss ν j a b)) q = _
      have hc : opW x (wordW w (psiSummandGauss ν j a b)) q
          = opW x (gbC ν j L) q :=
        gb_opW_congr x (Filter.eventually_of_mem (gb_open.mem_nhds hq)
          (fun p hp => hrep ν hν j p hp))
      rw [hc, gbC_opW_dir x ν j L q hν hq.1]

theorem psiGaussWordBound : PsiGaussWordBound := by
  have hex : ∀ w ∈ budgetWords, ∀ a b : Fin 2, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ν : ℝ), 0 < ν → ∀ (j : ℤ), ∀ q : Chart, 0 < q.1 →
        |wordW w (psiSummandGauss ν j a b) q| ≤ K * envTerm 11 ν j q := by
    intro w hw a b
    have hlen : w.length ≤ 4 := gb_len_of_budget hw
    obtain ⟨L, hdeg, hrep⟩ := pg_rep_all a b w hlen
    refine ⟨gbK L, gbK_nonneg _, fun ν hν j q hq => ?_⟩
    have hqU : q ∈ UChart := ⟨hq, Set.mem_univ _⟩
    rw [hrep ν hν j q hqU]
    have hd : ∀ mo ∈ L, mo.α + mo.β ≤ 11 := fun mo h => by
      have := hdeg mo h
      omega
    exact gb_chart_bound L ν j hν q hq hd
  choose! K hK0 hK using hex
  refine ⟨∑ w ∈ budgetWords, ∑ a : Fin 2, ∑ b : Fin 2, K w a b, 11,
    Finset.sum_nonneg fun w hw => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      hK0 w hw a b, fun ν hν s hs _ w hw a b x j => ?_⟩
  have hKC : K w a b ≤ ∑ w ∈ budgetWords, ∑ a : Fin 2, ∑ b : Fin 2, K w a b := by
    have h1 : K w a b ≤ ∑ b : Fin 2, K w a b :=
      Finset.single_le_sum (f := fun b => K w a b) (fun b _ => hK0 w hw a b) (Finset.mem_univ b)
    have h2 : ∑ b : Fin 2, K w a b ≤ ∑ a : Fin 2, ∑ b : Fin 2, K w a b :=
      Finset.single_le_sum (f := fun a => ∑ b : Fin 2, K w a b)
        (fun a _ => Finset.sum_nonneg fun b _ => hK0 w hw a b) (Finset.mem_univ a)
    have h3 : ∑ a : Fin 2, ∑ b : Fin 2, K w a b
        ≤ ∑ w ∈ budgetWords, ∑ a : Fin 2, ∑ b : Fin 2, K w a b :=
      Finset.single_le_sum (f := fun w => ∑ a : Fin 2, ∑ b : Fin 2, K w a b)
        (fun w hw' => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hK0 w hw' a b) hw
    linarith
  have hq : (0 : ℝ) < (s, x).1 := hs
  have henv : 0 ≤ envTerm 11 ν j (s, x) :=
    mul_nonneg (pow_nonneg (add_nonneg zero_le_one (norm_nonneg _)) _) (Real.exp_pos _).le
  calc |wordW w (psiSummandGauss ν j a b) (s, x)| ≤ K w a b * envTerm 11 ν j (s, x) :=
        hK w hw a b ν hν j (s, x) hq
    _ ≤ (∑ w ∈ budgetWords, ∑ a : Fin 2, ∑ b : Fin 2, K w a b) * envTerm 11 ν j (s, x) :=
        mul_le_mul_of_nonneg_right hKC henv

end UnforcedLeray.Short.PartIIIb.Concrete
