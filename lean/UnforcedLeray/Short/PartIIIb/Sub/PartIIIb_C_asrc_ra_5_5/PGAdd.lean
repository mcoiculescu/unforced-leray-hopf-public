import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# `PartIII-b:C/asrc/ra/5/5` : polynomial growth is stable under sums, differences and negation

Toolkit lemma for `PolyGrowth`: the sum, difference and negation of two functions of polynomial
growth again have polynomial growth (`iteratedFDeriv` is additive, the constants add, and the
exponents are absorbed by `1 ≤ 1 + |x|²`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem pgAdd_one_le (x : ℝ × ℝ) : 1 ≤ 1 + sq2 x := by
  unfold sq2
  nlinarith [sq_nonneg x.1, sq_nonneg x.2]

theorem pgAdd_gen {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (P Q : ℝ × (ℝ × ℝ) → E) (hP : PolyGrowth n P) (hQ : PolyGrowth n Q) :
    PolyGrowth n (fun p => P p + Q p) := by
  obtain ⟨hPc, hPb⟩ := hP
  obtain ⟨hQc, hQb⟩ := hQ
  refine ⟨hPc.add hQc, fun s0 s1 hs0 hs01 => ?_⟩
  obtain ⟨C1, N1, hC1, hP1⟩ := hPb s0 s1 hs0 hs01
  obtain ⟨C2, N2, hC2, hQ1⟩ := hQb s0 s1 hs0 hs01
  refine ⟨C1 + C2, max N1 N2, add_nonneg hC1 hC2, fun m hm s hs x => ?_⟩
  have hS : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hsS : (s, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    ⟨lt_of_lt_of_le hs0 hs.1, mem_univ _⟩
  have hmn : (m : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hm
  have hPd : ContDiffAt ℝ (n : WithTop ℕ∞) P (s, x) := hPc.contDiffAt (hS.mem_nhds hsS)
  have hQd : ContDiffAt ℝ (n : WithTop ℕ∞) Q (s, x) := hQc.contDiffAt (hS.mem_nhds hsS)
  rw [fun_iteratedFDeriv_add_apply (hPd.of_le hmn) (hQd.of_le hmn)]
  have hp1 : (1 + sq2 x) ^ N1 ≤ (1 + sq2 x) ^ (max N1 N2) :=
    pow_le_pow_right₀ (pgAdd_one_le x) (le_max_left _ _)
  have hp2 : (1 + sq2 x) ^ N2 ≤ (1 + sq2 x) ^ (max N1 N2) :=
    pow_le_pow_right₀ (pgAdd_one_le x) (le_max_right _ _)
  refine (norm_add_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ m P (s, x)‖ + ‖iteratedFDeriv ℝ m Q (s, x)‖
      ≤ C1 * (1 + sq2 x) ^ N1 + C2 * (1 + sq2 x) ^ N2 :=
        add_le_add (hP1 m hm s hs x) (hQ1 m hm s hs x)
    _ ≤ C1 * (1 + sq2 x) ^ (max N1 N2) + C2 * (1 + sq2 x) ^ (max N1 N2) :=
        add_le_add (mul_le_mul_of_nonneg_left hp1 hC1) (mul_le_mul_of_nonneg_left hp2 hC2)
    _ = (C1 + C2) * (1 + sq2 x) ^ (max N1 N2) := by ring

theorem pgAdd_neg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (P : ℝ × (ℝ × ℝ) → E) (hP : PolyGrowth n P) : PolyGrowth n (fun p => -P p) := by
  obtain ⟨hPc, hPb⟩ := hP
  refine ⟨hPc.neg, fun s0 s1 hs0 hs01 => ?_⟩
  obtain ⟨C, N, hC, hP1⟩ := hPb s0 s1 hs0 hs01
  refine ⟨C, N, hC, fun m hm s hs x => ?_⟩
  show ‖iteratedFDeriv ℝ m (-P) (s, x)‖ ≤ C * (1 + sq2 x) ^ N
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact hP1 m hm s hs x

theorem polyGrowth_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (P Q : ℝ × (ℝ × ℝ) → E) (hP : PolyGrowth n P) (hQ : PolyGrowth n Q) :
    PolyGrowth n (fun p => P p + Q p) ∧ PolyGrowth n (fun p => P p - Q p) ∧
      PolyGrowth n (fun p => -P p) := by
  have hsub : (fun p => P p - Q p) = fun p => P p + (fun q => -Q q) p := by
    funext p
    exact sub_eq_add_neg _ _
  refine ⟨pgAdd_gen n P Q hP hQ, ?_, pgAdd_neg n P hP⟩
  rw [hsub]
  exact pgAdd_gen n P (fun q => -Q q) hP (pgAdd_neg n Q hQ)

end UnforcedLeray.Short.PartIIIb.Concrete
