import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# `PartIII-b:C/asrc/ra/5/5` : a function of the time variable has polynomial growth (order 0)

Toolkit lemma for `PolyGrowth`: for `f : ℝ → E` of class `C^n` on `(0,∞)`, the map
`p ↦ f p.1` is `C^n` on `(0,∞) × ℝ²` and its derivatives of order `m ≤ n` are bounded
uniformly in `x` and in `s` on compact subsets of `(0,∞)` (the derivatives are the derivatives
of `f` composed with the projection, whose norm is at most `1`; continuity and compactness
give the bound).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem polyGrowth_of_s {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (f : ℝ → E) (hf : ContDiffOn ℝ (n : WithTop ℕ∞) f (Ioi (0 : ℝ))) :
    PolyGrowth n (fun p : ℝ × (ℝ × ℝ) => f p.1) := by
  have hfst : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => f p.1)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hf.comp contDiffOn_fst (fun p hp => hp.1)
  refine ⟨hfst, fun s0 s1 hs0 hs01 => ?_⟩
  have hall : ∀ m : ℕ, ∃ C : ℝ, m ≤ n → ∀ s ∈ Icc s0 s1,
      ‖iteratedFDerivWithin ℝ m f (Ioi (0 : ℝ)) s‖ ≤ C := by
    intro m
    by_cases hm : m ≤ n
    · have hc : ContinuousOn (iteratedFDerivWithin ℝ m f (Ioi (0 : ℝ))) (Icc s0 s1) :=
        (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hm)
          isOpen_Ioi.uniqueDiffOn).mono (fun s hs => lt_of_lt_of_le hs0 hs.1)
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := s0) (b := s1)).exists_bound_of_continuousOn hc.norm
      exact ⟨C, fun _ s hs => by simpa using hC s hs⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose Cm hCm using hall
  refine ⟨∑ m ∈ Finset.range (n + 1), |Cm m|, 0,
    Finset.sum_nonneg (fun i _ => abs_nonneg _), fun m hm s hs x => ?_⟩
  rw [pow_zero, mul_one]
  have hT : IsOpen ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ)) :=
    isOpen_Ioi.preimage (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).continuous
  have hTmem : (s, x) ∈ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ) :=
    lt_of_lt_of_le hs0 hs.1
  have hconv : iteratedFDeriv ℝ m (f ∘ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) (s, x) =
      iteratedFDerivWithin ℝ m (f ∘ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)))
        ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ)) (s, x) :=
    ((iteratedFDerivWithin_of_isOpen (f := f ∘ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) m hT)
      hTmem).symm
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) hf isOpen_Ioi.uniqueDiffOn hT.uniqueDiffOn
    (x := (s, x)) (lt_of_lt_of_le hs0 hs.1) (i := m) (hi := by exact_mod_cast hm)
  have hbd : ‖iteratedFDeriv ℝ m (fun p : ℝ × (ℝ × ℝ) => f p.1) (s, x)‖ ≤ Cm m := by
    show ‖iteratedFDeriv ℝ m (f ∘ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) (s, x)‖ ≤ Cm m
    rw [hconv, hcomp]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hprod : ∏ _i : Fin m, ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ))
    refine (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans ?_
    rw [mul_one]
    exact hCm m hm _ hs
  have hle : Cm m ≤ ∑ i ∈ Finset.range (n + 1), |Cm i| :=
    (le_abs_self (Cm m)).trans
      (Finset.single_le_sum (f := fun i => |Cm i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega)))
  exact hbd.trans hle

end UnforcedLeray.Short.PartIIIb.Concrete
