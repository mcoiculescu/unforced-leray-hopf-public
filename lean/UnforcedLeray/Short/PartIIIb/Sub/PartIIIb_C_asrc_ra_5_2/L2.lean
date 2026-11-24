import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# `PartIII-b:C/asrc/ra/5/2/2` : iterated derivatives of the age factor `(κ a(s))⁻¹`

Source 4963-4968.  The function `s ↦ (κ (1 + ν s))⁻¹` is smooth on `(0, ∞)`.  Its iterated
derivatives are continuous there, hence bounded on the compact interval `[s0, s1] ⊆ (0, ∞)`.
The function `p ↦ (κ a(p.1))⁻¹` is this one-variable function composed with the first
projection, a continuous linear map of norm at most one, so the iterated derivatives are
bounded by the same constant.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set

theorem gauss_age_iterated_bound (κ ν s0 s1 : ℝ) (hκ : 0 < κ) (hν : 0 < ν) (hs0 : 0 < s0) (hs01 : s0 ≤ s1) (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc s0 s1, ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ j (fun p : ℝ × (ℝ × ℝ) => (κ * ageA ν p.1)⁻¹) (s, x)‖ ≤ C := by
  -- smoothness of the one-variable factor on `(0, ∞)`
  have hpos : ∀ t ∈ Ioi (0 : ℝ), κ * ageA ν t ≠ 0 := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have : 0 < ageA ν t := by unfold ageA; nlinarith [mul_pos hν ht']
    exact (mul_pos hκ this).ne'
  have hsmooth : ∀ n : WithTop ℕ∞,
      ContDiffOn ℝ n (fun t : ℝ => (κ * ageA ν t)⁻¹) (Ioi 0) := by
    intro n
    have hc : ContDiff ℝ n (fun t : ℝ => κ * ageA ν t) := by
      unfold ageA
      fun_prop
    exact (hc.contDiffOn).inv hpos
  -- continuity of the derivatives on `(0, ∞)`
  have hcont : ContinuousOn (iteratedFDeriv ℝ j (fun t : ℝ => (κ * ageA ν t)⁻¹)) (Ioi 0) :=
    ContinuousOn.continuousOn_iteratedFDeriv (hsmooth (j : WithTop ℕ∞)) isOpen_Ioi (le_refl _)
  have hK : ContinuousOn (iteratedFDeriv ℝ j (fun t : ℝ => (κ * ageA ν t)⁻¹)) (Icc s0 s1) :=
    hcont.mono (fun t ht => lt_of_lt_of_le hs0 ht.1)
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := s0) (b := s1)).exists_bound_of_continuousOn hK
  refine ⟨max C0 0, le_max_right _ _, ?_⟩
  intro s hs x
  -- the composition with the first projection
  have hfst : ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ)
  have hopenG : IsOpen ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ)) :=
    isOpen_Ioi.preimage (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).continuous
  have hUDO : UniqueDiffOn ℝ ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ)) :=
    hopenG.uniqueDiffOn
  have hUDO' : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hsmem : (s, x) ∈ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ) := by
    show (0 : ℝ) < s
    exact lt_of_lt_of_le hs0 hs.1
  have hxfst : (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (s, x) ∈ Ioi (0 : ℝ) := hsmem
  have hcomp := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).iteratedFDerivWithin_comp_right
    (f := fun t : ℝ => (κ * ageA ν t)⁻¹) (hsmooth (j : WithTop ℕ∞)) hUDO' hUDO hxfst
    (i := j) (le_refl _)
  have hfun : (fun p : ℝ × (ℝ × ℝ) => (κ * ageA ν p.1)⁻¹) =
      (fun t : ℝ => (κ * ageA ν t)⁻¹) ∘ (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) := rfl
  have e1 : iteratedFDeriv ℝ j ((fun t : ℝ => (κ * ageA ν t)⁻¹) ∘
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) (s, x) =
      iteratedFDerivWithin ℝ j ((fun t : ℝ => (κ * ageA ν t)⁻¹) ∘
        (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)))
        ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ⁻¹' Ioi (0 : ℝ)) (s, x) :=
    (iteratedFDerivWithin_of_isOpen j hopenG hsmem).symm
  have e2 : iteratedFDerivWithin ℝ j (fun t : ℝ => (κ * ageA ν t)⁻¹) (Ioi (0 : ℝ))
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (s, x)) =
      iteratedFDeriv ℝ j (fun t : ℝ => (κ * ageA ν t)⁻¹)
        ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (s, x)) :=
    iteratedFDerivWithin_of_isOpen j isOpen_Ioi hxfst
  rw [hfun, e1, hcomp, e2]
  have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j (fun t : ℝ => (κ * ageA ν t)⁻¹) ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (s, x)))
    (fun _ : Fin j => ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
  have hprod : ∏ _i : Fin j, ‖ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hfst)
  have hA : ‖iteratedFDeriv ℝ j (fun t : ℝ => (κ * ageA ν t)⁻¹)
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (s, x))‖ ≤ C0 :=
    hC0 _ hs
  have hA0 : 0 ≤ ‖iteratedFDeriv ℝ j (fun t : ℝ => (κ * ageA ν t)⁻¹)
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (s, x))‖ := norm_nonneg _
  calc _ ≤ _ := hb
    _ ≤ ‖iteratedFDeriv ℝ j (fun t : ℝ => (κ * ageA ν t)⁻¹)
        ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (s, x))‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod hA0
    _ = _ := mul_one _
    _ ≤ C0 := hA
    _ ≤ max C0 0 := le_max_left _ _

end UnforcedLeray.Short.PartIIIb.Concrete
