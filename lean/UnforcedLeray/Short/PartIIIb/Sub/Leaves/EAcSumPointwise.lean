import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10_3
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.EAcTermPointwise
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellSumPointwise

/-!
# `PartIII-b:C/inst/10/3/4` leaf E2: pointwise square bound of `e_AB` (source 5063-5079)

Proves `EAcSumPointwise`: `‖merOf (eAB ν s B C x)‖² ≤ K1 (|B|+|C|)² Σ_j G_a(x_j)`.

Same plan as `fAcSumPointwise` (`Sub/Leaves/CellSumPointwise.lean`), with the term bound
`EAcTermPointwise` in place of `FAcTermPointwise`. The Vec3-valued family `eAcTerm` need not be
known summable: if it is not, `eAB` is `0` and the bound is trivial; if it is, `merOf` commutes
with the tsum.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem eAcSumPointwise : EAcSumPointwise := by
  obtain ⟨C0, hC0, hT⟩ := eAcTermPointwise
  obtain ⟨C1, hC1⟩ := fAcLatticeWeight
  refine ⟨max C1 0 * C0 ^ 2, mul_nonneg (le_max_right _ _) (sq_nonneg _), ?_⟩
  intro ν s B C x hν hν1 hs hsT
  have hνs : ν * s ≤ 11 / 10 := by
    rw [le_div_iff₀ hν] at hsT
    linarith [mul_comm ν s]
  have ha0 : 0 < ageA ν s := by unfold ageA; linarith [mul_pos hν hs]
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; linarith [mul_pos hν hs]
  have ha2 : ageA ν s ≤ 21 / 10 := by unfold ageA; linarith
  have hc0 : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hc1 : 1 ≤ cOf ν := by
    unfold cOf
    rw [one_le_inv₀ (pow_pos hν 2)]
    nlinarith
  -- the squared-distance bound `(x₁ - jc)² ≤ |x_j|²`
  have hq : ∀ j : ℤ, (x.1 - (j : ℝ) * cOf ν) ^ 2 ≤ sq2 (xj ν j x) := fun j => by
    show (x.1 - (j : ℝ) * cOf ν) ^ 2 ≤ (x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hq0 : ∀ j : ℤ, 0 ≤ sq2 (xj ν j x) := fun j => by unfold sq2; positivity
  have hGnn : ∀ j : ℤ, 0 ≤ fAcG (ageA ν s) (xj ν j x) := fun j => by
    unfold fAcG; have := hq0 j; positivity
  -- summability of the lattice weights
  have hwS : Summable (fun j : ℤ => fAcWt ν s x j) := by
    have hα : 0 < 1 / (8 * ageA ν s) := div_pos one_pos (by linarith)
    refine (gp_gauss_summable x.1 (1 / (8 * ageA ν s)) (cOf ν) hα hc0).congr (fun j => ?_)
    unfold fAcWt
    congr 1
    ring
  -- summability of the majorant `G_a`
  have hGS : Summable (fun j : ℤ => fAcG (ageA ν s) (xj ν j x)) := by
    have hα : 0 < 1 / (16 * ageA ν s) := div_pos one_pos (by linarith)
    refine Summable.of_nonneg_of_le hGnn (fun j => ?_)
      ((gp_gauss_summable x.1 (1 / (16 * ageA ν s)) (cOf ν) hα hc0).mul_left
        ((64 * ageA ν s / 5) ^ 4))
    unfold fAcG
    exact fAc_G_le (ageA ν s) (sq2 (xj ν j x)) (x.1 - (j : ℝ) * cOf ν) ha1 (hq0 j) (hq j)
  -- per-term estimate `m_j² / w_j ≤ (C0 (|B|+|C|))² G_a(x_j)`
  have hkey : ∀ j : ℤ, ‖merOf (eAcTerm ν s B C j x)‖ ^ 2 / fAcWt ν s x j
      ≤ (C0 * (frob B + frob C)) ^ 2 * fAcG (ageA ν s) (xj ν j x) := by
    intro j
    have h := fAc_term_sq_div (C0 * (frob B + frob C)) (ageA ν s) (sq2 (xj ν j x))
      (x.1 - (j : ℝ) * cOf ν) ‖merOf (eAcTerm ν s B C j x)‖ (fAcWt ν s x j) ha0 (hq j)
      (norm_nonneg _) (hT ν s B C j x hν hν1 hs hsT) rfl
    unfold fAcG
    exact h
  -- arithmetic-geometric mean: `m_j ≤ (m_j²/w_j + w_j)/2`
  have hmle : ∀ j : ℤ, ‖merOf (eAcTerm ν s B C j x)‖ ≤
      ((C0 * (frob B + frob C)) ^ 2 * fAcG (ageA ν s) (xj ν j x) + fAcWt ν s x j) / 2 := by
    intro j
    have hw0 : 0 < fAcWt ν s x j := by unfold fAcWt; exact Real.exp_pos _
    have hwne : fAcWt ν s x j ≠ 0 := hw0.ne'
    have h1 := hkey j
    have h2 : ‖merOf (eAcTerm ν s B C j x)‖ ^ 2 / fAcWt ν s x j + fAcWt ν s x j
        - 2 * ‖merOf (eAcTerm ν s B C j x)‖
        = (‖merOf (eAcTerm ν s B C j x)‖ - fAcWt ν s x j) ^ 2 / fAcWt ν s x j := by
      field_simp
      ring
    have h3 : 0 ≤ (‖merOf (eAcTerm ν s B C j x)‖ - fAcWt ν s x j) ^ 2 / fAcWt ν s x j :=
      div_nonneg (sq_nonneg _) hw0.le
    linarith
  have hmS : Summable (fun j : ℤ => ‖merOf (eAcTerm ν s B C j x)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hmle
      (((hGS.mul_left ((C0 * (frob B + frob C)) ^ 2)).add hwS).div_const 2)
  -- `merOf` of the lattice sum
  have h0 : merOf (0 : Vec3) = 0 := by
    have h := map_zero fAcMerL
    rw [fAcMerL_apply] at h
    exact h
  have hfAB_bound : ‖merOf (eAB ν s B C x)‖ ≤ ∑' j, ‖merOf (eAcTerm ν s B C j x)‖ := by
    by_cases hf : Summable (fun j : ℤ => eAcTerm ν s B C j x)
    · have e : eAB ν s B C x = ∑' j : ℤ, eAcTerm ν s B C j x := rfl
      rw [e, fAc_merOf_tsum _ hf]
      exact norm_tsum_le_tsum_norm hmS
    · have e : eAB ν s B C x = 0 := by
        unfold eAB
        exact tsum_eq_zero_of_not_summable hf
      rw [e, h0, norm_zero]
      exact tsum_nonneg (fun j => norm_nonneg _)
  -- finite Cauchy-Schwarz (Titu form) and the lattice bound
  have hWle : ∑' j : ℤ, fAcWt ν s x j ≤ C1 := hC1 (cOf ν) x.1 (ageA ν s) hc1 ha1 ha2
  have hFin : ∀ F : Finset ℤ, (∑ j ∈ F, ‖merOf (eAcTerm ν s B C j x)‖) ^ 2
      ≤ max C1 0 * ((C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) := by
    intro F
    have hsq : (∑ j ∈ F, ‖merOf (eAcTerm ν s B C j x)‖) ^ 2
        ≤ (∑ j ∈ F, ‖merOf (eAcTerm ν s B C j x)‖ ^ 2 / fAcWt ν s x j) * ∑ j ∈ F, fAcWt ν s x j := by
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · have hgpos : 0 < ∑ j ∈ F, fAcWt ν s x j :=
          Finset.sum_pos (fun j _ => by unfold fAcWt; exact Real.exp_pos _) hne
        have h := Finset.sq_sum_div_le_sum_sq_div F (fun j => ‖merOf (eAcTerm ν s B C j x)‖)
          (g := fun j => fAcWt ν s x j) (fun j _ => by unfold fAcWt; exact Real.exp_pos _)
        exact (div_le_iff₀ hgpos).mp h
    have hQ : ∑ j ∈ F, ‖merOf (eAcTerm ν s B C j x)‖ ^ 2 / fAcWt ν s x j
        ≤ (C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x) := by
      calc ∑ j ∈ F, ‖merOf (eAcTerm ν s B C j x)‖ ^ 2 / fAcWt ν s x j
          ≤ ∑ j ∈ F, (C0 * (frob B + frob C)) ^ 2 * fAcG (ageA ν s) (xj ν j x) :=
            Finset.sum_le_sum (fun j _ => hkey j)
        _ = (C0 * (frob B + frob C)) ^ 2 * ∑ j ∈ F, fAcG (ageA ν s) (xj ν j x) := by
            rw [Finset.mul_sum]
        _ ≤ (C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x) :=
            mul_le_mul_of_nonneg_left (sum_le_hasSum F (fun j _ => hGnn j) hGS.hasSum)
              (sq_nonneg _)
    have hSg : ∑ j ∈ F, fAcWt ν s x j ≤ max C1 0 := by
      have h1 : ∑ j ∈ F, fAcWt ν s x j ≤ ∑' j, fAcWt ν s x j :=
        sum_le_hasSum F (fun j _ => by unfold fAcWt; positivity) hwS.hasSum
      exact le_trans (h1.trans hWle) (le_max_left _ _)
    have hSgnn : 0 ≤ ∑ j ∈ F, fAcWt ν s x j :=
      Finset.sum_nonneg (fun j _ => by unfold fAcWt; positivity)
    have hTnn : 0 ≤ (C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x) :=
      mul_nonneg (sq_nonneg _) (tsum_nonneg hGnn)
    calc (∑ j ∈ F, ‖merOf (eAcTerm ν s B C j x)‖) ^ 2
        ≤ (∑ j ∈ F, ‖merOf (eAcTerm ν s B C j x)‖ ^ 2 / fAcWt ν s x j) *
            ∑ j ∈ F, fAcWt ν s x j := hsq
      _ ≤ ((C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) * max C1 0 :=
          mul_le_mul hQ hSg hSgnn hTnn
      _ = max C1 0 * ((C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) :=
          mul_comm _ _
  have hX : 0 ≤ max C1 0 * ((C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) :=
    mul_nonneg (le_max_right _ _) (mul_nonneg (sq_nonneg _) (tsum_nonneg hGnn))
  have hS : ∑' j, ‖merOf (eAcTerm ν s B C j x)‖
      ≤ Real.sqrt (max C1 0 * ((C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x))) :=
    Real.tsum_le_of_sum_le (fun j => norm_nonneg _)
      (fun F => le_trans (le_abs_self _) (Real.abs_le_sqrt (hFin F)))
  have hfin : ‖merOf (eAB ν s B C x)‖ ^ 2
      ≤ max C1 0 * ((C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) := by
    have h1 : ‖merOf (eAB ν s B C x)‖
        ≤ Real.sqrt (max C1 0 * ((C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x))) :=
      hfAB_bound.trans hS
    calc ‖merOf (eAB ν s B C x)‖ ^ 2
        ≤ (Real.sqrt (max C1 0 * ((C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = max C1 0 * ((C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) :=
          Real.sq_sqrt hX
  calc ‖merOf (eAB ν s B C x)‖ ^ 2
      ≤ max C1 0 * ((C0 * (frob B + frob C)) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) := hfin
    _ = max C1 0 * C0 ^ 2 * (frob B + frob C) ^ 2 * ∑' j : ℤ, fAcG (ageA ν s) (xj ν j x) := by
      ring

end UnforcedLeray.Short.PartIIIb.Concrete
