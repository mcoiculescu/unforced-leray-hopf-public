import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellTerm
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellLattice

/-!
# `PartIII-b:C/inst/9/3` leaf 3: pointwise square bound of `f_AB` (source 5063-5079)

Proves `FAcSumPointwise`: `‖merOf (fAB ν s B x)‖² ≤ K1 |B|² Σ_j G_a(x_j)`.

Plan. `merOf` is a continuous linear map, so it commutes with the summable lattice sum. Put
`w_j = e^{-(x₁ - jc)²/(8a)}` (the weight of the lattice leaf) and `m_j = ‖merOf t_j‖`. The term
bound of the first leaf gives `m_j² / w_j ≤ C0² |B|² G_a(x_j)`, because
`e^{-q/(4a)}² ≤ e^{-3q/(8a)} w_j` when `q = |x_j|² ≥ (x₁ - jc)²`. The Sedrakyan (Titu) form of
Cauchy-Schwarz over finite sets and the uniform bound `Σ_j w_j ≤ C1` of the lattice leaf give
`(Σ_j m_j)² ≤ max C1 0 · C0² |B|² Σ_j G_a(x_j)`, and `‖merOf (Σ_j t_j)‖ ≤ Σ_j m_j`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `merOf` as a continuous linear map, so that it commutes with convergent sums. -/
def fAcMerL : Vec3 →L[ℝ] UnforcedLeray.Axi.Merid :=
  LinearMap.toContinuousLinearMap
    { toFun := merOf
      map_add' := fun v w => by
        ext i
        fin_cases i <;> simp [merOf]
      map_smul' := fun r v => by
        ext i
        fin_cases i <;> simp [merOf, PiLp.smul_apply] }

lemma fAcMerL_apply (v : Vec3) : fAcMerL v = merOf v := rfl

lemma fAc_merOf_tsum (f : ℤ → Vec3) (hf : Summable f) :
    merOf (∑' j, f j) = ∑' j, merOf (f j) := by
  have h := fAcMerL.map_tsum hf
  simp only [fAcMerL_apply] at h
  exact h

lemma fAc_merOf_neg (v : Vec3) : merOf (-v) = -merOf v := by
  have h := map_neg fAcMerL v
  simp only [fAcMerL_apply] at h
  exact h

/-- The lattice weight `w_j = e^{-(x₁ - jc)²/(8a)}`. -/
def fAcWt (ν s : ℝ) (x : ℝ × ℝ) (j : ℤ) : ℝ :=
  Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2) / (8 * ageA ν s))

/-- Exponential algebra: `e^{-q/(4a)}² ≤ e^{-(3/8)q/a} · e^{-u²/(8a)}` when `u² ≤ q`. -/
lemma fAc_exp_step (q u a : ℝ) (ha : 0 < a) (hq : u ^ 2 ≤ q) :
    Real.exp (-q / (4 * a)) ^ 2 ≤ Real.exp (-(3 / 8) * q / a) * Real.exp (-(u ^ 2) / (8 * a)) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  rw [← Real.exp_add, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have key : -(3 / 8) * q / a + -(u ^ 2) / (8 * a) - ((2 : ℕ) : ℝ) * (-q / (4 * a))
      = (q - u ^ 2) / (8 * a) := by
    push_cast
    field_simp
    ring
  have h0 : 0 ≤ (q - u ^ 2) / (8 * a) := div_nonneg (by linarith) (by linarith)
  linarith

/-- Exponential algebra: the majorant `G_a` dominates a Gaussian of the first coordinate. -/
lemma fAc_G_le (a q u : ℝ) (ha1 : 1 ≤ a) (hq0 : 0 ≤ q) (hq : u ^ 2 ≤ q) :
    (1 + q) ^ 4 * Real.exp (-(3 / 8) * q / a)
      ≤ (64 * a / 5) ^ 4 * Real.exp (-(1 / (16 * a)) * u ^ 2) := by
  have ha0 : 0 < a := by linarith
  have ha' : a ≠ 0 := ne_of_gt ha0
  have hsplit : Real.exp (-(3 / 8) * q / a)
      = Real.exp (-(5 * q / (16 * a))) * Real.exp (-(q / (16 * a))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hy0 : 0 ≤ 5 * q / (16 * a) := div_nonneg (by linarith) (by linarith)
  have hE1 : 1 + (5 * q / (16 * a)) / 4 ≤ Real.exp ((5 * q / (16 * a)) / 4) := by
    linarith [Real.add_one_le_exp ((5 * q / (16 * a)) / 4)]
  have hE2 : (1 + (5 * q / (16 * a)) / 4) ^ 4 ≤ Real.exp (5 * q / (16 * a)) := by
    have h := pow_le_pow_left₀ (by linarith) hE1 4
    have e : Real.exp ((5 * q / (16 * a)) / 4) ^ 4 = Real.exp (5 * q / (16 * a)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    linarith
  have hA : 1 + q ≤ (64 * a / 5) * (1 + (5 * q / (16 * a)) / 4) := by
    have e : (64 * a / 5) * (1 + (5 * q / (16 * a)) / 4) = 64 * a / 5 + q := by
      field_simp
      ring
    linarith
  have hB : (1 + q) ^ 4 ≤ (64 * a / 5) ^ 4 * Real.exp (5 * q / (16 * a)) := by
    have h := pow_le_pow_left₀ (by linarith) hA 4
    calc (1 + q) ^ 4 ≤ ((64 * a / 5) * (1 + (5 * q / (16 * a)) / 4)) ^ 4 := h
      _ = (64 * a / 5) ^ 4 * (1 + (5 * q / (16 * a)) / 4) ^ 4 := by ring
      _ ≤ (64 * a / 5) ^ 4 * Real.exp (5 * q / (16 * a)) :=
          mul_le_mul_of_nonneg_left hE2 (pow_nonneg (by linarith) 4)
  have hC : (1 + q) ^ 4 * Real.exp (-(5 * q / (16 * a))) ≤ (64 * a / 5) ^ 4 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    exact hB
  have hD : Real.exp (-(q / (16 * a))) ≤ Real.exp (-(1 / (16 * a)) * u ^ 2) := by
    apply Real.exp_le_exp.mpr
    have key : -(1 / (16 * a)) * u ^ 2 - -(q / (16 * a)) = (q - u ^ 2) / (16 * a) := by
      field_simp
      ring
    have h0 : 0 ≤ (q - u ^ 2) / (16 * a) := div_nonneg (by linarith) (by linarith)
    linarith
  rw [hsplit]
  calc (1 + q) ^ 4 * (Real.exp (-(5 * q / (16 * a))) * Real.exp (-(q / (16 * a))))
      = ((1 + q) ^ 4 * Real.exp (-(5 * q / (16 * a)))) * Real.exp (-(q / (16 * a))) := by ring
    _ ≤ (64 * a / 5) ^ 4 * Real.exp (-(q / (16 * a))) :=
        mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
    _ ≤ (64 * a / 5) ^ 4 * Real.exp (-(1 / (16 * a)) * u ^ 2) :=
        mul_le_mul_of_nonneg_left hD (pow_nonneg (by linarith) 4)

/-- Per-term estimate: `m² / w ≤ M² G` for `m ≤ M (1+q)² e^{-q/(4a)}` and `w = e^{-u²/(8a)}`. -/
lemma fAc_term_sq_div (M a q u m w : ℝ) (ha : 0 < a) (hq : u ^ 2 ≤ q)
    (hm0 : 0 ≤ m) (hm : m ≤ M * (1 + q) ^ 2 * Real.exp (-q / (4 * a)))
    (hw : w = Real.exp (-(u ^ 2) / (8 * a))) :
    m ^ 2 / w ≤ M ^ 2 * ((1 + q) ^ 4 * Real.exp (-(3 / 8) * q / a)) := by
  have hw0 : 0 < w := by rw [hw]; exact Real.exp_pos _
  have hm2 : m ^ 2 ≤ (M * (1 + q) ^ 2 * Real.exp (-q / (4 * a))) ^ 2 :=
    pow_le_pow_left₀ hm0 hm 2
  have hstep := fAc_exp_step q u a ha hq
  rw [← hw] at hstep
  rw [div_le_iff₀ hw0]
  calc m ^ 2 ≤ (M * (1 + q) ^ 2 * Real.exp (-q / (4 * a))) ^ 2 := hm2
    _ = M ^ 2 * (1 + q) ^ 4 * Real.exp (-q / (4 * a)) ^ 2 := by ring
    _ ≤ M ^ 2 * (1 + q) ^ 4 * (Real.exp (-(3 / 8) * q / a) * w) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = M ^ 2 * ((1 + q) ^ 4 * Real.exp (-(3 / 8) * q / a)) * w := by ring

theorem fAcSumPointwise : FAcSumPointwise := by
  obtain ⟨C0, hC0, hT⟩ := fAcTermPointwise
  obtain ⟨C1, hC1⟩ := fAcLatticeWeight
  refine ⟨max C1 0 * C0 ^ 2, mul_nonneg (le_max_right _ _) (sq_nonneg _), ?_⟩
  intro ν s B x hν hν1 hs hsT
  have hfr : 0 ≤ frob B := by unfold frob; exact Real.sqrt_nonneg _
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
  -- summability of the lattice terms of `f_AB`
  have hTS : Summable (fun j : ℤ => fAcTerm ν s B j x) := by
    obtain ⟨K, hK⟩ := fa_term_bound ν s ha0 B x
    have hα : 0 < 1 / (4 * ageA ν s) := div_pos one_pos (by linarith)
    refine Summable.of_norm_bounded
      ((gp_poly_summable x.1 (1 / (4 * ageA ν s)) (cOf ν) hα hc0).mul_left K) (fun j => ?_)
    unfold fAcTerm
    exact hK j
  -- per-term estimate `m_j² / w_j ≤ (C0 |B|)² G_a(x_j)`
  have hkey : ∀ j : ℤ, ‖merOf (fAcTerm ν s B j x)‖ ^ 2 / fAcWt ν s x j
      ≤ (C0 * frob B) ^ 2 * fAcG (ageA ν s) (xj ν j x) := by
    intro j
    have h := fAc_term_sq_div (C0 * frob B) (ageA ν s) (sq2 (xj ν j x)) (x.1 - (j : ℝ) * cOf ν)
      ‖merOf (fAcTerm ν s B j x)‖ (fAcWt ν s x j) ha0 (hq j)
      (norm_nonneg _) (hT ν s B j x hν hν1 hs hsT) rfl
    unfold fAcG
    exact h
  -- arithmetic-geometric mean: `m_j ≤ (m_j²/w_j + w_j)/2`
  have hmle : ∀ j : ℤ, ‖merOf (fAcTerm ν s B j x)‖ ≤
      ((C0 * frob B) ^ 2 * fAcG (ageA ν s) (xj ν j x) + fAcWt ν s x j) / 2 := by
    intro j
    have hw0 : 0 < fAcWt ν s x j := by unfold fAcWt; exact Real.exp_pos _
    have hwne : fAcWt ν s x j ≠ 0 := hw0.ne'
    have h1 := hkey j
    have h2 : ‖merOf (fAcTerm ν s B j x)‖ ^ 2 / fAcWt ν s x j + fAcWt ν s x j
        - 2 * ‖merOf (fAcTerm ν s B j x)‖
        = (‖merOf (fAcTerm ν s B j x)‖ - fAcWt ν s x j) ^ 2 / fAcWt ν s x j := by
      field_simp
      ring
    have h3 : 0 ≤ (‖merOf (fAcTerm ν s B j x)‖ - fAcWt ν s x j) ^ 2 / fAcWt ν s x j :=
      div_nonneg (sq_nonneg _) hw0.le
    linarith
  have hmS : Summable (fun j : ℤ => ‖merOf (fAcTerm ν s B j x)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hmle
      (((hGS.mul_left ((C0 * frob B) ^ 2)).add hwS).div_const 2)
  -- `merOf` of the lattice sum
  have hfAB_bound : ‖merOf (fAB ν s B x)‖ ≤ ∑' j, ‖merOf (fAcTerm ν s B j x)‖ := by
    have e : fAB ν s B x = -(∑' j, fAcTerm ν s B j x) := rfl
    rw [e, fAc_merOf_neg, norm_neg, fAc_merOf_tsum _ hTS]
    exact norm_tsum_le_tsum_norm hmS
  -- finite Cauchy-Schwarz (Titu form) and the lattice bound
  have hWle : ∑' j : ℤ, fAcWt ν s x j ≤ C1 := hC1 (cOf ν) x.1 (ageA ν s) hc1 ha1 ha2
  have hFin : ∀ F : Finset ℤ, (∑ j ∈ F, ‖merOf (fAcTerm ν s B j x)‖) ^ 2
      ≤ max C1 0 * ((C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) := by
    intro F
    have hsq : (∑ j ∈ F, ‖merOf (fAcTerm ν s B j x)‖) ^ 2
        ≤ (∑ j ∈ F, ‖merOf (fAcTerm ν s B j x)‖ ^ 2 / fAcWt ν s x j) * ∑ j ∈ F, fAcWt ν s x j := by
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · have hgpos : 0 < ∑ j ∈ F, fAcWt ν s x j :=
          Finset.sum_pos (fun j _ => by unfold fAcWt; exact Real.exp_pos _) hne
        have h := Finset.sq_sum_div_le_sum_sq_div F (fun j => ‖merOf (fAcTerm ν s B j x)‖)
          (g := fun j => fAcWt ν s x j) (fun j _ => by unfold fAcWt; exact Real.exp_pos _)
        exact (div_le_iff₀ hgpos).mp h
    have hQ : ∑ j ∈ F, ‖merOf (fAcTerm ν s B j x)‖ ^ 2 / fAcWt ν s x j
        ≤ (C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x) := by
      calc ∑ j ∈ F, ‖merOf (fAcTerm ν s B j x)‖ ^ 2 / fAcWt ν s x j
          ≤ ∑ j ∈ F, (C0 * frob B) ^ 2 * fAcG (ageA ν s) (xj ν j x) :=
            Finset.sum_le_sum (fun j _ => hkey j)
        _ = (C0 * frob B) ^ 2 * ∑ j ∈ F, fAcG (ageA ν s) (xj ν j x) := by rw [Finset.mul_sum]
        _ ≤ (C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x) :=
            mul_le_mul_of_nonneg_left (sum_le_hasSum F (fun j _ => hGnn j) hGS.hasSum)
              (sq_nonneg _)
    have hSg : ∑ j ∈ F, fAcWt ν s x j ≤ max C1 0 := by
      have h1 : ∑ j ∈ F, fAcWt ν s x j ≤ ∑' j, fAcWt ν s x j :=
        sum_le_hasSum F (fun j _ => by unfold fAcWt; positivity) hwS.hasSum
      exact le_trans (h1.trans hWle) (le_max_left _ _)
    have hSgnn : 0 ≤ ∑ j ∈ F, fAcWt ν s x j :=
      Finset.sum_nonneg (fun j _ => by unfold fAcWt; positivity)
    have hTnn : 0 ≤ (C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x) :=
      mul_nonneg (sq_nonneg _) (tsum_nonneg hGnn)
    calc (∑ j ∈ F, ‖merOf (fAcTerm ν s B j x)‖) ^ 2
        ≤ (∑ j ∈ F, ‖merOf (fAcTerm ν s B j x)‖ ^ 2 / fAcWt ν s x j) *
            ∑ j ∈ F, fAcWt ν s x j := hsq
      _ ≤ ((C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) * max C1 0 :=
          mul_le_mul hQ hSg hSgnn hTnn
      _ = max C1 0 * ((C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) := mul_comm _ _
  have hX : 0 ≤ max C1 0 * ((C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) :=
    mul_nonneg (le_max_right _ _) (mul_nonneg (sq_nonneg _) (tsum_nonneg hGnn))
  have hS : ∑' j, ‖merOf (fAcTerm ν s B j x)‖
      ≤ Real.sqrt (max C1 0 * ((C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x))) :=
    Real.tsum_le_of_sum_le (fun j => norm_nonneg _)
      (fun F => le_trans (le_abs_self _) (Real.abs_le_sqrt (hFin F)))
  have hfin : ‖merOf (fAB ν s B x)‖ ^ 2
      ≤ max C1 0 * ((C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) := by
    have h1 : ‖merOf (fAB ν s B x)‖
        ≤ Real.sqrt (max C1 0 * ((C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x))) :=
      hfAB_bound.trans hS
    calc ‖merOf (fAB ν s B x)‖ ^ 2
        ≤ (Real.sqrt (max C1 0 * ((C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = max C1 0 * ((C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) :=
          Real.sq_sqrt hX
  calc ‖merOf (fAB ν s B x)‖ ^ 2
      ≤ max C1 0 * ((C0 * frob B) ^ 2 * ∑' j, fAcG (ageA ν s) (xj ν j x)) := hfin
    _ = max C1 0 * C0 ^ 2 * frob B ^ 2 * ∑' j : ℤ, fAcG (ageA ν s) (xj ν j x) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
