import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.ParChartJet
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Weighted composition through the parity chart (`parCompWeightJet`)

Source: `the November 2 reference manuscript` lines 1287-1291 (parity chart), with
the Leibniz and Faa di Bruno bounds of `ParChartJet` and `ParWeightJet`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

theorem pcw_hN (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

theorem pcw_open_t : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  isOpen_Ioi.prod isOpen_univ

theorem pcw_iter_eq {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (i : ℕ)
    (f : ℝ × (ℝ × ℝ) → F) {x : ℝ × (ℝ × ℝ)} (hx : x ∈ parPos) :
    iteratedFDerivWithin ℝ i f parPos x = iteratedFDeriv ℝ i f x :=
  iteratedFDerivWithin_of_isOpen i isOpen_parPos hx

theorem pcw_maps (R : ℝ) (hR : 0 < R) :
    MapsTo (parChart R) parPos (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  intro x hx
  have hw : 0 < x.2.1 := hx
  refine ⟨?_, mem_univ _⟩
  show 0 < R ^ 2 / x.2.1
  exact div_pos (pow_pos hR 2) hw

/-- Exponent algebra: `w^(-a-i) w^β (D/w²)^j ≤ D^j w^(β-a-2n)` for `i + j = n`, `0 < w ≤ 1`. -/
theorem pcw_key (w a β D : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) (hD : 0 ≤ D) (i j n : ℕ)
    (hn : i + j = n) :
    w ^ (-a - (i : ℝ)) * w ^ β * (D / w ^ 2) ^ j ≤ D ^ j * w ^ (β - a - 2 * (n : ℝ)) := by
  have hn' : (n : ℝ) = (i : ℝ) + (j : ℝ) := by
    rw [← hn, Nat.cast_add]
  have e2 : (w ^ (2 * j))⁻¹ = w ^ (-(2 * (j : ℝ))) := by
    rw [Real.rpow_neg hw.le, show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by simp, Real.rpow_natCast]
  have e1 : (D / w ^ 2) ^ j = D ^ j * (w ^ (2 * j))⁻¹ := by
    rw [div_pow, ← pow_mul, div_eq_mul_inv]
  have hpow : w ^ (i : ℝ) ≤ 1 := by
    rw [Real.rpow_natCast]
    exact pow_le_one₀ hw.le hw1
  have hpos : 0 ≤ w ^ (β - a - 2 * (n : ℝ)) := Real.rpow_nonneg hw.le _
  have hsplit : w ^ ((-a - (i : ℝ)) + β + -(2 * (j : ℝ))) =
      w ^ (β - a - 2 * (n : ℝ)) * w ^ (i : ℝ) := by
    rw [← Real.rpow_add hw]
    congr 1
    rw [hn']
    ring
  calc w ^ (-a - (i : ℝ)) * w ^ β * (D / w ^ 2) ^ j
      = D ^ j * w ^ ((-a - (i : ℝ)) + β + -(2 * (j : ℝ))) := by
        rw [e1, Real.rpow_add hw, Real.rpow_add hw, e2]
        ring
    _ = D ^ j * (w ^ (β - a - 2 * (n : ℝ)) * w ^ (i : ℝ)) := by rw [hsplit]
    _ ≤ D ^ j * w ^ (β - a - 2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hpos hpow) (pow_nonneg hD j)

/-- The value bound `(R²/w)^(-β) ≤ w^β` for `R ≥ 1`, `0 < w`. -/
theorem pcw_inv_pow_le (R : ℝ) (hR1 : 1 ≤ R) (w β : ℝ) (hw : 0 < w) (hβ : 0 ≤ β) :
    (R ^ 2 / w) ^ (-β) ≤ w ^ β := by
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hle : 1 / w ≤ R ^ 2 / w := div_le_div_of_nonneg_right hR2 hw.le
  have h := Real.rpow_le_rpow_of_nonpos (one_div_pos.2 hw) hle (neg_nonpos.2 hβ)
  rw [one_div, Real.inv_rpow hw.le (-β), Real.rpow_neg hw.le β, inv_inv] at h
  exact h

theorem pcw_sqrt_chart (R : ℝ) (hR : 0 < R) (w : ℝ) :
    Real.sqrt (R ^ 2 / w) = R / Real.sqrt w := by
  rw [Real.sqrt_div (sq_nonneg R), Real.sqrt_sq hR.le]

/-- The chart's `z`-coordinate against the square root of its age coordinate. -/
theorem pcw_chart_bound (R M : ℝ) (hR : 0 < R) (x : ℝ × (ℝ × ℝ)) (hw : 0 < x.2.1)
    (hzM : |x.2.2| ≤ M) :
    |(parChart R x).2.2| ≤ M * Real.sqrt (parChart R x).1 := by
  have hs : 0 < Real.sqrt x.2.1 := Real.sqrt_pos.2 hw
  have h1 : (parChart R x).2.2 = R * x.2.2 / Real.sqrt x.2.1 := rfl
  have h2 : (parChart R x).1 = R ^ 2 / x.2.1 := rfl
  rw [h1, h2, pcw_sqrt_chart R hR x.2.1, abs_div, abs_mul, abs_of_pos hR,
    abs_of_pos hs]
  calc R * |x.2.2| / Real.sqrt x.2.1 ≤ R * M / Real.sqrt x.2.1 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzM hR.le) hs.le
    _ = M * (R / Real.sqrt x.2.1) := by ring

/-- Derivatives of `g ∘ parChart R` on the half space, with the constant and power bounds. -/
theorem pcw_comp_bound (R β : ℝ) (hR1 : 1 ≤ R) (hβ : 0 ≤ β)
    (g : ℝ × (ℝ × ℝ) → ℝ) (hg : ContDiffOn ℝ ∞ g (Ioi 0 ×ˢ univ))
    (hgb : ∀ (i : ℕ) (M : ℝ), ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 →
      |y.2.2| ≤ M * Real.sqrt y.1 → ‖iteratedFDeriv ℝ i g y‖ ≤ C * y.1 ^ (-β))
    (n : ℕ) (M : ℝ) :
    ∃ K D : ℝ, 0 ≤ K ∧ 0 ≤ D ∧ ∀ x ∈ parPos, x.2.1 ≤ 1 → |x.2.2| ≤ M → ∀ m : ℕ, m ≤ n →
      ‖iteratedFDeriv ℝ m (fun y => g (parChart R y)) x‖ ≤
        (m.factorial : ℝ) * (K * x.2.1 ^ β) * (D / x.2.1 ^ 2) ^ m := by
  have hR : 0 < R := by linarith
  choose Cg hCg using hgb
  obtain ⟨D, hD0, hDb⟩ := (parChartJet R hR).2 n M
  refine ⟨∑ l ∈ Finset.range (n + 1), |Cg l M|, D,
    Finset.sum_nonneg (fun l _ => abs_nonneg _), hD0, ?_⟩
  intro x hx hx1 hzM m hmn
  have hw : 0 < x.2.1 := hx
  have hmem : x ∈ parPos := hx
  have hy1 : 1 ≤ (parChart R x).1 := by
    show 1 ≤ R ^ 2 / x.2.1
    rw [le_div_iff₀ hw]
    nlinarith
  have hval : ∀ i : ℕ, i ≤ n →
      ‖iteratedFDeriv ℝ i g (parChart R x)‖ ≤
        (∑ l ∈ Finset.range (n + 1), |Cg l M|) * x.2.1 ^ β := by
    intro i hi
    have hC := hCg i M (parChart R x) hy1 (pcw_chart_bound R M hR x hw hzM)
    have hpow : (parChart R x).1 ^ (-β) ≤ x.2.1 ^ β := pcw_inv_pow_le R hR1 x.2.1 β hw hβ
    have ht0 : 0 ≤ (parChart R x).1 ^ (-β) := Real.rpow_nonneg (by linarith) _
    have hsingle : |Cg i M| ≤ ∑ l ∈ Finset.range (n + 1), |Cg l M| :=
      Finset.single_le_sum (f := fun l => |Cg l M|) (fun l _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    have hwb : 0 ≤ x.2.1 ^ β := Real.rpow_nonneg hw.le _
    calc ‖iteratedFDeriv ℝ i g (parChart R x)‖
        ≤ Cg i M * (parChart R x).1 ^ (-β) := hC
      _ ≤ |Cg i M| * (parChart R x).1 ^ (-β) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) ht0
      _ ≤ |Cg i M| * x.2.1 ^ β := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ ≤ (∑ l ∈ Finset.range (n + 1), |Cg l M|) * x.2.1 ^ β :=
          mul_le_mul_of_nonneg_right hsingle hwb
  have hC' : ∀ i : ℕ, i ≤ m →
      ‖iteratedFDerivWithin ℝ i g (Ioi 0 ×ˢ univ) (parChart R x)‖ ≤
        (∑ l ∈ Finset.range (n + 1), |Cg l M|) * x.2.1 ^ β := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i pcw_open_t ((pcw_maps R hR) hmem)]
    exact hval i (hi.trans hmn)
  have hD' : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      ‖iteratedFDerivWithin ℝ i (parChart R) parPos x‖ ≤ (D / x.2.1 ^ 2) ^ i := by
    intro i h1 h2
    rw [pcw_iter_eq i _ hmem]
    exact hDb x hmem hx1 hzM i h1 (h2.trans hmn)
  have hFdB := norm_iteratedFDerivWithin_comp_le (g := g) (f := parChart R) (n := m)
    (hg) (pc_smooth R hR) (pcw_hN m) pcw_open_t.uniqueDiffOn isOpen_parPos.uniqueDiffOn (pcw_maps R hR) hmem
    hC' hD'
  have hconv : iteratedFDeriv ℝ m (fun y => g (parChart R y)) x =
      iteratedFDerivWithin ℝ m (g ∘ parChart R) parPos x :=
    (pcw_iter_eq m _ hmem).symm
  rw [hconv]
  exact hFdB

/-- **Weighted composition through the parity chart** (`ParCompWeightJet`). -/
theorem parCompWeightJet : UnforcedLeray.Short.IIb.ParCompWeightJet := by
  intro R a β wt g hR1 hβ hwt hg hwb hgb
  have hR : 0 < R := by linarith
  have hF : ContDiffOn ℝ ∞ (fun x => g (parChart R x)) parPos :=
    hg.comp (pc_smooth R hR) (pcw_maps R hR)
  refine ⟨hwt.mul hF, ?_⟩
  intro n M
  obtain ⟨K, D, hK, hD0, hbd⟩ := pcw_comp_bound R β hR1 hβ g hg hgb n M
  obtain ⟨Cw, hCw⟩ := hwb n
  refine ⟨∑ i ∈ Finset.range (n + 1),
    ((n.choose i : ℝ) * (|Cw| * ((n - i).factorial : ℝ) * K * D ^ (n - i))), ?_⟩
  intro x hx hx1 hzM
  have hw : 0 < x.2.1 := hx
  have hmem : x ∈ parPos := hx
  have hL := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) hwt hF isOpen_parPos.uniqueDiffOn hmem
    (pcw_hN n)
  simp only [pcw_iter_eq _ _ hmem] at hL
  refine hL.trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i wt x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y => g (parChart R y)) x‖ ≤
        (n.choose i : ℝ) * (|Cw| * ((n - i).factorial : ℝ) * K * D ^ (n - i)) *
          x.2.1 ^ (β - a - 2 * (n : ℝ)) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hA : ‖iteratedFDeriv ℝ i wt x‖ ≤ |Cw| * x.2.1 ^ (-a - (i : ℝ)) := by
      refine (hCw x hmem hx1 i hi').trans ?_
      exact mul_le_mul_of_nonneg_right (le_abs_self Cw) (Real.rpow_nonneg hw.le _)
    have hB : ‖iteratedFDeriv ℝ (n - i) (fun y => g (parChart R y)) x‖ ≤
        ((n - i).factorial : ℝ) * (K * x.2.1 ^ β) * (D / x.2.1 ^ 2) ^ (n - i) :=
      hbd x hmem hx1 hzM (n - i) (Nat.sub_le n i)
    have hchoose : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    have hfac : (0 : ℝ) ≤ ((n - i).factorial : ℝ) := Nat.cast_nonneg _
    have hA0 : 0 ≤ |Cw| * x.2.1 ^ (-a - (i : ℝ)) :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hw.le _)
    have hB0 : 0 ≤ ((n - i).factorial : ℝ) * (K * x.2.1 ^ β) * (D / x.2.1 ^ 2) ^ (n - i) := by
      have hK' : 0 ≤ K * x.2.1 ^ β := mul_nonneg hK (Real.rpow_nonneg hw.le _)
      have hDp : 0 ≤ (D / x.2.1 ^ 2) ^ (n - i) := pow_nonneg (div_nonneg hD0 (sq_nonneg _)) _
      exact mul_nonneg (mul_nonneg hfac hK') hDp
    have h1 : (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i wt x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y => g (parChart R y)) x‖ ≤
        (n.choose i : ℝ) * (|Cw| * x.2.1 ^ (-a - (i : ℝ))) *
          (((n - i).factorial : ℝ) * (K * x.2.1 ^ β) * (D / x.2.1 ^ 2) ^ (n - i)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hA hchoose) hB (norm_nonneg _)
        (mul_nonneg hchoose hA0)
    have hcoef : 0 ≤ (n.choose i : ℝ) * (|Cw| * ((n - i).factorial : ℝ) * K) :=
      mul_nonneg hchoose (mul_nonneg (mul_nonneg (abs_nonneg _) hfac) hK)
    have hkey := pcw_key x.2.1 a β D hw hx1 hD0 i (n - i) n (Nat.add_sub_of_le hi')
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i wt x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y => g (parChart R y)) x‖
        ≤ (n.choose i : ℝ) * (|Cw| * x.2.1 ^ (-a - (i : ℝ))) *
          (((n - i).factorial : ℝ) * (K * x.2.1 ^ β) * (D / x.2.1 ^ 2) ^ (n - i)) := h1
      _ = (n.choose i : ℝ) * (|Cw| * ((n - i).factorial : ℝ) * K) *
            (x.2.1 ^ (-a - (i : ℝ)) * x.2.1 ^ β * (D / x.2.1 ^ 2) ^ (n - i)) := by ring
      _ ≤ (n.choose i : ℝ) * (|Cw| * ((n - i).factorial : ℝ) * K) *
            (D ^ (n - i) * x.2.1 ^ (β - a - 2 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hkey hcoef
      _ = (n.choose i : ℝ) * (|Cw| * ((n - i).factorial : ℝ) * K * D ^ (n - i)) *
            x.2.1 ^ (β - a - 2 * (n : ℝ)) := by ring
  exact (Finset.sum_le_sum hterm).trans (le_of_eq (Finset.sum_mul _ _ _).symm)

end UnforcedLeray.Short.IIb
