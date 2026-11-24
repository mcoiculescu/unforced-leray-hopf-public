import UnforcedLeray.Short.PartIIa.Calc.BlockB3
import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, block `B₃`: the leaf `RemJetUnif3` (task `PartII-a:R02/11/9`)

Target: `remJetUnif3_of : LateMeanRemainder → RemJetUnif3`.

Source of record: `the November 2 reference manuscript`, lines 447-459
(`sct:expansion`, remainder bound with `N = 1`, `b = a`, `p = ∞`).

Route: `LateMeanRemainder` gives, for each pair `(ℓ, a)`, constants `C ℓ a, M ℓ a, ν₀ ℓ a`.
The pairs `(ℓ, a)` with `ℓ < 5`, `a < 2` form a finite set `S`; the constants are merged as
`C' = ∑ max (C p) 0`, `M' = ∑ M p`, `ν₀' = 1/(1 + ∑ 1/ν₀ p)`, using `polyConst_mono` and
`inv_one_add_le`.  The exponent `-(((a:ℝ) + 2 * 1 + 3)/2)` equals `-((a+5)/2)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB3

theorem remJetUnif3_of (h : UnforcedLeray.Short.PartIIa.LateMeanRemainder) :
    UnforcedLeray.Short.PartIIa.BlockB3.RemJetUnif3 := by
  intro ρ m hρ
  have key := fun (ℓ a : ℕ) => h ρ 1 m a ℓ hρ
  choose! C M ν₀ hν₀ H using key
  obtain ⟨S, hS⟩ : ∃ S : Finset (ℕ × ℕ), S = Finset.range 5 ×ˢ Finset.range 2 := ⟨_, rfl⟩
  have hmemS : ∀ ℓ a : ℕ, ℓ ≤ 4 → a ≤ 1 → (ℓ, a) ∈ S := by
    intro ℓ a hℓ ha
    rw [hS]
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
  have he : ∀ a : ℕ, -(((a : ℝ) + 2 * ((1 : ℕ) : ℝ) + 3) / 2) = -(((a : ℝ) + 5) / 2) := by
    intro a
    push_cast
    ring
  refine ⟨∑ p ∈ S, max (C p.1 p.2) 0, ∑ p ∈ S, M p.1 p.2,
    1 / (1 + ∑ p ∈ S, 1 / ν₀ p.1 p.2),
    inv_one_add_pos (Finset.sum_nonneg fun p _ => (one_div_pos.2 (hν₀ p.1 p.2)).le), ?_⟩
  intro ν hν hνle tr htr ℓ a hℓ ha x hx
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have hp : (ℓ, a) ∈ S := hmemS ℓ a hℓ ha
  have hνp : ν ≤ ν₀ ℓ a := by
    have h1 : 1 / ν₀ ℓ a ≤ ∑ p ∈ S, 1 / ν₀ p.1 p.2 :=
      Finset.single_le_sum (f := fun p : ℕ × ℕ => 1 / ν₀ p.1 p.2)
        (fun p _ => (one_div_pos.2 (hν₀ p.1 p.2)).le) hp
    exact hνle.trans (inv_one_add_le (hν₀ ℓ a) h1)
  have hpoly : polyConst (C ℓ a) (M ℓ a) ν (ν ^ (-ρ)) ≤
      polyConst (∑ p ∈ S, max (C p.1 p.2) 0) (∑ p ∈ S, M p.1 p.2) ν (ν ^ (-ρ)) := by
    apply polyConst_mono hν hc
    · calc C ℓ a ≤ max (C ℓ a) 0 := le_max_left _ _
        _ ≤ ∑ p ∈ S, max (C p.1 p.2) 0 :=
          Finset.single_le_sum (f := fun p : ℕ × ℕ => max (C p.1 p.2) 0)
            (fun p _ => le_max_right _ _) hp
    · exact Finset.sum_nonneg fun p _ => le_max_right _ _
    · exact Finset.single_le_sum (f := fun p : ℕ × ℕ => M p.1 p.2)
        (fun p _ => Nat.zero_le _) hp
  have hH : (1 + x.2.1 ^ 2 / x.2.2) ^ m * |jet ℓ a 0 (remP tr 1) x| ≤
      polyConst (C ℓ a) (M ℓ a) ν (ν ^ (-ρ)) * x.2.2 ^ (-(((a : ℝ) + 5) / 2)) := by
    have := H ℓ a ν hν hνp tr htr x hx
    rw [he a] at this
    exact this
  have hx0 : (0 : ℝ) ≤ x.2.2 := le_trans zero_le_one hx
  exact hH.trans (mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hx0 _))

end UnforcedLeray.Short.PartIIa.BlockB3
