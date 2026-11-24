import UnforcedLeray.Short.PartIIa.Calc.BlockB1
import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, block `B₁`: the leaf `RemJetUnif` (task `PartII-a:R02/9/9`)

Target: `remJetUnif_of : LateMeanRemainder → RemJetUnif`.

Source of record: `the November 2 reference manuscript`, lines 447-459
(`sct:expansion`, remainder bound with `N = 1`, `b = a`).

Route: `LateMeanRemainder` gives, for each pair `(ℓ, a)`, constants `C ℓ a, M ℓ a, ν₀ ℓ a` with
bound `polyConst · · ν c * s^{-((a+5)/2)}` (`N = 1`).  The pairs `(ℓ, a)` with `ℓ ≤ 3`, `a ≤ 2`
lie in the finite set `S = range 4 ×ˢ range 3`; the constants are merged as
`C' = ∑ max (C p) 0`, `M' = ∑ M p`, `ν₀' = 1/(1 + ∑ 1/ν₀ p)`, using `polyConst_mono` and
`inv_one_add_le`.  For `a ≥ 1`, `s^{-((a+5)/2)} ≤ s^{-3}` on `s ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB1

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStream meanRemainder meanCoeff heatKernel1)

theorem remJetUnif_of (hR : LateMeanRemainder) : RemJetUnif := by
  intro ρ m hρ
  have key := fun (ℓ a : ℕ) => hR ρ 1 m a ℓ hρ
  choose! C M ν₀ hν₀ H using key
  obtain ⟨S, hS⟩ : ∃ S : Finset (ℕ × ℕ), S = Finset.range 4 ×ˢ Finset.range 3 := ⟨_, rfl⟩
  have hmemS : ∀ ℓ a : ℕ, ℓ ≤ 3 → a ≤ 2 → (ℓ, a) ∈ S := by
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
  intro ν hν hνle tr htr ℓ a hℓ ha1 ha2 x hx
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have hp : (ℓ, a) ∈ S := hmemS ℓ a hℓ ha2
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
  have hexp : x.2.2 ^ (-(((a : ℝ) + 5) / 2)) ≤ x.2.2 ^ (-3 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    have ha1' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    linarith
  have hBS : 0 ≤ polyConst (∑ p ∈ S, max (C p.1 p.2) 0) (∑ p ∈ S, M p.1 p.2) ν (ν ^ (-ρ)) := by
    unfold polyConst
    apply mul_nonneg (Finset.sum_nonneg fun p _ => le_max_right _ _)
    apply pow_nonneg
    have h1 : 0 ≤ ν ^ (-ρ) := hc.le
    have h2 : 0 ≤ ν⁻¹ := (inv_pos.2 hν).le
    linarith
  calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * |jet ℓ a 0 (remP tr 1) x|
      ≤ polyConst (C ℓ a) (M ℓ a) ν (ν ^ (-ρ)) * x.2.2 ^ (-(((a : ℝ) + 5) / 2)) := hH
    _ ≤ polyConst (∑ p ∈ S, max (C p.1 p.2) 0) (∑ p ∈ S, M p.1 p.2) ν (ν ^ (-ρ)) *
          x.2.2 ^ (-(((a : ℝ) + 5) / 2)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hx0 _)
    _ ≤ polyConst (∑ p ∈ S, max (C p.1 p.2) 0) (∑ p ∈ S, M p.1 p.2) ν (ν ^ (-ρ)) *
          x.2.2 ^ (-3 : ℝ) := mul_le_mul_of_nonneg_left hexp hBS

end UnforcedLeray.Short.PartIIa.BlockB1
