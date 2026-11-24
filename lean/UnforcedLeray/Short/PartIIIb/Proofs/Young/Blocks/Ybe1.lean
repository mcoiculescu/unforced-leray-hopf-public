import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.GronwallApply
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Setup

/-!
# `YBE1` from the retained block estimates (source 4376-4411)

Reflexivity of the evolution (`𝒰(s,s) = id`) is `BlockSetup.refl`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

theorem ybe1_holds (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) (δ : ℕ → ℝ)
    (hGr : ConcreteYF.BlockGronwall) (hS : ConcreteYF.BlockSetup pk ν lam κ Sg α δ) :
    ConcreteYF.YBE1 pk ν lam κ Sg α := by
  obtain ⟨K2, g, N, hg, hK2, hmain⟩ := gronwall_apply hGr hS
  obtain ⟨CB, hCB⟩ := hS.bdd
  obtain ⟨hpos, -, -, hα, hαS⟩ := hS.hyp
  refine ⟨K2, N, ?_⟩
  intro n hn t ht i j
  have hv : 0 < ν n := hpos n
  have ht0 : 0 ≤ t := ht.1
  have htH : t ≤ Sg / ν n := ht.2.trans (div_le_div_of_nonneg_right hαS.le hv.le)
  have hH0 : 0 ≤ Sg / ν n := ht0.trans htH
  obtain ⟨f1, -, f3, f4, -, -⟩ := block_setup_facts (pk n) lam κ (ν n) t hv ht0 (hS.refl n)
    (hS.gram n) CB (fun j => hCB n t ⟨ht0, htH⟩ j)
  obtain ⟨h1, -⟩ := hmain n hn t ht ((pk n).q j t)
  have hFi : ‖Fpm i lam κ (ν n) (Sg / ν n) t‖ = ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ := by
    cases i
    · exact (fpm_facts (ν n) hv lam κ (Sg / ν n) t hH0 ht0).2.2
    · rfl
  have hsum : ‖ampN (pk n) lam κ (ν n) t ((pk n).q j t) true t‖ +
      ‖ampN (pk n) lam κ (ν n) t ((pk n).q j t) false t‖ +
      cmpN (pk n) lam κ (ν n) t ((pk n).q j t) t = 1 := by
    rw [f4 j, f3 j true, f3 j false]
    cases j <;> simp
  have hA := h1 i
  rw [hsum, mul_one] at hA
  rw [f1 ((pk n).q j t) i _ hH0]
  have hexp : Fpm i lam κ (ν n) (Sg / ν n) t *
        ampN (pk n) lam κ (ν n) t ((pk n).q j t) i (Sg / ν n) -
      (if i = j then Fpm j lam κ (ν n) (Sg / ν n) t else 0) =
      Fpm i lam κ (ν n) (Sg / ν n) t *
        (ampN (pk n) lam κ (ν n) t ((pk n).q j t) i (Sg / ν n) -
          ampN (pk n) lam κ (ν n) t ((pk n).q j t) i t) := by
    rw [f3 j i]
    by_cases h : i = j
    · subst h; simp [mul_sub]
    · simp [h]
  rw [hexp, norm_mul, hFi]
  calc ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ *
        ‖ampN (pk n) lam κ (ν n) t ((pk n).q j t) i (Sg / ν n) -
          ampN (pk n) lam κ (ν n) t ((pk n).q j t) i t‖
      ≤ ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ * (K2 * ν n) :=
        mul_le_mul_of_nonneg_left hA (norm_nonneg _)
    _ = K2 * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ := by ring

end ConcreteYF

end UnforcedLeray.Short.PartIIIb
