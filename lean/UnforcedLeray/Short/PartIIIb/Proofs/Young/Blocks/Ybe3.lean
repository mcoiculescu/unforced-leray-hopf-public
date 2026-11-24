import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.GronwallApply
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Setup

/-!
# `YBE3` from the retained block estimates (source 4376-4411)

Reflexivity of the evolution (`𝒰(s,s) = id`) is `BlockSetup.refl`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

theorem ybe3_holds (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) (δ : ℕ → ℝ)
    (hGr : ConcreteYF.BlockGronwall) (hS : ConcreteYF.BlockSetup pk ν lam κ Sg α δ) :
    ConcreteYF.YBE3 pk ν lam κ Sg α := by
  obtain ⟨K2, g, N, hg, hK2, hmain⟩ := gronwall_apply hGr hS
  obtain ⟨CB, hCB⟩ := hS.bdd
  obtain ⟨hpos, -, -, hα, hαS⟩ := hS.hyp
  refine ⟨K2 * (1 + 2 * CB ^ 2), N, ?_⟩
  intro n hn t ht i y
  have hv : 0 < ν n := hpos n
  have ht0 : 0 ≤ t := ht.1
  have htH : t ≤ Sg / ν n := ht.2.trans (div_le_div_of_nonneg_right hαS.le hv.le)
  have hH0 : 0 ≤ Sg / ν n := ht0.trans htH
  obtain ⟨f1, -, -, -, f5, f6⟩ := block_setup_facts (pk n) lam κ (ν n) t hv ht0 (hS.refl n)
    (hS.gram n) CB (fun j => hCB n t ⟨ht0, htH⟩ j)
  have hFi : ‖Fpm i lam κ (ν n) (Sg / ν n) t‖ = ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ := by
    cases i
    · exact (fpm_facts (ν n) hv lam κ (Sg / ν n) t hH0 ht0).2.2
    · rfl
  have hsum : ‖ampN (pk n) lam κ (ν n) t (Pc (pk n) t y) true t‖ +
      ‖ampN (pk n) lam κ (ν n) t (Pc (pk n) t y) false t‖ +
      cmpN (pk n) lam κ (ν n) t (Pc (pk n) t y) t = ‖Pc (pk n) t y‖ := by
    rw [f5 y true, f5 y false, (f6 y).1]
    simp
  have hHy := (hmain n hn t ht (Pc (pk n) t y)).1 i
  rw [hsum, f5 y i, sub_zero] at hHy
  have hA : ‖ampN (pk n) lam κ (ν n) t (Pc (pk n) t y) i (Sg / ν n)‖ ≤
      K2 * ν n * ((1 + 2 * CB ^ 2) * ‖y‖) :=
    hHy.trans (mul_le_mul_of_nonneg_left (f6 y).2 (mul_nonneg hK2 hv.le))
  rw [f1 (Pc (pk n) t y) i (Sg / ν n) hH0, norm_mul]
  calc ‖Fpm i lam κ (ν n) (Sg / ν n) t‖ *
        ‖ampN (pk n) lam κ (ν n) t (Pc (pk n) t y) i (Sg / ν n)‖
      ≤ ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ * (K2 * ν n * ((1 + 2 * CB ^ 2) * ‖y‖)) := by
        rw [hFi]
        exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)
    _ = K2 * (1 + 2 * CB ^ 2) * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ * ‖y‖ := by ring

end ConcreteYF

end UnforcedLeray.Short.PartIIIb
