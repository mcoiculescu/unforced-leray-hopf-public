import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.GronwallApply
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Setup

/-!
# `YBE2` from the retained block estimates (source 4376-4411)

Reflexivity of the evolution (`𝒰(s,s) = id`) is `BlockSetup.refl`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

theorem ybe2_holds (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) (δ : ℕ → ℝ)
    (hGr : ConcreteYF.BlockGronwall) (hS : ConcreteYF.BlockSetup pk ν lam κ Sg α δ) :
    ConcreteYF.YBE2 pk ν lam κ Sg α := by
  obtain ⟨K2, g, N, hg, hK2, hmain⟩ := gronwall_apply hGr hS
  obtain ⟨CB, hCB⟩ := hS.bdd
  obtain ⟨hpos, -, -, hα, hαS⟩ := hS.hyp
  refine ⟨K2, N, ?_⟩
  intro n hn t ht j
  have hv : 0 < ν n := hpos n
  have ht0 : 0 ≤ t := ht.1
  have htH : t ≤ Sg / ν n := ht.2.trans (div_le_div_of_nonneg_right hαS.le hv.le)
  have hH0 : 0 ≤ Sg / ν n := ht0.trans htH
  obtain ⟨-, f2, f3, f4, -, -⟩ := block_setup_facts (pk n) lam κ (ν n) t hv ht0 (hS.refl n)
    (hS.gram n) CB (fun j => hCB n t ⟨ht0, htH⟩ j)
  have hsum : ‖ampN (pk n) lam κ (ν n) t ((pk n).q j t) true t‖ +
      ‖ampN (pk n) lam κ (ν n) t ((pk n).q j t) false t‖ +
      cmpN (pk n) lam κ (ν n) t ((pk n).q j t) t = 1 := by
    rw [f4 j, f3 j true, f3 j false]
    cases j <;> simp
  have hR : cmpN (pk n) lam κ (ν n) t ((pk n).q j t) (Sg / ν n) ≤ K2 * ν n := by
    have h := (hmain n hn t ht ((pk n).q j t)).2
    rw [hsum, f4 j] at h
    simp only [mul_zero, zero_add, mul_one] at h
    exact h
  calc ‖Pc (pk n) (Sg / ν n) ((pk n).Uev (Sg / ν n) t ((pk n).q j t))‖
      = ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ *
          cmpN (pk n) lam κ (ν n) t ((pk n).q j t) (Sg / ν n) :=
        f2 ((pk n).q j t) (Sg / ν n) hH0
    _ ≤ ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ * (K2 * ν n) :=
        mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    _ = K2 * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ := by ring

end ConcreteYF

end UnforcedLeray.Short.PartIIIb
