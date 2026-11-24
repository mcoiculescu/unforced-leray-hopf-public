import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.GronwallApply
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Setup

/-!
# `YBE4` from the retained block estimates (source 4376-4411)

Reflexivity of the evolution (`𝒰(s,s) = id`) is `BlockSetup.refl`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

theorem ybe4_holds (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) (δ : ℕ → ℝ)
    (hGr : ConcreteYF.BlockGronwall)
    (hS : ConcreteYF.BlockSetup pk ν lam κ Sg α δ) :
    ConcreteYF.YBE4 pk ν lam κ Sg α := by
  obtain ⟨K2, g, N, hg, hK2, hmain⟩ := gronwall_apply hGr hS
  obtain ⟨CB, hCB⟩ := hS.bdd
  obtain ⟨hpos, -, -, hα, hαS⟩ := hS.hyp
  have hD : 0 < g * (Sg - α) := mul_pos hg (by linarith)
  refine ⟨K2 * (1 / (g * (Sg - α)) + 1) * (1 + 2 * CB ^ 2), N, ?_⟩
  intro n hn t ht
  have hv : 0 < ν n := hpos n
  have ht0 : 0 ≤ t := ht.1
  have htH : t ≤ Sg / ν n := ht.2.trans (div_le_div_of_nonneg_right hαS.le hv.le)
  have hH0 : 0 ≤ Sg / ν n := ht0.trans htH
  obtain ⟨-, f2, -, -, f5, f6⟩ := block_setup_facts (pk n) lam κ (ν n) t hv ht0 (hS.refl n)
    (hS.gram n) CB (fun j => hCB n t ⟨ht0, htH⟩ j)
  -- exponential smallness
  have hexp : Real.exp (-g * (Sg / ν n - t)) ≤ ν n / (g * (Sg - α)) := by
    have hu : g * (Sg - α) / ν n ≤ g * (Sg / ν n - t) := by
      have h1 : (Sg - α) / ν n ≤ Sg / ν n - t := by
        have : t ≤ α / ν n := ht.2
        rw [sub_div]; linarith
      calc g * (Sg - α) / ν n = g * ((Sg - α) / ν n) := by ring
        _ ≤ g * (Sg / ν n - t) := mul_le_mul_of_nonneg_left h1 hg.le
    have hupos : 0 < g * (Sg - α) / ν n := div_pos hD hv
    have hu2 : g * (Sg / ν n - t) ≤ Real.exp (g * (Sg / ν n - t)) := by
      linarith [Real.add_one_le_exp (g * (Sg / ν n - t))]
    have hnu : -g * (Sg / ν n - t) = -(g * (Sg / ν n - t)) := by ring
    rw [hnu, Real.exp_neg]
    calc (Real.exp (g * (Sg / ν n - t)))⁻¹ ≤ (g * (Sg / ν n - t))⁻¹ :=
          inv_anti₀ (hupos.trans_le hu) hu2
      _ ≤ (g * (Sg - α) / ν n)⁻¹ := inv_anti₀ hupos hu
      _ = ν n / (g * (Sg - α)) := by rw [inv_div]
  refine ContinuousLinearMap.opNorm_le_bound _ (by
    have := norm_nonneg (Fpm true lam κ (ν n) (Sg / ν n) t)
    have : 0 ≤ K2 * (1 / (g * (Sg - α)) + 1) * (1 + 2 * CB ^ 2) := by positivity
    positivity) ?_
  intro y
  obtain ⟨-, h2⟩ := hmain n hn t ht (Pc (pk n) t y)
  obtain ⟨e6, h6⟩ := f6 y
  have hsum : ‖ampN (pk n) lam κ (ν n) t (Pc (pk n) t y) true t‖ +
      ‖ampN (pk n) lam κ (ν n) t (Pc (pk n) t y) false t‖ = 0 := by
    rw [f5 y true, f5 y false]; simp
  rw [hsum, zero_add] at h2
  have hρ0 : 0 ≤ cmpN (pk n) lam κ (ν n) t (Pc (pk n) t y) t :=
    div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hR : cmpN (pk n) lam κ (ν n) t (Pc (pk n) t y) (Sg / ν n) ≤
      K2 * (1 / (g * (Sg - α)) + 1) * (1 + 2 * CB ^ 2) * ν n * ‖y‖ := by
    refine h2.trans ?_
    set ρ := cmpN (pk n) lam κ (ν n) t (Pc (pk n) t y) t with hρ
    have hρy : ρ ≤ (1 + 2 * CB ^ 2) * ‖y‖ := by rw [e6]; exact h6
    have h3 : Real.exp (-g * (Sg / ν n - t)) * ρ + ν n * ρ ≤
        (1 / (g * (Sg - α)) + 1) * ν n * ρ := by
      have : Real.exp (-g * (Sg / ν n - t)) * ρ ≤ ν n / (g * (Sg - α)) * ρ :=
        mul_le_mul_of_nonneg_right hexp hρ0
      have e : ν n / (g * (Sg - α)) * ρ + ν n * ρ = (1 / (g * (Sg - α)) + 1) * ν n * ρ := by
        field_simp
      linarith
    have h4 : (1 / (g * (Sg - α)) + 1) * ν n * ρ ≤
        (1 / (g * (Sg - α)) + 1) * ν n * ((1 + 2 * CB ^ 2) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hρy (by positivity)
    calc K2 * (Real.exp (-g * (Sg / ν n - t)) * ρ + ν n * ρ)
        ≤ K2 * ((1 / (g * (Sg - α)) + 1) * ν n * ((1 + 2 * CB ^ 2) * ‖y‖)) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) hK2
      _ = K2 * (1 / (g * (Sg - α)) + 1) * (1 + 2 * CB ^ 2) * ν n * ‖y‖ := by ring
  have := f2 ((pk n).Uev (Sg / ν n) t (Pc (pk n) t y) |> fun _ => Pc (pk n) t y) (Sg / ν n) hH0
  calc ‖((Pc (pk n) (Sg / ν n)).comp (((pk n).Uev (Sg / ν n) t).comp (Pc (pk n) t))) y‖
      = ‖Pc (pk n) (Sg / ν n) ((pk n).Uev (Sg / ν n) t (Pc (pk n) t y))‖ := rfl
    _ = ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ *
        cmpN (pk n) lam κ (ν n) t (Pc (pk n) t y) (Sg / ν n) := this
    _ ≤ ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ *
        (K2 * (1 / (g * (Sg - α)) + 1) * (1 + 2 * CB ^ 2) * ν n * ‖y‖) :=
        mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    _ = _ := by ring

end ConcreteYF

end UnforcedLeray.Short.PartIIIb
