import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_4_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RadOne.SmoothExtOn
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RadOne.InvIterBound
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RadOne.GaussSqrtComp

/-!
# Part II-b, task `PartII-b:G4/2/2/4/1`: `RadOneDDecay`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: `g₁ = g ∘ √` and `i₁ = (·)⁻¹` are smooth on `(0,∞)`; their globally smooth extensions
`G₁, I₁` (leaf `smoothExtOn`) agree with them on `t > 1/2`. Put `β = G₁ · I₁`. Then `β t = g(√t)/t`
for `t > 1/2`, and Leibniz (`norm_iteratedFDeriv_mul_le`) bounds `β^{(m)}` on `[1,∞)` by the
Gaussian bounds of `(g ∘ √)^{(i)}` (leaf `gaussSqrtComp`) times the uniform bounds of
`(s⁻¹)^{(j)}` (leaf `invIterBound`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem radOneDDecay : UnforcedLeray.Short.IIb.RadOneDDecay := by
  intro g hg hG
  -- smoothness of `g ∘ √` and of `s ↦ s⁻¹` on `(0,∞)`
  have hsq : ContDiffOn ℝ ∞ Real.sqrt (Ioi (0 : ℝ)) := fun x hx =>
    (Real.contDiffAt_sqrt (show (0 : ℝ) < x from hx).ne').contDiffWithinAt
  have hst : MapsTo Real.sqrt (Ioi (0 : ℝ)) (Ioi (0 : ℝ)) := fun x hx =>
    Real.sqrt_pos.mpr (show (0 : ℝ) < x from hx)
  have hg1 : ContDiffOn ℝ ∞ (fun s : ℝ => g (Real.sqrt s)) (Ioi (0 : ℝ)) :=
    hg.comp hsq hst
  have hi1 : ContDiffOn ℝ ∞ (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) (Ioi (0 : ℝ)) := by
    intro x hx
    have hx0 : x ≠ 0 := (show (0 : ℝ) < x from hx).ne'
    have hinv : ContDiffAt ℝ ∞ (Inv.inv : ℝ → ℝ) x := contDiffAt_inv ℝ hx0
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x hinv).contDiffWithinAt
  -- global smooth extensions
  obtain ⟨G1, hG1c, hG1eq⟩ := smoothExtOn (fun s : ℝ => g (Real.sqrt s)) hg1
  obtain ⟨I1, hI1c, hI1eq⟩ := smoothExtOn (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) hi1
  refine ⟨fun t => G1 t * I1 t, hG1c.mul hI1c, ?_, ?_⟩
  · intro t ht
    show G1 t * I1 t = g (Real.sqrt t) / (t : ℂ)
    rw [hG1eq t ht, hI1eq t ht]
    show g (Real.sqrt t) * ((t⁻¹ : ℝ) : ℂ) = g (Real.sqrt t) / (t : ℂ)
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  · intro k
    obtain ⟨C1, κ1, hκ1, hgc⟩ := gaussSqrtComp g hg hG k
    have hInv : ∀ j : ℕ, ∃ D : ℝ, ∀ t : ℝ, 1 ≤ t →
        ‖iteratedDeriv j (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) t‖ ≤ D := invIterBound
    choose Dinv hDinv using hInv
    obtain ⟨D, hD0, hDle⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ k → |Dinv j| ≤ D :=
      ⟨∑ l ∈ Finset.range (k + 1), |Dinv l|, Finset.sum_nonneg (fun l _ => abs_nonneg _),
        fun j hj => Finset.single_le_sum (f := fun l => |Dinv l|) (fun l _ => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))⟩
    have hE1 : ∀ i : ℕ, i ≤ k → ∀ t : ℝ, 1 ≤ t →
        ‖iteratedDeriv i G1 t‖ ≤ C1 * Real.exp (-(κ1 * t)) := by
      intro i hi t ht
      have hfg : G1 =ᶠ[𝓝 t] (fun s : ℝ => g (Real.sqrt s)) := by
        filter_upwards [Ioi_mem_nhds (show (1 / 2 : ℝ) < t by linarith)] with s hs
        exact hG1eq s (show (1 / 2 : ℝ) < s from hs)
      rw [Filter.EventuallyEq.iteratedDeriv_eq i hfg]
      exact hgc i hi t ht
    have hE2 : ∀ j : ℕ, j ≤ k → ∀ t : ℝ, 1 ≤ t → ‖iteratedDeriv j I1 t‖ ≤ D := by
      intro j hj t ht
      have hfg : I1 =ᶠ[𝓝 t] (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) := by
        filter_upwards [Ioi_mem_nhds (show (1 / 2 : ℝ) < t by linarith)] with s hs
        exact hI1eq s (show (1 / 2 : ℝ) < s from hs)
      rw [Filter.EventuallyEq.iteratedDeriv_eq j hfg]
      exact (hDinv j t ht).trans ((le_abs_self _).trans (hDle j hj))
    refine ⟨(2 : ℝ) ^ k * (C1 * D), κ1, hκ1, fun m hmk t ht => ?_⟩
    have hX0 : 0 ≤ C1 * Real.exp (-(κ1 * t)) :=
      (norm_nonneg _).trans (hgc 0 (Nat.zero_le k) t ht)
    have hX : 0 ≤ C1 * Real.exp (-(κ1 * t)) * D := mul_nonneg hX0 hD0
    have hmain := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (n := m) hG1c hI1c t
      (by exact_mod_cast le_top)
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ)]
    refine hmain.trans ?_
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hterm : ∀ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedDeriv i G1 t‖ * ‖iteratedDeriv (m - i) I1 t‖
          ≤ (m.choose i : ℝ) * (C1 * Real.exp (-(κ1 * t)) * D) := by
      intro i hi
      have hi' : i < m + 1 := Finset.mem_range.mp hi
      have h12 : ‖iteratedDeriv i G1 t‖ * ‖iteratedDeriv (m - i) I1 t‖
          ≤ C1 * Real.exp (-(κ1 * t)) * D :=
        mul_le_mul (hE1 i (by omega) t ht) (hE2 (m - i) (by omega) t ht) (norm_nonneg _) hX0
      calc (m.choose i : ℝ) * ‖iteratedDeriv i G1 t‖ * ‖iteratedDeriv (m - i) I1 t‖
          = (m.choose i : ℝ) * (‖iteratedDeriv i G1 t‖ * ‖iteratedDeriv (m - i) I1 t‖) := by ring
        _ ≤ (m.choose i : ℝ) * (C1 * Real.exp (-(κ1 * t)) * D) :=
            mul_le_mul_of_nonneg_left h12 (Nat.cast_nonneg _)
    have hsum : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = (2 : ℝ) ^ m := by
      exact_mod_cast Nat.sum_range_choose m
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, hsum]
    have h2m : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hmk
    have hfin := mul_le_mul_of_nonneg_right h2m hX
    calc (2 : ℝ) ^ m * (C1 * Real.exp (-(κ1 * t)) * D)
        ≤ (2 : ℝ) ^ k * (C1 * Real.exp (-(κ1 * t)) * D) := hfin
      _ = (2 : ℝ) ^ k * (C1 * D) * Real.exp (-(κ1 * t)) := by ring

end
