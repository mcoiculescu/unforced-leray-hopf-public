import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_1

/-!
# Part II-b, task `PartII-b:G4/2/2/1/2`: `PolyZpow`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: `r ↦ (r : ℂ)^m` is smooth on `(0,∞)` (natural powers, and inverses of nonvanishing natural
powers). Its `j`-th derivative on `(0,∞)` is `c_j · r^(m-j)` with `c_j : ℂ` (induction on `j`,
`hasDerivAt_zpow` composed with `ofReal`). On `[1,∞)`, `r^(m-j) ≤ r^(natAbs (m-j))`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem polyZpow : UnforcedLeray.Short.IIb.PolyZpow := by
  -- smoothness of `r ↦ (r : ℂ)^k` on `(0,∞)`
  have hS : ∀ k : ℤ, ContDiffOn ℝ ∞ (fun s : ℝ => (s : ℂ) ^ k) (Ioi 0) := by
    intro k r hr
    have hr0 : (0 : ℝ) < r := hr
    have hofR : ContDiff ℝ ∞ (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
    obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
    · subst hn
      have hf : (fun s : ℝ => (s : ℂ) ^ ((n : ℕ) : ℤ)) = fun s : ℝ => (s : ℂ) ^ n := by
        funext s
        rw [zpow_natCast]
      rw [hf]
      exact ((hofR.pow n).contDiffAt).contDiffWithinAt
    · subst hn
      have hf : (fun s : ℝ => (s : ℂ) ^ (-(n : ℤ))) = fun s : ℝ => ((s : ℂ) ^ n)⁻¹ := by
        funext s
        rw [zpow_neg, zpow_natCast]
      rw [hf]
      have hne : (r : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr0.ne')
      exact (((hofR.pow n).contDiffAt).inv hne).contDiffWithinAt
  -- derivatives on `(0,∞)`: `iteratedDeriv j (r^k) = c * r^(k - j)`
  have hI : ∀ (k : ℤ) (j : ℕ), ∃ c : ℂ, ∀ r : ℝ, 0 < r →
      iteratedDeriv j (fun s : ℝ => (s : ℂ) ^ k) r = c * (r : ℂ) ^ (k - (j : ℤ)) := by
    intro k j
    induction j with
    | zero =>
      refine ⟨1, fun r hr => ?_⟩
      simp
    | succ j ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c * ((k - (j : ℤ) : ℤ) : ℂ), fun r hr => ?_⟩
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (fun s : ℝ => (s : ℂ) ^ k) =ᶠ[𝓝 r]
          fun s : ℝ => c * (s : ℂ) ^ (k - (j : ℤ)) := by
        filter_upwards [Ioi_mem_nhds hr] with s hs
        exact hc s hs
      rw [hev.deriv_eq]
      have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have hd : HasDerivAt (fun s : ℝ => c * (s : ℂ) ^ (k - (j : ℤ)))
          (c * ((((k - (j : ℤ) : ℤ)) : ℂ) * (r : ℂ) ^ ((k - (j : ℤ)) - 1))) r :=
        ((hasDerivAt_zpow (k - (j : ℤ)) (r : ℂ) (Or.inl hr')).comp_ofReal).const_mul c
      rw [hd.deriv, mul_assoc]
      rw [show k - ((j + 1 : ℕ) : ℤ) = k - (j : ℤ) - 1 by push_cast; ring]
  refine fun m => ⟨hS m, fun j => ?_⟩
  obtain ⟨c, hc⟩ := hI m j
  refine ⟨‖c‖, (m - (j : ℤ)).natAbs, fun r hr1 => ?_⟩
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have hn : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hle : r ^ (m - (j : ℤ)) ≤ r ^ (m - (j : ℤ)).natAbs := by
    have h := zpow_le_zpow_right₀ hr1 (Int.le_natAbs (a := m - (j : ℤ)))
    rwa [zpow_natCast] at h
  rw [hc r hr0, norm_mul, norm_zpow, hn]
  exact mul_le_mul_of_nonneg_left hle (norm_nonneg c)

end UnforcedLeray.Short.IIb
