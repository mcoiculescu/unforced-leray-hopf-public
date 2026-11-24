import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip.ForwardUniq.Props

/-!
# `FUAeOfIntervals` (item `PartIII-b:C/near/delta/9/1/8`)

A nonnegative locally integrable `E` with `∫_ε^{t₁} E = 0` for all `0 < ε < t₁ < T` vanishes
a.e. on `(0,T)`.  Source 3541-3545 (uniqueness on `[δ_j, B]`).

The intervals `[c_n, T - c_n]` with `c_n = T/(n+3)` have `c_n < T - c_n < T`, and their
interiors (as open sets) cover `(0,T)`: for `s ∈ (0,T)` pick `n` with `T/(n+3) < min(s, T-s)`.
Each integral vanishes, so `E = 0` a.e. on each interior (`integral_eq_zero_iff_of_nonneg`),
and a countable union gives the claim (`ae_restrict_iUnion_iff`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem fuAeOfIntervals : UnforcedLeray.Short.PartIIIb.NearInst.Delta.FUAeOfIntervals := by
  intro T E hT hE hEi hI
  have hE' : (0 : ℝ → ℝ) ≤ E := fun s => hE s
  have key : ∀ n : ℕ, ∀ᵐ s ∂(volume.restrict
      (Ioo (T / ((n : ℝ) + 3)) (T - T / ((n : ℝ) + 3)))), E s = 0 := by
    intro n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h3 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
    have hc0 : 0 < T / ((n : ℝ) + 3) := div_pos hT h3
    have hcdef : T / ((n : ℝ) + 3) * ((n : ℝ) + 3) = T := div_mul_cancel₀ T (ne_of_gt h3)
    set c := T / ((n : ℝ) + 3) with hc
    have h2c : 2 * c < T := by nlinarith
    have hab : c < T - c := by linarith
    have hbT : T - c < T := by linarith
    have hI' := hI c (T - c) hc0 hab hbT
    have hint : IntegrableOn E (Icc c (T - c)) := hEi c (T - c) hc0 hab
    have h0 := (integral_eq_zero_iff_of_nonneg hE' hint).1 hI'
    exact ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self h0
  have hsub : Ioo (0 : ℝ) T ⊆ ⋃ n : ℕ, Ioo (T / ((n : ℝ) + 3)) (T - T / ((n : ℝ) + 3)) := by
    intro s hs
    have hm : 0 < min s (T - s) := lt_min hs.1 (by linarith [hs.2])
    obtain ⟨n, hn⟩ := exists_nat_gt (T / min s (T - s))
    have h1 : T < (n : ℝ) * min s (T - s) := (div_lt_iff₀ hm).1 hn
    have h3 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
    have h4 : T / ((n : ℝ) + 3) < min s (T - s) := by
      rw [div_lt_iff₀ h3]
      nlinarith
    have h5 := min_le_left s (T - s)
    have h6 := min_le_right s (T - s)
    refine Set.mem_iUnion.2 ⟨n, ?_, ?_⟩
    · linarith
    · linarith
  have hU : ∀ᵐ s ∂(volume.restrict
      (⋃ n : ℕ, Ioo (T / ((n : ℝ) + 3)) (T - T / ((n : ℝ) + 3)))), E s = 0 :=
    (ae_restrict_iUnion_iff (fun n : ℕ => Ioo (T / ((n : ℝ) + 3)) (T - T / ((n : ℝ) + 3)))
      (fun s => E s = 0)).2 key
  exact ae_restrict_of_ae_restrict_of_subset hsub hU

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
