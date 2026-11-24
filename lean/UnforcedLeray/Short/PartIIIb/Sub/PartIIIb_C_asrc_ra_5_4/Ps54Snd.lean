import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4

/-!
# `PartIII-b:C/asrc/ra/5/4` task 4 : the projection `p ↦ p.2` is in `PS54`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
`p ↦ p.2` is the continuous linear map `L = snd`: it is smooth, its first derivative is the
constant `L` and its derivatives of order at least two vanish.  The norm bound `‖x‖ ≤ 1 + sq2 x`
gives the polynomial bound with `N = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ps54_snd (n : ℕ) : PS54 n (fun p : ℝ × (ℝ × ℝ) => p.2) := by
  set L : ℝ × (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ) with hLdef
  have hfun : (fun p : ℝ × (ℝ × ℝ) => p.2) = ⇑L := rfl
  rw [hfun]
  have key1 : ∀ t : ℝ, ‖t‖ ≤ 1 + t ^ 2 := fun t => by
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 1 / 2)]
  have key2 : ∀ y : ℝ × ℝ, ‖y‖ ≤ 1 + sq2 y := fun y => by
    rw [Prod.norm_def]
    apply max_le
    · have := key1 y.1
      unfold sq2
      nlinarith [sq_nonneg y.2]
    · have := key1 y.2
      unfold sq2
      nlinarith [sq_nonneg y.1]
  refine ⟨L.contDiff.contDiffOn, fun s0 s1 _ _ => ⟨1 + ‖L‖, 1, by positivity, ?_⟩⟩
  intro m _ s _ x
  have hsq : 0 ≤ sq2 x := by unfold sq2; positivity
  obtain rfl | rfl | hm2 : m = 0 ∨ m = 1 ∨ 2 ≤ m := by omega
  · rw [norm_iteratedFDeriv_zero]
    show ‖x‖ ≤ (1 + ‖L‖) * (1 + sq2 x) ^ 1
    rw [pow_one]
    nlinarith [key2 x, norm_nonneg L, hsq]
  · rw [norm_iteratedFDeriv_one]
    rw [ContinuousLinearMap.fderiv]
    rw [pow_one]
    nlinarith [norm_nonneg L, hsq]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 + 1 := ⟨m - 2, by omega⟩
    rw [← norm_iteratedFDeriv_fderiv]
    have hfd : fderiv ℝ (⇑L) = fun _ => L := funext fun y => L.fderiv
    rw [hfd, iteratedFDeriv_const_of_ne (by omega : k + 1 ≠ 0)]
    simp only [Pi.zero_apply, norm_zero]
    have : (0 : ℝ) ≤ (1 + ‖L‖) * (1 + sq2 x) ^ 1 := by
      rw [pow_one]; nlinarith [norm_nonneg L, hsq]
    exact this

end UnforcedLeray.Short.PartIIIb.Concrete
