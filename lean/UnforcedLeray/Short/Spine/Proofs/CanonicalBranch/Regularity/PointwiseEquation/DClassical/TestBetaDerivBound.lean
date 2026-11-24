import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5_3

/-!
# Leaf 2 proof: the Gaussian derivative bound for a compactly supported `β`

Proves `UnforcedLeray.Short.Spine.TestBetaDerivBound` (`Sub/SP_CAN4_5_3.lean`) with order bound
`N = 0` and weight constant `C = M · e^{|B|/4}`, where `M` bounds `iteratedDeriv m β` on `[A, B]`.

Source of record: `the November 2 reference manuscript` lines 1086 and 1134-1140.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b
open UnforcedLeray.Short.Spine.DClassicalAux

theorem testBetaDerivBound_proof : UnforcedLeray.Short.Spine.TestBetaDerivBound := by
  intro β hβ A B hA hB
  intro k
  intro m _
  -- (a) the derivative of order m is continuous
  have hg : Continuous (iteratedDeriv m β) :=
    hβ.continuous_iteratedDeriv m (natCast_le_infty m)
  -- (b) it vanishes off [A, B]
  have hzl : ∀ s : ℝ, s < A → iteratedDeriv m β s = 0 := by
    intro s hs
    have hev : β =ᶠ[𝓝 s] (fun _ => (0 : ℂ)) :=
      Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hs))
        (by intro x hx; exact hA x (Set.mem_Iio.mp hx))
    rw [hev.iteratedDeriv_eq m, iteratedDeriv_const]
    simp
  have hzr : ∀ s : ℝ, B < s → iteratedDeriv m β s = 0 := by
    intro s hs
    have hev : β =ᶠ[𝓝 s] (fun _ => (0 : ℂ)) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hs))
        (by intro x hx; exact hB x (Set.mem_Ioi.mp hx))
    rw [hev.iteratedDeriv_eq m, iteratedDeriv_const]
    simp
  -- (c) a bound M on [A, B]
  have hK : IsCompact (Icc A B) := isCompact_Icc
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ Icc A B, ‖iteratedDeriv m β x‖ ≤ M :=
    hK.exists_bound_of_continuousOn hg.continuousOn
  have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right M 0
  -- (d) the weight Gaussian exp(-s/4) with N = 0 and C = max M 0 * exp(|B|/4)
  refine ⟨max M 0 * Real.exp (|B| / 4), 0, mul_nonneg hM0 (Real.exp_pos _).le, fun s _ => ?_⟩
  simp only [pow_zero, mul_one]
  by_cases hs : s ∈ Icc A B
  · have hbound : ‖iteratedDeriv m β s‖ ≤ max M 0 := (hM s hs).trans (le_max_left M 0)
    have key : (1 : ℝ) ≤ Real.exp (|B| / 4) * Real.exp ((-1 / 4) * s) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have h1 := le_abs_self B
      have h2 := (Set.mem_Icc.mp hs).2
      linarith
    calc ‖iteratedDeriv m β s‖ ≤ max M 0 := hbound
      _ ≤ max M 0 * (Real.exp (|B| / 4) * Real.exp ((-1 / 4) * s)) :=
          le_mul_of_one_le_right hM0 key
      _ = max M 0 * Real.exp (|B| / 4) * Real.exp ((-1 / 4) * s) := by ring
  · have hz : iteratedDeriv m β s = 0 := by
      rcases lt_or_ge s A with h1 | h1
      · exact hzl s h1
      · have h2 : B < s := by
          by_contra h2
          exact hs (Set.mem_Icc.mpr ⟨h1, not_lt.mp h2⟩)
        exact hzr s h2
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg hM0 (Real.exp_pos _).le) (Real.exp_pos _).le

end UnforcedLeray.Short.Spine
