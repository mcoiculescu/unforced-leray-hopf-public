import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift

/-!
# `PartII-b:T10/6/3/1/1a`: smoothness of the `q`-periodization

`perCoord c φ` is, near each point, a finite sum of smooth translates of a coordinate test `φ`,
since the `q`-coordinates of `tsupport φ` are bounded.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.ChartLift

theorem perSmooth_proof : UnforcedLeray.Short.IIb.ChartLift.PerSmooth := by
  intro c φ hc hφ
  have hc0 : c ≠ 0 := hc.ne'
  -- the `q`-coordinates of the support are bounded
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, ∀ y : Coord, φ y ≠ 0 → |y.2.1| ≤ Q := by
    obtain ⟨Q, hQ⟩ :=
      ((hφ.compact.image (continuous_fst.comp continuous_snd)).isBounded).exists_norm_le
    refine ⟨Q, fun y hy => ?_⟩
    have hy' : y ∈ tsupport φ := subset_tsupport φ hy
    have h := hQ (y.2.1) ⟨y, hy', rfl⟩
    rw [Real.norm_eq_abs] at h
    exact h
  rw [contDiff_iff_contDiffAt]
  intro x0
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |x0.2.1| + 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈(Q + M) / c⌉₊ := ⟨_, rfl⟩
  have hNc : Q + M ≤ (N : ℝ) * c := by
    have h1 : (Q + M) / c ≤ (N : ℝ) := by
      rw [hN]
      exact Nat.le_ceil _
    have h2 : (Q + M) / c * c = Q + M := by field_simp
    have h3 := mul_le_mul_of_nonneg_right h1 hc.le
    linarith
  have hopen : IsOpen {x : Coord | |x.2.1| < M} :=
    isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_snd)) continuous_const
  have hmem : {x : Coord | |x.2.1| < M} ∈ 𝓝 x0 := by
    apply hopen.mem_nhds
    show |x0.2.1| < M
    rw [hM]
    linarith
  have hfin : perCoord c φ =ᶠ[𝓝 x0]
      fun x => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), φ (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) := by
    filter_upwards [hmem] with x hx
    have hx' : |x.2.1| < M := hx
    have hlo : -M < x.2.1 := by linarith [neg_abs_le x.2.1]
    have hhi : x.2.1 < M := by linarith [le_abs_self x.2.1]
    unfold perCoord
    rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ))]
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_contra hne
    have hb : |x.2.1 + (k : ℝ) * c| ≤ Q := hQ _ hne
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    rcases (show k < -(N : ℤ) ∨ (N : ℤ) < k by omega) with h | h
    · have h1 : (k : ℝ) ≤ -(N : ℝ) - 1 := by
        have : k ≤ -(N : ℤ) - 1 := by omega
        exact_mod_cast this
      have h2 : (k : ℝ) * c ≤ (-(N : ℝ) - 1) * c := mul_le_mul_of_nonneg_right h1 hc.le
      have h3 : (-(N : ℝ) - 1) * c = -((N : ℝ) * c) - c := by ring
      linarith
    · have h1 : (N : ℝ) + 1 ≤ (k : ℝ) := by
        have : (N : ℤ) + 1 ≤ k := by omega
        exact_mod_cast this
      have h2 : ((N : ℝ) + 1) * c ≤ (k : ℝ) * c := mul_le_mul_of_nonneg_right h1 hc.le
      have h3 : ((N : ℝ) + 1) * c = (N : ℝ) * c + c := by ring
      linarith
  have hsm : ContDiff ℝ ∞ (fun x : Coord =>
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), φ (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) := by
    refine ContDiff.sum (f := fun (k : ℤ) (x : Coord) => φ (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) ?_
    intro k _
    have hA : ContDiff ℝ ∞ (fun x : Coord => (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))) := by
      fun_prop
    exact hφ.smooth.comp hA
  exact hsm.contDiffAt.congr_of_eventuallyEq hfin

end UnforcedLeray.Short.IIb.ChartLift
