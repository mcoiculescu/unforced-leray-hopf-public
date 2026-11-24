import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2_2

/-!
# `LimitContDiff` (source 1684-1689): limit of `C^m` maps with uniformly Cauchy derivatives

Source `the November 2 reference manuscript`
1650-1656, 1684-1689. Induction on `m`, generalised over the target normed space.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

theorem limitContDiff_zero_diff {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g h : Plane → F) (x : Plane) :
    ‖iteratedFDeriv ℝ 0 g x - iteratedFDeriv ℝ 0 h x‖ = ‖g x - h x‖ := by
  have e : iteratedFDeriv ℝ 0 g x - iteratedFDeriv ℝ 0 h x
      = (continuousMultilinearCurryFin0 ℝ Plane F).symm (g x - h x) := by
    rw [map_sub]; rfl
  rw [e, LinearIsometryEquiv.norm_map]

theorem limitContDiff_pointwise {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (u : ℕ → Plane → F)
    (H : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n p, N ≤ n → N ≤ p → ∀ x : Plane,
      ‖u n x - u p x‖ < ε) :
    ∃ z : Plane → F, ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (z x)) := by
  have hex : ∀ x, ∃ l : F, Tendsto (fun n => u n x) atTop (𝓝 l) := by
    intro x
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := H ε hε
    exact ⟨N, fun m hm n hn => by rw [dist_eq_norm]; exact hN m n hm hn x⟩
  choose z hz using hex
  exact ⟨z, hz⟩

theorem limitContDiff_unif {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℕ → Plane → F) (z : Plane → F)
    (hz : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (z x)))
    (H : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n p, N ≤ n → N ≤ p → ∀ x : Plane,
      ‖u n x - u p x‖ < ε) :
    TendstoUniformly u z atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := H (ε / 2) (by positivity)
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn x => ?_⟩
  have hlim : Tendsto (fun p => ‖u n x - u p x‖) atTop (𝓝 ‖u n x - z x‖) :=
    ((tendsto_const_nhds (x := u n x)).sub (hz x)).norm
  have hle : ‖u n x - z x‖ ≤ ε / 2 :=
    le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨N, fun p hp => (hN n p hn hp x).le⟩)
  rw [dist_eq_norm, norm_sub_rev]
  linarith

theorem limitContDiff_aux (m : ℕ) : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (u : ℕ → Plane → F), (∀ n, ContDiff ℝ m (u n)) →
    (∀ j : ℕ, j ≤ m → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n p, N ≤ n → N ≤ p → ∀ x : Plane,
      ‖iteratedFDeriv ℝ j (u n) x - iteratedFDeriv ℝ j (u p) x‖ < ε) →
    ∃ z : Plane → F, ContDiff ℝ m z ∧ ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (z x)) := by
  induction m with
  | zero =>
    intro F _ _ _ u hu hyp
    have H0 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n p, N ≤ n → N ≤ p → ∀ x : Plane,
        ‖u n x - u p x‖ < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hyp 0 (Nat.zero_le _) ε hε
      refine ⟨N, fun n p hn hp x => ?_⟩
      have := hN n p hn hp x
      rwa [limitContDiff_zero_diff] at this
    obtain ⟨z, hz⟩ := limitContDiff_pointwise u H0
    refine ⟨z, ?_, hz⟩
    have hU := limitContDiff_unif u z hz H0
    have hc : ∀ n, Continuous (u n) := fun n => by
      have h0 := hu n
      rw [Nat.cast_zero] at h0
      exact contDiff_zero.mp h0
    rw [Nat.cast_zero, contDiff_zero]
    exact hU.continuous (Filter.Eventually.frequently (Filter.Eventually.of_forall hc))
  | succ m ih =>
    intro F _ _ _ u hu hyp
    have hdu : ∀ n, ContDiff ℝ m (fun x => fderiv ℝ (u n) x) := fun n =>
      ContDiff.fderiv_right (hu n) (by norm_cast)
    have hyp' : ∀ j : ℕ, j ≤ m → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n p, N ≤ n → N ≤ p →
        ∀ x : Plane, ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (u n) y) x
          - iteratedFDeriv ℝ j (fun y => fderiv ℝ (u p) y) x‖ < ε := by
      intro j hj ε hε
      obtain ⟨N, hN⟩ := hyp (j + 1) (by omega) ε hε
      refine ⟨N, fun n p hn hp x => ?_⟩
      have key : ∀ q : ℕ, iteratedFDeriv ℝ j.succ (u q) x
          = (continuousMultilinearCurryRightEquiv' ℝ j Plane F).symm
              (iteratedFDeriv ℝ j (fun y => fderiv ℝ (u q) y) x) := fun q =>
        iteratedFDeriv_succ_eq_comp_right
      have hsub : ∀ a b : (Plane [×j]→L[ℝ] Plane →L[ℝ] F),
          (continuousMultilinearCurryRightEquiv' ℝ j Plane F).symm a
            - (continuousMultilinearCurryRightEquiv' ℝ j Plane F).symm b
          = (continuousMultilinearCurryRightEquiv' ℝ j Plane F).symm (a - b) := fun a b =>
        (LinearMap.map_sub
          (continuousMultilinearCurryRightEquiv' ℝ j Plane F).symm.toLinearEquiv.toLinearMap a b).symm
      have h1 : ‖iteratedFDeriv ℝ j.succ (u n) x - iteratedFDeriv ℝ j.succ (u p) x‖ < ε :=
        hN n p hn hp x
      rw [key n, key p, hsub, LinearIsometryEquiv.norm_map] at h1
      exact h1
    obtain ⟨w, hw, hwl⟩ := ih (Plane →L[ℝ] F) (fun n y => fderiv ℝ (u n) y) hdu hyp'
    have H0 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n p, N ≤ n → N ≤ p → ∀ x : Plane,
        ‖u n x - u p x‖ < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hyp 0 (Nat.zero_le _) ε hε
      refine ⟨N, fun n p hn hp x => ?_⟩
      have := hN n p hn hp x
      rwa [limitContDiff_zero_diff] at this
    have Hv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n p, N ≤ n → N ≤ p → ∀ x : Plane,
        ‖fderiv ℝ (u n) x - fderiv ℝ (u p) x‖ < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hyp' 0 (Nat.zero_le _) ε hε
      refine ⟨N, fun n p hn hp x => ?_⟩
      have := hN n p hn hp x
      rwa [limitContDiff_zero_diff] at this
    obtain ⟨z, hz⟩ := limitContDiff_pointwise u H0
    have hwU : TendstoUniformly (fun n y => fderiv ℝ (u n) y) w atTop :=
      limitContDiff_unif (fun n y => fderiv ℝ (u n) y) w hwl Hv
    have hu_fd : ∀ n x, HasFDerivAt (u n) (fderiv ℝ (u n) x) x := fun n x =>
      ((hu n).differentiable (by norm_cast)).differentiableAt.hasFDerivAt
    have hzD : ∀ x, HasFDerivAt z (w x) x := fun x =>
      hasFDerivAt_of_tendstoUniformly hwU hu_fd hz x
    refine ⟨z, ?_, hz⟩
    rw [Nat.cast_succ]
    exact contDiff_succ_iff_hasFDerivAt.mpr ⟨w, hw, hzD⟩

theorem limitContDiff_proof : LimitContDiff := by
  intro m u hu hyp
  exact limitContDiff_aux m Vec2 u hu hyp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
