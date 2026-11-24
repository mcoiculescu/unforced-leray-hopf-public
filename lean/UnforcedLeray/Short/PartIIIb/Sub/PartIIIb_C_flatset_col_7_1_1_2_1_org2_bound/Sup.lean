import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bound

/-!
# `DuhamelSupBound`: sup bound of the Duhamel integral on a slice `s > 0`

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The planar heat of a uniformly bounded function is uniformly bounded (Gaussian probability
density, `B0224.planeHeat_of_pos`; the identity for `θ ≤ 0`). -/
theorem norm_planeHeat_le_of_bound {θ M : ℝ} (u : ℝ × ℝ → ℂ) (hu : ∀ z, ‖u z‖ ≤ M)
    (x : ℝ × ℝ) :
    ‖UnforcedLeray.B0224.planeHeat θ u x‖ ≤ M := by
  by_cases hθ : 0 < θ
  · rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
    have hint := UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ
    calc ‖∫ y : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y)‖
        ≤ ∫ y : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ y * M := by
          apply MeasureTheory.norm_integral_le_of_norm_le (hint.mul_const M)
          refine Filter.Eventually.of_forall (fun y => ?_)
          rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)]
          exact mul_le_mul_of_nonneg_left (hu _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)
      _ = M := by
          rw [integral_mul_const, UnforcedLeray.Gaussian.integral_gaussKernel hθ, one_mul]
  · rw [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]
    exact hu x

/-- The cpow factor `(σ/s)^μ` on `s₀ ≤ σ ≤ s`, uniformly bounded. -/
theorem cpow_ratio_bound {s s0 μ σ : ℝ} (hs0 : 0 < s0) (hσ0 : 0 < σ) (hσs : σ ≤ s)
    (hσ0' : s0 ≤ σ) (hs : 0 < s) :
    ‖((σ / s : ℝ) : ℂ) ^ (μ : ℂ)‖ ≤ Real.exp (|Real.log (s0 / s)| * |μ|) := by
  have ht : 0 < σ / s := div_pos hσ0 hs
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp only [Complex.ofReal_re]
  rw [Real.rpow_def_of_pos ht]
  apply Real.exp_le_exp.2
  have hup : Real.log (σ / s) ≤ 0 := Real.log_nonpos ht.le ((div_le_one hs).2 hσs)
  have hratio : s0 / s ≤ σ / s := by gcongr
  have hlow : Real.log (s0 / s) ≤ Real.log (σ / s) :=
    Real.log_le_log (div_pos hs0 hs) hratio
  have hlt : |Real.log (σ / s)| ≤ |Real.log (s0 / s)| :=
    abs_le.2 ⟨le_trans (neg_abs_le _) hlow, le_trans hup (abs_nonneg _)⟩
  calc Real.log (σ / s) * μ ≤ |Real.log (σ / s) * μ| := le_abs_self _
    _ = |Real.log (σ / s)| * |μ| := abs_mul _ _
    _ ≤ |Real.log (s0 / s)| * |μ| := mul_le_mul_of_nonneg_right hlt (abs_nonneg _)

theorem duhamelSupBound : DuhamelSupBound := by
  intro c ν μ G hG hν s hs
  have hb : ∀ i : Fin 2, ∃ C : ℝ, ∀ p : Chart, ‖G p i‖ ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := hG.2.2.2 i 0
    exact ⟨C, fun p => by simpa [norm_iteratedFDeriv_zero] using hC p⟩
  choose Cb hCb using hb
  set M : ℝ := |Cb 0| + |Cb 1| with hMdef
  have hM0 : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hle : ∀ i : Fin 2, Cb i ≤ M :=
    Fin.forall_fin_two.2 ⟨by linarith [abs_nonneg (Cb 1), le_abs_self (Cb 0)],
      by linarith [abs_nonneg (Cb 0), le_abs_self (Cb 1)]⟩
  have hGM : ∀ (i : Fin 2) (p : Chart), ‖G p i‖ ≤ M := fun i p => (hCb i p).trans (hle i)
  obtain ⟨s0, s1, hs0, hsupp⟩ := hG.2.2.1
  have hK0 : 0 ≤ Real.exp (|Real.log (s0 / s)| * |μ|) := (Real.exp_pos _).le
  have hpt : ∀ (x : ℝ × ℝ) (i : Fin 2) (σ : ℝ), σ ∈ Ioc 0 s →
      ‖(((σ / s : ℝ) : ℂ) ^ (μ : ℂ)) •
          UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) x‖
        ≤ Real.exp (|Real.log (s0 / s)| * |μ|) * M := by
    intro x i σ hσ
    obtain ⟨hσ0, hσs⟩ := hσ
    rw [norm_smul]
    by_cases hlt : σ < s0
    · have hz : ∀ z, G (σ, z) = 0 := by
        intro z
        by_contra hne
        have h1 : s0 ≤ (σ, z).1 := (hsupp (σ, z) hne).1
        exact absurd h1 (not_le.2 hlt)
      have hu : ∀ z, ‖((G (σ, z) i : ℝ) : ℂ)‖ ≤ 0 := fun z => by
        rw [hz z]
        simp
      have h0 : ‖UnforcedLeray.B0224.planeHeat (ν * (s - σ))
          (fun z => ((G (σ, z) i : ℝ) : ℂ)) x‖ = 0 :=
        le_antisymm (norm_planeHeat_le_of_bound (θ := ν * (s - σ))
          (fun z => ((G (σ, z) i : ℝ) : ℂ)) hu x) (norm_nonneg _)
      rw [h0, mul_zero]
      exact mul_nonneg hK0 hM0
    · have hlt' : s0 ≤ σ := not_lt.1 hlt
      have hu : ∀ z, ‖((G (σ, z) i : ℝ) : ℂ)‖ ≤ M := fun z => by
        rw [Complex.norm_real]
        exact hGM i (σ, z)
      have hH := norm_planeHeat_le_of_bound (θ := ν * (s - σ))
        (fun z => ((G (σ, z) i : ℝ) : ℂ)) hu x
      have ha := cpow_ratio_bound (μ := μ) hs0 hσ0 hσs hlt' hs
      exact mul_le_mul ha hH (norm_nonneg _) hK0
  refine ⟨Real.exp (|Real.log (s0 / s)| * |μ|) * M * |s - 0|, fun x i => ?_⟩
  dsimp only [duhamel]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  rw [Set.uIoc_of_le hs.le] at hσ
  exact hpt x i σ hσ

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
