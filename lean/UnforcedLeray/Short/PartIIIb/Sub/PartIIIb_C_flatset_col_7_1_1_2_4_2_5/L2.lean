import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_5

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (tnorm2)

theorem tnorm2_sq_eq' (T : Fin 2 → Fin 2 → ℂ) : tnorm2 T ^ 2 = ∑ i, ∑ j, ‖T i j‖ ^ 2 := by
  unfold tnorm2
  rw [Real.sq_sqrt (by positivity)]

theorem tnorm2_row0_sq' (g : Fin 2 → ℂ) :
    tnorm2 (fun i j => g j * (if i = 0 then 1 else 0)) ^ 2 = ∑ j, ‖g j‖ ^ 2 := by
  rw [tnorm2_sq_eq']
  simp [Fin.sum_univ_two]

theorem periodize_slice_eq' {c σ : ℝ} {Gs : UnforcedLeray.B0220.Profile →
      UnforcedLeray.B0223.MeridC}
    (hper : ∀ q η, Gs (σ, (q + c, η)) = Gs (σ, (q, η))) (z : ℝ × ℝ) :
    UnforcedLeray.B0220.periodize c Gs (σ, z) = Gs (σ, z) := by
  obtain ⟨q, η⟩ := z
  have key : ∀ m : ℤ, Gs (σ, (q + m * c, η)) = Gs (σ, (q, η)) := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ k ih =>
        have h := hper (q + k * c) η
        push_cast at ih ⊢
        rw [show q + ((k : ℝ) + 1) * c = q + k * c + c by ring, h, ih]
    | pred k ih =>
        have h := hper (q + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c) η
        have e : q + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c + c = q + ((-(k : ℤ) : ℤ) : ℝ) * c := by
          push_cast; ring
        rw [e] at h
        rw [← h]
        exact ih
  obtain ⟨m, hm⟩ : ∃ m : ℤ, UnforcedLeray.B0220.reduceIoc c q = q + m * c :=
    ⟨-((⌈q / c⌉ : ℤ) - 1), by unfold UnforcedLeray.B0220.reduceIoc; push_cast; ring⟩
  unfold UnforcedLeray.B0220.periodize
  rw [hm, key m]

theorem planeHeat_apply_comp' {θ : ℝ} (hθ : 0 < θ) {u : ℝ × ℝ → UnforcedLeray.B0223.MeridC}
    (hu : Continuous u) {C : ℝ} (hC : ∀ z, ‖u z‖ ≤ C) (i : Fin 2) (x : ℝ × ℝ) :
    UnforcedLeray.B0224.planeHeat θ u x i =
      UnforcedLeray.B0224.planeHeat θ (fun z => u z i) x := by
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ, UnforcedLeray.B0224.planeHeat_of_pos hθ]
  have hmeas : AEStronglyMeasurable
      (fun y : UnforcedLeray.Gaussian.Euc 2 => u (x - UnforcedLeray.B0224.planeι y)) volume :=
    (hu.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι)).aestronglyMeasurable
  have hbdd : MemLp (fun y : UnforcedLeray.Gaussian.Euc 2 => u (x - UnforcedLeray.B0224.planeι y))
      ⊤ volume :=
    memLp_top_of_bound hmeas C (Eventually.of_forall fun y => hC _)
  have hint : Integrable (fun y : UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y)) volume :=
    (UnforcedLeray.Gaussian.integrable_gaussKernel hθ).smul_of_top_left hbdd
  let L : UnforcedLeray.B0223.MeridC →L[ℝ] ℂ :=
    (EuclideanSpace.proj i : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ).restrictScalars ℝ
  have h := L.integral_comp_comm hint
  calc (∫ y : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y)) i
      = L (∫ y : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y)) := rfl
    _ = ∫ y : UnforcedLeray.Gaussian.Euc 2,
          L (UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y)) :=
        h.symm
    _ = ∫ y : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 θ y •
            (fun z => u z i) (x - UnforcedLeray.B0224.planeι y) := by
        congr 1

theorem sliceHeat_bound : SliceHeatP := by
  intro hH c ν σ s C hc Gs hν hlt hsm hper hbd hen
  have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hlt)
  have hcont : Continuous (fun z : ℝ × ℝ => Gs (σ, z)) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (hsm i).continuous)
  obtain ⟨C', hC'⟩ := hbd
  have hcomp : ∀ i : Fin 2, ∀ z : ℝ × ℝ, ‖Gs (σ, z) i‖ ≤ C' := fun i z =>
    (PiLp.norm_apply_le _ i).trans (hC' z)
  have hmA : ∀ F : ℝ × ℝ → ℂ, Measurable (fun x : ℝ × ℝ =>
      ∑ j : Fin 2, ‖fderiv ℝ F x (UnforcedLeray.B0579.dir j)‖ ^ 2) := fun F =>
    Finset.measurable_sum _ fun j _ =>
      ((measurable_fderiv_apply_const ℝ F (UnforcedLeray.B0579.dir j)).norm).pow_const 2
  have hrow : ∀ i : Fin 2,
      ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (∑ j : Fin 2,
          ‖fderiv ℝ (UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => Gs (σ, z) i)) x
            (UnforcedLeray.B0579.dir j)‖ ^ 2)
      ≤ ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (∑ j : Fin 2, ‖fderiv ℝ (fun y : ℝ × ℝ => Gs (σ, y) i) x
          (UnforcedLeray.B0579.dir j)‖ ^ 2) := by
    intro i
    have h := hH c (ν * (s - σ)) hc hθ.le (fun y : ℝ × ℝ => Gs (σ, y) i) (hsm i)
      (fun q η => by simp only [hper q η]) ⟨C', fun y => hcomp i y⟩
    simpa only [tnorm2_row0_sq'] using h
  have hfd : ∀ i : Fin 2, (fun y : ℝ × ℝ => UnforcedLeray.B0224.planeHeat (ν * (s - σ))
      (fun z => Gs (σ, z)) y i) =
      UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => Gs (σ, z) i) := fun i =>
    funext fun y => planeHeat_apply_comp' hθ hcont hC' i y
  simp only [periodize_slice_eq' hper, hfd]
  calc ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (tnorm2 (fun i j => fderiv ℝ
          (UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => Gs (σ, z) i)) x
          (UnforcedLeray.B0579.dir j)) ^ 2)
      = ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ), ∑ i : Fin 2,
        ENNReal.ofReal (∑ j : Fin 2, ‖fderiv ℝ
          (UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => Gs (σ, z) i)) x
          (UnforcedLeray.B0579.dir j)‖ ^ 2) := by
        refine lintegral_congr fun x => ?_
        rw [tnorm2_sq_eq', ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    _ = ∑ i : Fin 2, ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (∑ j : Fin 2, ‖fderiv ℝ
          (UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => Gs (σ, z) i)) x
          (UnforcedLeray.B0579.dir j)‖ ^ 2) :=
        lintegral_finsetSum _ fun i _ => ENNReal.measurable_ofReal.comp (hmA _)
    _ ≤ ∑ i : Fin 2, ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (∑ j : Fin 2, ‖fderiv ℝ (fun y : ℝ × ℝ => Gs (σ, y) i) x
          (UnforcedLeray.B0579.dir j)‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ), ∑ i : Fin 2,
        ENNReal.ofReal (∑ j : Fin 2, ‖fderiv ℝ (fun y : ℝ × ℝ => Gs (σ, y) i) x
          (UnforcedLeray.B0579.dir j)‖ ^ 2) :=
        (lintegral_finsetSum _ fun i _ => ENNReal.measurable_ofReal.comp (hmA _)).symm
    _ = ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (tnorm2 (fun i j => fderiv ℝ (fun y : ℝ × ℝ => (Gs (σ, y)) i) x
          (UnforcedLeray.B0579.dir j)) ^ 2) := by
        refine lintegral_congr fun x => ?_
        rw [tnorm2_sq_eq', ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    _ ≤ ENNReal.ofReal C := hen

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
