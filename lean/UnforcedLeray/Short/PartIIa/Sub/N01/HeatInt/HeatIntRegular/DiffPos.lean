import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_3
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular.DiffPos.Basic

/-!
# `PartII-a:N01/9/1/2/4/3/5` (heat integral): `HeatIntDiffPos`

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430. For `s > 0` the component `y ↦ smoothHeatInt (s,y) i`
is differentiable: the `σ`-integral over `(0, s)` is differentiated under the integral sign
(`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`), with the Gaussian average and
the slice bounds of `DiffPos/Basic.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)

set_option maxHeartbeats 1000000 in
theorem dp_main {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) (μ : ℂ) {F : Profile → MeridC}
    (hF : IsSmoothForceFn c F) {s : ℝ} (hs : 0 < s) (y0 : ℝ × ℝ) :
    HasFDerivAt (fun y : ℝ × ℝ => ∫ σ in (0:ℝ)..s, dpF c ν s μ F σ y)
      (∫ σ in (0:ℝ)..s, dpF' c ν s μ F σ y0) y0 := by
  obtain ⟨M, hM0, hb⟩ := dp_slice_bounds hc hF
  obtain ⟨s₁, hs₁, hzero⟩ := dp_support hF
  obtain ⟨B, hB0, hBw⟩ := dp_W_bound hs μ hs₁
  have hgnn : ∀ σ, 0 ≤ dpBound s₁ s B M σ := fun σ =>
    Set.indicator_nonneg (fun _ _ => mul_nonneg hB0 hM0) σ
  have hWm : Measurable (dpW s μ) := by
    unfold dpW
    exact (Complex.measurable_ofReal.comp (measurable_id.div_const s)).pow_const μ
  have hne : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ s := by
    filter_upwards [(Set.countable_singleton s).ae_notMem (volume : Measure ℝ)] with σ hσ
    exact fun h => hσ (by simp [h])
  have hmeasF : ∀ y : ℝ × ℝ, AEStronglyMeasurable (fun σ => dpF c ν s μ F σ y)
      (volume.restrict (Set.uIoc 0 s)) := by
    intro y
    have h1 : StronglyMeasurable (fun σ => dpW s μ σ • dpP c ν s F σ y) :=
      hWm.stronglyMeasurable.smul (dp_sm_P hF y)
    refine h1.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (hne.mono fun σ hσne hmem => ?_)
    rw [Set.uIoc_of_le hs.le] at hmem
    have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 (lt_of_le_of_ne hmem.2 hσne))
    simp only [dpF, dpP]
    rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  have hF_meas : ∀ᶠ y in 𝓝 y0, AEStronglyMeasurable (fun σ => dpF c ν s μ F σ y)
      (volume.restrict (Set.uIoc 0 s)) := Eventually.of_forall hmeasF
  have hgInt : IntervalIntegrable (dpBound s₁ s B M) volume 0 s := by
    have hc0 : IntervalIntegrable (fun _ : ℝ => B * M) volume 0 s := intervalIntegrable_const
    rw [intervalIntegrable_iff, Set.uIoc_of_le hs.le]
    exact hc0.1.indicator measurableSet_Icc
  have hF_int : IntervalIntegrable (fun σ => dpF c ν s μ F σ y0) volume 0 s := by
    refine IntervalIntegrable.mono_fun' hgInt (hmeasF y0) ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun σ hmem => ?_)
    rw [Set.uIoc_of_le hs.le] at hmem
    show ‖dpF c ν s μ F σ y0‖ ≤ dpBound s₁ s B M σ
    by_cases hσ : σ < s₁
    · have hz0 : heatSlice c F σ = fun _ => 0 := funext fun w => hzero σ hσ w
      unfold dpF
      rw [hz0, dp_planeHeat_zero]
      simp only [smul_zero, norm_zero]
      exact hgnn σ
    · push_neg at hσ
      have hmemI : σ ∈ Icc s₁ s := ⟨hσ, hmem.2⟩
      have hind : dpBound s₁ s B M σ = B * M := by
        unfold dpBound
        exact Set.indicator_of_mem hmemI _
      rw [hind]
      unfold dpF
      rw [norm_smul]
      exact mul_le_mul (hBw σ hmemI)
        (dp_planeHeat_norm_le (ν * (s - σ)) (heatSlice c F σ) M (fun x => (hb σ x).1) y0)
        (norm_nonneg _) hB0
  have hF'_meas : AEStronglyMeasurable (fun σ => dpF' c ν s μ F σ y0)
      (volume.restrict (Set.uIoc 0 s)) :=
    (hWm.stronglyMeasurable.smul (dp_sm_D hF y0)).aestronglyMeasurable
  have h_bound : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Set.uIoc 0 s → ∀ x ∈ (univ : Set (ℝ × ℝ)),
      ‖dpF' c ν s μ F σ x‖ ≤ dpBound s₁ s B M σ := by
    refine hne.mono fun σ hσne hmem x _ => ?_
    rw [Set.uIoc_of_le hs.le] at hmem
    by_cases hσ : σ < s₁
    · have hz0 : heatSlice c F σ = fun _ => 0 := funext fun w => hzero σ hσ w
      have hσs : σ < s := lt_of_le_of_ne hmem.2 hσne
      have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hσs)
      have hD0 : ‖dpD c ν s F σ x‖ ≤ 0 :=
        dp_norm_dpD_le hθ (dp_slice_contDiff hF σ) (M := 0)
          (fun z => by rw [hz0, fderiv_const_apply]; simp) x
      unfold dpF'
      refine (norm_smul_le (dpW s μ σ) (dpD c ν s F σ x)).trans ?_
      calc ‖dpW s μ σ‖ * ‖dpD c ν s F σ x‖ ≤ ‖dpW s μ σ‖ * 0 :=
            mul_le_mul_of_nonneg_left hD0 (norm_nonneg _)
        _ = 0 := mul_zero _
        _ ≤ dpBound s₁ s B M σ := hgnn σ
    · push_neg at hσ
      have hσs : σ < s := lt_of_le_of_ne hmem.2 hσne
      have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hσs)
      have hmemI : σ ∈ Icc s₁ s := ⟨hσ, hmem.2⟩
      have hD : ‖dpD c ν s F σ x‖ ≤ M :=
        dp_norm_dpD_le hθ (dp_slice_contDiff hF σ) (fun z => (hb σ z).2) x
      have hind : dpBound s₁ s B M σ = B * M := by
        unfold dpBound
        exact Set.indicator_of_mem hmemI _
      rw [hind]
      exact (norm_smul_le (dpW s μ σ) (dpD c ν s F σ x)).trans
        (mul_le_mul (hBw σ hmemI) hD (norm_nonneg _) hB0)
  have h_diff : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Set.uIoc 0 s → ∀ x ∈ (univ : Set (ℝ × ℝ)),
      HasFDerivAt (fun x => dpF c ν s μ F σ x) (dpF' c ν s μ F σ x) x := by
    refine hne.mono fun σ hσne hmem x _ => ?_
    rw [Set.uIoc_of_le hs.le] at hmem
    have hσs : σ < s := lt_of_le_of_ne hmem.2 hσne
    have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hσs)
    have hd := dp_hasFDerivAt_planeHeat hθ (dp_slice_contDiff hF σ) (fun z => hb σ z) x
    exact hd.const_smul (dpW s μ σ)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (F := fun y σ => dpF c ν s μ F σ y) (F' := fun y σ => dpF' c ν s μ F σ y)
    (bound := dpBound s₁ s B M) (x₀ := y0) Filter.univ_mem hF_meas hF_int hF'_meas h_bound
    hgInt h_diff

theorem heatIntDiffPos : UnforcedLeray.Short.PartIIa.N01.HeatIntDiffPos := by
  intro c ν hc hν μ F hF s hs i
  have hV : Differentiable ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (s, y)) := fun y0 =>
    (dp_main hc hν μ hF hs y0).differentiableAt
  exact ((PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 2 => ℂ) i).restrictScalars ℝ).differentiable.comp hV

end UnforcedLeray.Short.PartIIa.N01
