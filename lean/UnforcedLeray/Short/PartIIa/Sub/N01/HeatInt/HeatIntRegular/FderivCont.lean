import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular.ContPos
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular.DiffPos

/-!
# `PartII-a:N01/9/1/2/4/3/6` (helper): continuity of the `(q,η)`-derivative of the heat integral

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.

For `s > 0` the derivative of `y ↦ smoothHeatInt (s,y) i` at `y` is the `i`-th component of
`∫ σ in 0..s, dpF' σ y`. For each direction `v`, the directional derivative of a force `F` is
again a smooth periodic force `fdVField F v := fun p => fderiv F p (0,v)` (vanishing on the same
band), and `fderiv (heatSlice F σ) w v = heatSlice (fdVField F v) σ w`. Hence
`(∫ σ in 0..s, dpF' σ y) v = smoothHeatInt (fdVField F v) (s,y)`, which is jointly continuous on
`s > 0` by `heatIntContPos`. Continuity of a family of CLMs on a finite dimensional space is
checked on each application (`continuousOn_clm_apply`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The directional derivative `p ↦ DF(p)(0,v)` of a force in the `(s,w)`-directions. -/
def fdVField (F : Profile → MeridC) (v : ℝ × ℝ) : Profile → MeridC :=
  fun p => fderiv ℝ F p ((0 : ℝ), v)

theorem fdv_periodic {c : ℝ} {F : Profile → MeridC} (hF : IsSmoothForceFn c F) (v : ℝ × ℝ) :
    ∀ p : Profile, fdVField F v (p.1, p.2.1 + c, p.2.2) = fdVField F v p := by
  obtain ⟨hFc, hFper⟩ := dp_unpack hF
  have hxa' : ∀ x : Profile, x + ((0 : ℝ), c, (0 : ℝ)) = (x.1, x.2.1 + c, x.2.2) :=
    fun x => by ext <;> simp
  have hpa : ∀ x : Profile, F (x + ((0 : ℝ), c, (0 : ℝ))) = F x := fun x => by
    rw [hxa' x]
    exact hFper x
  intro p
  have h1 : fderiv ℝ (fun x : Profile => F (x + ((0 : ℝ), c, (0 : ℝ)))) p =
      fderiv ℝ F (p + ((0 : ℝ), c, (0 : ℝ))) := fderiv_comp_add_right _
  have h2 : (fun x : Profile => F (x + ((0 : ℝ), c, (0 : ℝ)))) = F := funext hpa
  rw [h2] at h1
  unfold fdVField
  rw [← hxa' p, ← h1]

theorem fdv_smooth {c : ℝ} {F : Profile → MeridC} (hF : IsSmoothForceFn c F) (v : ℝ × ℝ) :
    IsSmoothForceFn c (fdVField F v) := by
  have hper := fdv_periodic hF v
  obtain ⟨hFc, _, s₁, s₂, R, hs₁, hz⟩ := hF
  refine ⟨?_, hper, s₁, s₂, R, hs₁, ?_⟩
  · have hd : ContDiff ℝ ∞ (fderiv ℝ F) := hFc.fderiv_right (by simp)
    exact (ContinuousLinearMap.apply ℝ MeridC ((0 : ℝ), v)).contDiff.comp hd
  · intro p hp
    have hU : IsOpen {p : Profile | p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|} :=
      (isOpen_lt continuous_fst continuous_const).union
        ((isOpen_lt continuous_const continuous_fst).union
          (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))))
    have hev : F =ᶠ[𝓝 p] fun _ => (0 : MeridC) :=
      Filter.eventually_of_mem (hU.mem_nhds hp) (fun y hy => hz y hy)
    unfold fdVField
    rw [hev.fderiv_eq]
    simp

/-- The slice of the directional derivative field is the directional derivative of the slice. -/
theorem fd_heatSlice_eq {c : ℝ} {F : Profile → MeridC} (hF : IsSmoothForceFn c F) (v : ℝ × ℝ)
    (σ : ℝ) (w : ℝ × ℝ) :
    heatSlice c (fdVField F v) σ w = fderiv ℝ (heatSlice c F σ) w v := by
  rw [dp_heatSlice_eq (fdv_periodic hF v) σ w, dp_fderiv_slice hF σ w]
  simp [fdVField]

/-- For `σ < s`, the `v`-derivative of the `σ`-integrand is the heat integrand of `fdVField F v`. -/
theorem fd_dpF'_apply {c ν : ℝ} {μ : ℂ} {F : Profile → MeridC} (hc : 0 < c) (hν : 0 < ν)
    (hF : IsSmoothForceFn c F) {s : ℝ} (σ : ℝ) (hσ : σ < s) (y v : ℝ × ℝ) :
    dpF' c ν s μ F σ y v = dpF c ν s μ (fdVField F v) σ y := by
  have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hσ)
  obtain ⟨M, hM0, hb⟩ := dp_slice_bounds hc hF
  have hint := dp_integrable_D hθ (dp_slice_contDiff hF σ) (fun x => (hb σ x).2) y
  have hfun : heatSlice c (fdVField F v) σ = fun w => fderiv ℝ (heatSlice c F σ) w v :=
    funext fun w => fd_heatSlice_eq hF v σ w
  unfold dpF' dpF dpD
  rw [hfun, smul_apply, ContinuousLinearMap.integral_apply hint v,
    UnforcedLeray.B0224.planeHeat_of_pos hθ]
  simp only [smul_apply]

/-- Integrability of the `σ`-integrand of the `y`-derivative on `(0, s]`, for `s > 0`. -/
theorem fd_dpF'_intervalIntegrable {c ν : ℝ} {μ : ℂ} {F : Profile → MeridC} (hc : 0 < c)
    (hν : 0 < ν) (hF : IsSmoothForceFn c F) {s : ℝ} (hs : 0 < s) (y0 : ℝ × ℝ) :
    IntervalIntegrable (fun σ => dpF' c ν s μ F σ y0) volume 0 s := by
  obtain ⟨M, hM0, hb⟩ := dp_slice_bounds hc hF
  obtain ⟨s₁, hs₁, hzero⟩ := dp_support hF
  obtain ⟨B, hB0, hBw⟩ := dp_W_bound hs μ hs₁
  have hWm : Measurable (dpW s μ) := by
    unfold dpW
    exact (Complex.measurable_ofReal.comp (measurable_id.div_const s)).pow_const μ
  have hne : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ s := by
    filter_upwards [(Set.countable_singleton s).ae_notMem (volume : Measure ℝ)] with σ hσ
    exact fun h => hσ (by simp [h])
  have hgInt : IntervalIntegrable (dpBound s₁ s B M) volume 0 s := by
    have hc0 : IntervalIntegrable (fun _ : ℝ => B * M) volume 0 s := intervalIntegrable_const
    rw [intervalIntegrable_iff, Set.uIoc_of_le hs.le]
    exact hc0.1.indicator measurableSet_Icc
  refine IntervalIntegrable.mono_fun' hgInt
    (hWm.stronglyMeasurable.smul (dp_sm_D hF y0)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (hne.mono fun σ hσne hmem => ?_)
  rw [Set.uIoc_of_le hs.le] at hmem
  by_cases hσ : σ < s₁
  · have hz0 : heatSlice c F σ = fun _ => 0 := funext fun w => hzero σ hσ w
    have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 (lt_of_le_of_ne hmem.2 hσne))
    have hD0 : ‖dpD c ν s F σ y0‖ ≤ 0 :=
      dp_norm_dpD_le (mul_pos hν (sub_pos.2 (lt_of_le_of_ne hmem.2 hσne)))
        (dp_slice_contDiff hF σ) (M := 0)
        (fun z => by rw [hz0, fderiv_const_apply]; simp) y0
    have hn : ‖dpF' c ν s μ F σ y0‖ ≤ 0 := by
      unfold dpF'
      exact (norm_smul_le (dpW s μ σ) (dpD c ν s F σ y0)).trans
        ((mul_le_mul_of_nonneg_left hD0 (norm_nonneg _)).trans (le_of_eq (mul_zero _)))
    have hind0 : dpBound s₁ s B M σ = 0 := by
      unfold dpBound
      rw [Set.indicator_apply,
        if_neg (show ¬ (σ ∈ Icc s₁ s) from fun h => absurd h.1 (not_le.2 hσ))]
    show ‖dpF' c ν s μ F σ y0‖ ≤ dpBound s₁ s B M σ
    rw [hind0]
    exact hn
  · push_neg at hσ
    have hσs : σ < s := lt_of_le_of_ne hmem.2 hσne
    have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hσs)
    have hmemI : σ ∈ Icc s₁ s := ⟨hσ, hmem.2⟩
    have hD : ‖dpD c ν s F σ y0‖ ≤ M :=
      dp_norm_dpD_le hθ (dp_slice_contDiff hF σ) (fun z => (hb σ z).2) y0
    have hind : dpBound s₁ s B M σ = B * M := by
      unfold dpBound
      exact Set.indicator_of_mem hmemI _
    show ‖dpF' c ν s μ F σ y0‖ ≤ dpBound s₁ s B M σ
    rw [hind]
    unfold dpF'
    exact (norm_smul_le (dpW s μ σ) (dpD c ν s F σ y0)).trans
      (mul_le_mul (hBw σ hmemI) hD (norm_nonneg _) hB0)

/-- Pairing the `y`-derivative integral with a direction `v` gives the heat integral of
`fdVField F v`, for `s > 0`. -/
theorem fd_integral_apply {c ν : ℝ} {μ : ℂ} {F : Profile → MeridC} (hc : 0 < c) (hν : 0 < ν)
    (hF : IsSmoothForceFn c F) {s : ℝ} (hs : 0 < s) (y v : ℝ × ℝ) :
    (∫ σ in (0 : ℝ)..s, dpF' c ν s μ F σ y) v = smoothHeatInt c ν μ (fdVField F v) (s, y) := by
  have hint := fd_dpF'_intervalIntegrable (μ := μ) hc hν hF hs y
  have h1 := ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousLinearMap.apply ℝ MeridC v) hint
  simp only [ContinuousLinearMap.apply_apply] at h1
  rw [← h1]
  have hne : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ s := by
    filter_upwards [(Set.countable_singleton s).ae_notMem (volume : Measure ℝ)] with σ hσ
    exact fun h => hσ (by simp [h])
  show ∫ σ in (0 : ℝ)..s, dpF' c ν s μ F σ y v = ∫ σ in (0 : ℝ)..s, dpF c ν s μ (fdVField F v) σ y
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hne] with σ hσne
  intro hmem
  rw [Set.uIoc_of_le hs.le] at hmem
  exact fd_dpF'_apply hc hν hF σ (lt_of_le_of_ne hmem.2 hσne) y v

/-- **Target.** The `(q,η)`-derivative of the heat integral is jointly continuous on `s > 0`. -/
theorem heatIntFderivCont : UnforcedLeray.Short.PartIIa.N01.HeatIntFderivCont := by
  intro c ν hc hν μ F hF i
  let P : MeridC →L[ℝ] ℂ :=
    (PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 2 => ℂ) i).restrictScalars ℝ
  have hfd : ∀ p : UnforcedLeray.Short.PartIIIb.Concrete.Chart, 0 < p.1 →
      fderiv ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (p.1, y) i) p.2 =
        P.comp (∫ σ in (0 : ℝ)..p.1, dpF' c ν p.1 μ F σ p.2) := by
    intro p hp
    have hd := dp_main hc hν μ hF hp p.2
    have hP : HasFDerivAt (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (p.1, y) i)
        (P.comp (∫ σ in (0 : ℝ)..p.1, dpF' c ν p.1 μ F σ p.2)) p.2 :=
      P.hasFDerivAt.comp p.2 hd
    exact hP.fderiv
  refine ContinuousOn.congr (f := fun p : UnforcedLeray.Short.PartIIIb.Concrete.Chart =>
    P.comp (∫ σ in (0 : ℝ)..p.1, dpF' c ν p.1 μ F σ p.2)) ?_
    (fun p hp => hfd p hp.1)
  rw [continuousOn_clm_apply]
  intro v
  have hcont : ContinuousOn (fun p : UnforcedLeray.Short.PartIIIb.Concrete.Chart =>
      P (smoothHeatInt c ν μ (fdVField F v) p)) (Ioi (0 : ℝ) ×ˢ univ) :=
    P.continuous.comp_continuousOn (heatIntContPos c ν hc hν μ (fdVField F v) (fdv_smooth hF v))
  refine hcont.congr ?_
  intro p hp
  show P ((∫ σ in (0 : ℝ)..p.1, dpF' c ν p.1 μ F σ p.2) v) = _
  rw [fd_integral_apply (μ := μ) hc hν hF hp.1 p.2 v]

end UnforcedLeray.Short.PartIIa.N01
