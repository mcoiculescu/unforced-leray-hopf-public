import UnforcedLeray.Lib.PlanarSectors.Weighted

/-!
# Sector–profile isometry on `L²_M` (INF12 target P3)


§5, Level P, target **P3**. An element of angular sector `n` of `L²_M` (`paper/main.tex`
lines 653–660, blueprint unit `B0008`; "For `w ∈ L²_M` in angular sector `n ≥ 1`", line 1366)
is `w(r) e^{inϑ}`, and in polar coordinates
`‖w(r)e^{inϑ}‖²_{L²_M} = ∫₀^∞ |w(r)|² 2π r ⟨r⟩^{2M} dr`
(the polar form of the weighted norm; unit `B0079`, lines 1366–1379, writes the same norm
without the factor `2π`).

Main declarations (namespace `UnforcedLeray.Planar`):
* `profileMeasure M = 2π r (1 + r²)^M dr` on `(0, ∞)`;
* `lintegral_ofProfile`, `memLp_ofProfile_iff`, `eLpNorm_ofProfile`: the polar norm identity;
* `ofProfileL M n : L²(profileMeasure M) →ₗᵢ[ℂ] L2w M`, `w ↦ w(|x|)(x/|x|)ⁿ`;
* `range_ofProfileL`: its range is the range of `sectorProjW M n`;
* `sectorIso M n : range (sectorProjW M n) ≃ₗᵢ[ℂ] L²(profileMeasure M)`, with
  `coeFn_sectorIso_symm` (`(sectorIso M n).symm w = w(r) e^{inϑ}` a.e.).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

namespace UnforcedLeray.Planar

open UnforcedLeray.Planar.NUE

/-- The radial density `2π r ⟨r⟩^{2M}` of the profile space. -/
def profileDensity (M : ℝ) (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal (2 * π * r * (1 + r ^ 2) ^ M)

/-- The profile measure `2π r (1 + r²)^M dr` on `(0, ∞)`: `L²(profileMeasure M)` is the space of
radial profiles of one angular sector of `L²_M`. -/
def profileMeasure (M : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun r => ENNReal.ofReal (2 * π * r * (1 + r ^ 2) ^ M)

theorem measurable_profileDensity (M : ℝ) : Measurable (profileDensity M) := by
  unfold profileDensity
  fun_prop

theorem profileMeasure_ac (M : ℝ) : profileMeasure M ≪ volume.restrict (Ioi 0) :=
  withDensity_absolutelyContinuous _ _

theorem ac_profileMeasure (M : ℝ) : volume.restrict (Ioi (0 : ℝ)) ≪ profileMeasure M := by
  refine withDensity_absolutelyContinuous' (measurable_profileDensity M).aemeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr' : (0 : ℝ) < r := hr
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

theorem aestronglyMeasurable_profileMeasure_iff (M : ℝ) {h : ℝ → ℂ} :
    AEStronglyMeasurable h (profileMeasure M) ↔ AEStronglyMeasurable h (volume.restrict (Ioi 0)) :=
  ⟨fun hh => hh.mono_ac (ac_profileMeasure M), fun hh => hh.mono_ac (profileMeasure_ac M)⟩

/-- `eLpNorm f 2 μ = (∫⁻ ‖f‖ₑ²)^{1/2}`. -/
theorem eLpNorm_two_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- A profile equality almost everywhere on `(0, ∞)` gives an equality of the planar sector
functions almost everywhere on `ℂ`. -/
theorem ofProfile_congr_ae (n : ℤ) {h₁ h₂ : ℝ → ℂ} (h : h₁ =ᵐ[volume.restrict (Ioi 0)] h₂) :
    Ang.ofProfile n h₁ =ᵐ[volume] Ang.ofProfile n h₂ := by
  filter_upwards [Ang.SectorL2Aux.quasiMeasurePreserving_norm.ae_eq_comp h] with x hx
  simp only [Function.comp_apply] at hx
  rw [Ang.ofProfile, Ang.ofProfile, hx]

theorem ofProfile_congr_ae' (M : ℝ) (n : ℤ) {h₁ h₂ : ℝ → ℂ} (h : h₁ =ᵐ[profileMeasure M] h₂) :
    Ang.ofProfile n h₁ =ᵐ[wMeasure M] Ang.ofProfile n h₂ :=
  (wMeasure_ac M).ae_le (ofProfile_congr_ae n ((ac_profileMeasure M).ae_le h))

theorem aestronglyMeasurable_ofProfile (M : ℝ) (n : ℤ) {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h (profileMeasure M)) :
    AEStronglyMeasurable (Ang.ofProfile n h) (wMeasure M) :=
  (Ang.SectorL2Aux.aestronglyMeasurable_ofProfile
    ((aestronglyMeasurable_profileMeasure_iff M).1 hm)).mono_ac (wMeasure_ac M)

/-- **The polar norm identity**:
`∫ |w(|x|) e^{inϑ}|² ⟨x⟩^{2M} dx = ∫₀^∞ |w(r)|² 2π r ⟨r⟩^{2M} dr`. -/
theorem lintegral_ofProfile (M : ℝ) (n : ℤ) {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h (volume.restrict (Ioi 0))) :
    ∫⁻ x, ‖Ang.ofProfile n h x‖ₑ ^ 2 ∂wMeasure M = ∫⁻ r, ‖h r‖ₑ ^ 2 ∂profileMeasure M := by
  set h' : ℝ → ℂ := hm.mk h with hh'
  have hae : h =ᵐ[volume.restrict (Ioi 0)] h' := hm.ae_eq_mk
  have hm' : Measurable h' := hm.stronglyMeasurable_mk.measurable
  set G : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal ((1 + r ^ 2) ^ M) * ‖h' r‖ₑ ^ 2 with hG
  have hGm : Measurable G := by
    simp only [hG]
    fun_prop
  have hL : ∫⁻ x, ‖Ang.ofProfile n h x‖ₑ ^ 2 ∂wMeasure M = ∫⁻ x : ℂ, G ‖x‖ := by
    change ∫⁻ x, _ ∂(volume.withDensity (wDensity M)) = _
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (measurable_wDensity M) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine lintegral_congr_ae ?_
    filter_upwards [Ang.SectorL2Aux.ae_norm_ofProfile n h,
      Ang.SectorL2Aux.quasiMeasurePreserving_norm.ae_eq_comp hae] with x hx1 hx2
    simp only [Function.comp_apply] at hx2
    simp only [Pi.mul_apply, hG, wDensity]
    rw [← enorm_norm, hx1, enorm_norm, hx2]
  have hR : ∫⁻ r, ‖h r‖ₑ ^ 2 ∂profileMeasure M =
      ∫⁻ r in Ioi 0, profileDensity M r * ‖h' r‖ₑ ^ 2 := by
    change ∫⁻ r, _ ∂((volume.restrict (Ioi 0)).withDensity (profileDensity M)) = _
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (measurable_profileDensity M) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with r hr
    simp only [Pi.mul_apply, profileDensity]
    rw [hr]
  rw [hL, hR, Polar.lintegral_comp_norm hGm, ← lintegral_const_mul' _ _
    (by simp [ENNReal.mul_eq_top])]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  simp only [hG, profileDensity]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  ring

theorem eLpNorm_ofProfile (M : ℝ) (n : ℤ) {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h (profileMeasure M)) :
    eLpNorm (Ang.ofProfile n h) 2 (wMeasure M) = eLpNorm h 2 (profileMeasure M) := by
  rw [eLpNorm_two_eq, eLpNorm_two_eq,
    lintegral_ofProfile M n ((aestronglyMeasurable_profileMeasure_iff M).1 hm)]

/-- `w(r) e^{inϑ} ∈ L²_M` iff `w ∈ L²(2π r ⟨r⟩^{2M} dr)`. -/
theorem memLp_ofProfile_iff (M : ℝ) (n : ℤ) {h : ℝ → ℂ}
    (hm : AEStronglyMeasurable h (profileMeasure M)) :
    MemLp (Ang.ofProfile n h) 2 (wMeasure M) ↔ MemLp h 2 (profileMeasure M) := by
  unfold MemLp
  rw [eLpNorm_ofProfile M n hm]
  exact ⟨fun h1 => ⟨hm, h1.2⟩, fun h1 => ⟨aestronglyMeasurable_ofProfile M n hm, h1.2⟩⟩

theorem memLp_ofProfile (M : ℝ) (n : ℤ) (h : Lp ℂ 2 (profileMeasure M)) :
    MemLp (Ang.ofProfile n h) 2 (wMeasure M) :=
  (memLp_ofProfile_iff M n (Lp.aestronglyMeasurable h)).2 (Lp.memLp h)

/-- The profile map `w ↦ w(|x|) (x/|x|)ⁿ` as a linear map into `L²_M`. -/
def ofProfileLin (M : ℝ) (n : ℤ) : Lp ℂ 2 (profileMeasure M) →ₗ[ℂ] L2w M where
  toFun h := (memLp_ofProfile M n h).toLp _
  map_add' h g := by
    apply Lp.ext
    have hc := ofProfile_congr_ae' M n (Lp.coeFn_add h g)
    filter_upwards [MemLp.coeFn_toLp (memLp_ofProfile M n (h + g)),
      MemLp.coeFn_toLp (memLp_ofProfile M n h), MemLp.coeFn_toLp (memLp_ofProfile M n g),
      Lp.coeFn_add ((memLp_ofProfile M n h).toLp _) ((memLp_ofProfile M n g).toLp _), hc]
      with x h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, h5]
    simp only [Ang.ofProfile, Pi.add_apply, add_mul]
  map_smul' c h := by
    apply Lp.ext
    have hc := ofProfile_congr_ae' M n (Lp.coeFn_smul c h)
    filter_upwards [MemLp.coeFn_toLp (memLp_ofProfile M n (c • h)),
      MemLp.coeFn_toLp (memLp_ofProfile M n h),
      Lp.coeFn_smul c ((memLp_ofProfile M n h).toLp _), hc] with x h1 h2 h3 h5
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, h5]
    simp only [Ang.ofProfile, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem coeFn_ofProfileLin (M : ℝ) (n : ℤ) (h : Lp ℂ 2 (profileMeasure M)) :
    (ofProfileLin M n h : ℂ → ℂ) =ᵐ[wMeasure M] Ang.ofProfile n h :=
  MemLp.coeFn_toLp (memLp_ofProfile M n h)

theorem norm_ofProfileLin (M : ℝ) (n : ℤ) (h : Lp ℂ 2 (profileMeasure M)) :
    ‖ofProfileLin M n h‖ = ‖h‖ := by
  change ‖(memLp_ofProfile M n h).toLp _‖ = ‖h‖
  rw [Lp.norm_toLp, eLpNorm_ofProfile M n (Lp.aestronglyMeasurable h), Lp.norm_def]

/-- Profiles are sector-`n` elements: `P_n (w(r)e^{inϑ}) = w(r)e^{inϑ}`. -/
theorem sectorProjW_ofProfileLin (M : ℝ) (n : ℤ) (h : Lp ℂ 2 (profileMeasure M)) :
    sectorProjW M n (ofProfileLin M n h) = ofProfileLin M n h := by
  apply Lp.ext
  have h1 := coeFn_sectorProjW M n (ofProfileLin M n h)
  have h2 := (wMeasure_ac M).ae_le
    (Ang.sectorProj_congr_ae n ((volume_ac M).ae_le (coeFn_ofProfileLin M n h)))
  filter_upwards [h1, h2, coeFn_ofProfileLin M n h] with x hx1 hx2 hx3
  rw [hx1, hx2, Ang.sectorProj_ofProfile]
  simp only [↓reduceIte]
  rw [hx3]

theorem mem_range_sectorProjW_iff (M : ℝ) (n : ℤ) (f : L2w M) :
    f ∈ LinearMap.range (sectorProjW M n : L2w M →ₗ[ℂ] L2w M) ↔ sectorProjW M n f = f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact sectorProjW_idem n g
  · intro hf
    exact ⟨f, hf⟩

/-- The range of the profile map is the range of the sector projection. -/
theorem range_ofProfileLin (M : ℝ) (n : ℤ) :
    LinearMap.range (ofProfileLin M n) =
      LinearMap.range (sectorProjW M n : L2w M →ₗ[ℂ] L2w M) := by
  ext f
  constructor
  · rintro ⟨h, rfl⟩
    exact (mem_range_sectorProjW_iff M n _).2 (sectorProjW_ofProfileLin M n h)
  · rintro ⟨g, rfl⟩
    have hP := sectorProjW_ae_eq_ofProfile M n g
    set w := Polar.angularSector (g : ℂ → ℂ) n with hw
    have hwm : AEStronglyMeasurable w (profileMeasure M) :=
      (aestronglyMeasurable_profileMeasure_iff M).2
        (Ang.ParsevalH.aestronglyMeasurable_angularSector
          ((Lp.aestronglyMeasurable g).mono_ac (volume_ac M)) n)
    have hwL : MemLp w 2 (profileMeasure M) := by
      refine (memLp_ofProfile_iff M n hwm).1 ?_
      exact (Lp.memLp (sectorProjW M n g)).ae_eq hP
    refine ⟨hwL.toLp w, ?_⟩
    apply Lp.ext
    filter_upwards [coeFn_ofProfileLin M n (hwL.toLp w),
      ofProfile_congr_ae' M n hwL.coeFn_toLp, hP] with x h1 h2 h3
    change _ = (sectorProjW M n g : ℂ → ℂ) x
    rw [h1, h2, h3]

/-- The profile map with codomain the sector `range (sectorProjW M n)`. -/
def ofProfileSec (M : ℝ) (n : ℤ) :
    Lp ℂ 2 (profileMeasure M) →ₗᵢ[ℂ]
      ↥(LinearMap.range (sectorProjW M n : L2w M →ₗ[ℂ] L2w M)) where
  toLinearMap := (ofProfileLin M n).codRestrict _ fun h => by
    rw [← range_ofProfileLin]
    exact ⟨h, rfl⟩
  norm_map' h := norm_ofProfileLin M n h

theorem surjective_ofProfileSec (M : ℝ) (n : ℤ) : Function.Surjective (ofProfileSec M n) := by
  rintro ⟨f, hf⟩
  rw [← range_ofProfileLin] at hf
  obtain ⟨h, rfl⟩ := hf
  exact ⟨h, rfl⟩

/-- **The sector–profile isometry** (INF12 P3): the angular sector `n` of `L²_M` is isometric
to `L²(2π r ⟨r⟩^{2M} dr)` by `w(r)e^{inϑ} ↦ w`. -/
def sectorIso (M : ℝ) (n : ℤ) :
    ↥(LinearMap.range (sectorProjW M n : L2w M →ₗ[ℂ] L2w M)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (profileMeasure M) :=
  (LinearIsometryEquiv.ofSurjective (ofProfileSec M n) (surjective_ofProfileSec M n)).symm

/-- The inverse of `sectorIso` is `w ↦ w(r) e^{inϑ}`. -/
theorem coeFn_sectorIso_symm (M : ℝ) (n : ℤ) (h : Lp ℂ 2 (profileMeasure M)) :
    (((sectorIso M n).symm h : L2w M) : ℂ → ℂ) =ᵐ[wMeasure M] Ang.ofProfile n h := by
  have : ((sectorIso M n).symm h : L2w M) = ofProfileLin M n h := rfl
  rw [this]
  exact coeFn_ofProfileLin M n h

/-- A sector element is the planar function of its profile: `f = (sectorIso f)(r) e^{inϑ}`. -/
theorem coeFn_sectorIso (M : ℝ) (n : ℤ)
    (f : ↥(LinearMap.range (sectorProjW M n : L2w M →ₗ[ℂ] L2w M))) :
    ((f : L2w M) : ℂ → ℂ) =ᵐ[wMeasure M] Ang.ofProfile n (sectorIso M n f) := by
  have h := coeFn_sectorIso_symm M n (sectorIso M n f)
  rwa [LinearIsometryEquiv.symm_apply_apply] at h

end UnforcedLeray.Planar
