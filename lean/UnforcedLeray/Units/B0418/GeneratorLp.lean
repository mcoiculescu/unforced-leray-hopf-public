import UnforcedLeray.Units.B0418.Generator

/-!
# B0418 helper: the `L^p` generator of `S_ν` on `C_c^∞`

Blueprint unit B0418, `paper/main.tex` lines 7412 and 7419--7420. Assembly of
`Generator.lean`, `HeatGen.lean` and `Continuity.lean`: for `ν > 0`, `1 ≤ p < ∞` and
`h ∈ C_c^∞(ℝ³; ℝ³)`, `r⁻¹(S_ν(r)h - h) → νΔh + ½ y·∇h + ½h` in `L^p` as `r → 0⁺`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.B0418

open UnforcedLeray.AncientLocalization

variable {p : ℝ≥0∞}

/-- Six-term triangle inequality. -/
theorem eLpNorm_add6_le (hp1 : 1 ≤ p) {A1 A2 A3 A4 A5 A6 : SpatialField}
    (m1 : AEStronglyMeasurable A1 volume) (m2 : AEStronglyMeasurable A2 volume)
    (m3 : AEStronglyMeasurable A3 volume) (m4 : AEStronglyMeasurable A4 volume)
    (m5 : AEStronglyMeasurable A5 volume) (m6 : AEStronglyMeasurable A6 volume) :
    eLpNorm (A1 + A2 + A3 + A4 + A5 + A6) p volume ≤
      eLpNorm A1 p volume + eLpNorm A2 p volume + eLpNorm A3 p volume +
        eLpNorm A4 p volume + eLpNorm A5 p volume + eLpNorm A6 p volume := by
  have s2 := eLpNorm_add_le m1 m2 hp1
  have s3 := eLpNorm_add_le (m1.add m2) m3 hp1
  have s4 := eLpNorm_add_le ((m1.add m2).add m3) m4 hp1
  have s5 := eLpNorm_add_le (((m1.add m2).add m3).add m4) m5 hp1
  have s6 := eLpNorm_add_le ((((m1.add m2).add m3).add m4).add m5) m6 hp1
  calc eLpNorm (A1 + A2 + A3 + A4 + A5 + A6) p volume
      ≤ eLpNorm (A1 + A2 + A3 + A4 + A5) p volume + eLpNorm A6 p volume := s6
    _ ≤ eLpNorm (A1 + A2 + A3 + A4) p volume + eLpNorm A5 p volume + eLpNorm A6 p volume :=
        add_le_add_left s5 _
    _ ≤ eLpNorm (A1 + A2 + A3) p volume + eLpNorm A4 p volume + eLpNorm A5 p volume +
          eLpNorm A6 p volume := add_le_add_left (add_le_add_left s4 _) _
    _ ≤ eLpNorm (A1 + A2) p volume + eLpNorm A3 p volume + eLpNorm A4 p volume +
          eLpNorm A5 p volume + eLpNorm A6 p volume :=
        add_le_add_left (add_le_add_left (add_le_add_left s3 _) _) _
    _ ≤ _ := add_le_add_left (add_le_add_left (add_le_add_left (add_le_add_left s2 _) _) _) _

/-- Bound of a six-term decomposition. -/
theorem eLpNorm_le_of_sum6 (hp1 : 1 ≤ p) {F A1 A2 A3 A4 A5 A6 : SpatialField}
    {X1 X2 X3 X4 X5 : ℝ≥0∞} (hF : F = A1 + A2 + A3 + A4 + A5 + A6)
    (m1 : AEStronglyMeasurable A1 volume) (m2 : AEStronglyMeasurable A2 volume)
    (m3 : AEStronglyMeasurable A3 volume) (m4 : AEStronglyMeasurable A4 volume)
    (m5 : AEStronglyMeasurable A5 volume) (m6 : AEStronglyMeasurable A6 volume)
    (e1 : eLpNorm A1 p volume ≤ X1) (e2 : eLpNorm A2 p volume ≤ X2)
    (e3 : eLpNorm A3 p volume ≤ X3) (e4 : eLpNorm A4 p volume ≤ X4)
    (e5 : eLpNorm A5 p volume ≤ X5) :
    eLpNorm F p volume ≤ X1 + X2 + X3 + X4 + X5 + eLpNorm A6 p volume := by
  rw [hF]
  exact (eLpNorm_add6_le hp1 m1 m2 m3 m4 m5 m6).trans
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add e1 e2) e3) e4) e5) le_rfl)

/-- Function-level form of `quotient_decomposition`. -/
theorem quotient_eq_sum {ν r : ℝ} (hr : 0 < r) (hτ : 0 < ν * (Real.exp r - 1))
    (h : SpatialField) :
    (fun y => r⁻¹ • (freeEvolution ν r h y - h y) - generator ν h y) =
    SpatialScaling.spatialScale (Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹)
        (Real.exp (r / 2)) (fun x => (ν * (Real.exp r - 1))⁻¹ •
          (Heat.flow h (ν * (Real.exp r - 1)) x - h x) - vecLaplacian h x) +
      (Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹) •
        (fun x => vecLaplacian h (Real.exp (r / 2) • x) - vecLaplacian h x) +
      (Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹ - ν) • vecLaplacian h +
      (r⁻¹ * (Real.exp (r / 2) - 1)) • (fun x => h (Real.exp (r / 2) • x) - h x) +
      (r⁻¹ * (Real.exp (r / 2) - 1) - 1 / 2) • h +
      (fun y => r⁻¹ • (h (Real.exp (r / 2) • y) - h y) - (1 / 2 : ℝ) • fderiv ℝ h y y) := by
  funext y
  simp only [Pi.add_apply, Pi.smul_apply, SpatialScaling.spatialScale]
  exact quotient_decomposition hr.ne' hτ.ne' h y

/-- The `L^p` bound of the similarity difference quotient by six controlled terms. -/
theorem eLpNorm_quotient_le {ν r : ℝ} (hr : 0 < r) (hτ : 0 < ν * (Real.exp r - 1))
    (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞)) {h : SpatialField} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) :
    eLpNorm (fun y => r⁻¹ • (freeEvolution ν r h y - h y) - generator ν h y) p volume ≤
      ‖Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹‖ₑ *
          eLpNorm (fun x => (ν * (Real.exp r - 1))⁻¹ •
            (Heat.flow h (ν * (Real.exp r - 1)) x - h x) - vecLaplacian h x) p volume +
        ‖Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹‖ₑ *
          eLpNorm (fun x => vecLaplacian h (Real.exp (r / 2) • x) - vecLaplacian h x) p volume +
        ‖Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹ - ν‖ₑ *
          eLpNorm (vecLaplacian h) p volume +
        ‖r⁻¹ * (Real.exp (r / 2) - 1)‖ₑ *
          eLpNorm (fun x => h (Real.exp (r / 2) • x) - h x) p volume +
        ‖r⁻¹ * (Real.exp (r / 2) - 1) - 1 / 2‖ₑ * eLpNorm h p volume +
        eLpNorm (fun y => r⁻¹ • (h (Real.exp (r / 2) • y) - h y) -
          (1 / 2 : ℝ) • fderiv ℝ h y y) p volume := by
  have hLc : Continuous (vecLaplacian h) := continuous_vecLaplacian hs
  have hLp : MemLp (vecLaplacian h) p volume :=
    hLc.memLp_of_hasCompactSupport (hasCompactSupport_vecLaplacian hc)
  have hhp : MemLp h p volume := hs.continuous.memLp_of_hasCompactSupport hc
  have hl1 : 1 ≤ Real.exp (r / 2) := Real.one_le_exp (by linarith)
  have hlam0 : Real.exp (r / 2) ≠ 0 := (Real.exp_pos _).ne'
  have hQm : MemLp (fun x => (ν * (Real.exp r - 1))⁻¹ •
      (Heat.flow h (ν * (Real.exp r - 1)) x - h x) - vecLaplacian h x) p volume := by
    have h1 : MemLp (Heat.flow h (ν * (Real.exp r - 1)) - h) p volume :=
      (flow_memLp hp1 hp hhp (ν * (Real.exp r - 1))).sub hhp
    have h2 : MemLp ((ν * (Real.exp r - 1))⁻¹ • (Heat.flow h (ν * (Real.exp r - 1)) - h) -
        vecLaplacian h) p volume := (h1.const_smul (ν * (Real.exp r - 1))⁻¹).sub hLp
    exact h2
  have hLd : MemLp (fun x => vecLaplacian h (Real.exp (r / 2) • x) - vecLaplacian h x) p volume :=
    (SpatialScaling.memLp_comp_dilation hLp hlam0).sub hLp
  have hhd : MemLp (fun x => h (Real.exp (r / 2) • x) - h x) p volume :=
    (SpatialScaling.memLp_comp_dilation hhp hlam0).sub hhp
  have hcf : Continuous (fderiv ℝ h) :=
    (contDiff_one_of_infty hs).continuous_fderiv one_ne_zero
  have hh : Continuous h := hs.continuous
  have hA : Continuous (fun y : Space => h (Real.exp (r / 2) • y)) :=
    hh.comp (continuous_const_smul _)
  have hB : Continuous (fun y : Space => fderiv ℝ h y y) := hcf.clm_apply continuous_id
  have hC1 : Continuous (fun y : Space => r⁻¹ • (h (Real.exp (r / 2) • y) - h y)) :=
    (hA.sub hh).const_smul r⁻¹
  have hC2 : Continuous (fun y : Space => (1 / 2 : ℝ) • fderiv ℝ h y y) :=
    hB.const_smul (1 / 2 : ℝ)
  refine eLpNorm_le_of_sum6 hp1 (quotient_eq_sum hr hτ h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (SpatialScaling.memLp_spatialScale hQm _ hlam0).aestronglyMeasurable
  · exact (hLd.const_smul _).aestronglyMeasurable
  · exact (hLp.const_smul _).aestronglyMeasurable
  · exact (hhd.const_smul _).aestronglyMeasurable
  · exact (hhp.const_smul _).aestronglyMeasurable
  · exact (hC1.sub hC2).aestronglyMeasurable
  · exact eLpNorm_spatialScale_le hp _ hl1 _
  · exact (eLpNorm_const_smul _ _ _ _).le
  · exact (eLpNorm_const_smul _ _ _ _).le
  · exact (eLpNorm_const_smul _ _ _ _).le
  · exact (eLpNorm_const_smul _ _ _ _).le

/-- The generator of `S_ν` on `C_c^∞` in `L^p`: `r⁻¹(S_ν(r)h - h) → (νΔ + ½y·∇ + ½)h`. -/
theorem tendsto_generator {ν : ℝ} (hν : 0 < ν) (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞))
    {h : SpatialField} (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    Tendsto (fun r => eLpNorm (fun y => r⁻¹ • (freeEvolution ν r h y - h y) -
      generator ν h y) p volume) (𝓝[>] 0) (𝓝 0) := by
  have hLp : MemLp (vecLaplacian h) p volume :=
    (continuous_vecLaplacian hs).memLp_of_hasCompactSupport (hasCompactSupport_vecLaplacian hc)
  have hhp : MemLp h p volume := hs.continuous.memLp_of_hasCompactSupport hc
  have hlam : Tendsto (fun r : ℝ => Real.exp (r / 2)) (𝓝[>] 0) (𝓝 1) := by
    have hc' : Continuous (fun r : ℝ => Real.exp (r / 2)) :=
      Real.continuous_exp.comp (continuous_id.div_const 2)
    have := (hc'.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have htau : Tendsto (fun r : ℝ => ν * (Real.exp r - 1)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc' : Continuous (fun r : ℝ => ν * (Real.exp r - 1)) :=
        continuous_const.mul (Real.continuous_exp.sub continuous_const)
      have := (hc'.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : (0 : ℝ) < r := hr
      exact mul_pos hν (by linarith [Real.add_one_lt_exp hr0.ne'])
  have ha : Tendsto (fun r : ℝ => Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹)
      (𝓝[>] 0) (𝓝 ν) := by
    have he : (fun r : ℝ => Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹) =
        fun r => Real.exp (r / 2) * ν * (r⁻¹ * (Real.exp r - 1)) := by
      funext r
      ring
    rw [he]
    have := (hlam.mul (tendsto_const_nhds (x := ν))).mul tendsto_exp_slope
    simpa using this
  have hb := tendsto_halfexp_slope
  have hX1 := (tendsto_heat_generator hp1 hp hs hc).comp htau
  have hX2 := (tendsto_dilation hp1 hp hLp).comp hlam
  have hX4 := (tendsto_dilation hp1 hp hhp).comp hlam
  have hX6 := tendsto_dilation_generator hp1 hp hs hc
  have hea := (continuous_enorm.tendsto ν).comp ha
  have hea' : Tendsto (fun r : ℝ => ‖Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹ - ν‖ₑ)
      (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => Real.exp (r / 2) * (ν * (Real.exp r - 1)) * r⁻¹ - ν)
        (𝓝[>] 0) (𝓝 0) := by simpa using ha.sub_const ν
    have := (continuous_enorm.tendsto (0 : ℝ)).comp h0
    rw [enorm_zero] at this
    exact this
  have heb := (continuous_enorm.tendsto (1 / 2 : ℝ)).comp hb
  have heb' : Tendsto (fun r : ℝ => ‖r⁻¹ * (Real.exp (r / 2) - 1) - 1 / 2‖ₑ)
      (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => r⁻¹ * (Real.exp (r / 2) - 1) - 1 / 2) (𝓝[>] 0) (𝓝 0) := by
      simpa using hb.sub_const (1 / 2)
    have := (continuous_enorm.tendsto (0 : ℝ)).comp h0
    rw [enorm_zero] at this
    exact this
  have hP1 := ENNReal.Tendsto.mul hea (Or.inr ENNReal.zero_ne_top) hX1 (Or.inr enorm_ne_top)
  have hP2 := ENNReal.Tendsto.mul hea (Or.inr ENNReal.zero_ne_top) hX2 (Or.inr enorm_ne_top)
  have hP3 := ENNReal.Tendsto.mul_const hea' (Or.inr hLp.2.ne)
  have hP4 := ENNReal.Tendsto.mul heb (Or.inr ENNReal.zero_ne_top) hX4 (Or.inr enorm_ne_top)
  have hP5 := ENNReal.Tendsto.mul_const heb' (Or.inr hhp.2.ne)
  have hsum := ((((hP1.add hP2).add hP3).add hP4).add hP5).add hX6
  rw [show (‖ν‖ₑ * 0 + ‖ν‖ₑ * 0 + 0 * eLpNorm (vecLaplacian h) p volume +
      ‖(1 / 2 : ℝ)‖ₑ * 0 + 0 * eLpNorm h p volume + 0 : ℝ≥0∞) = 0 by simp] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0 : ℝ) < r := hr
  have hτ0 : 0 < ν * (Real.exp r - 1) := mul_pos hν (by linarith [Real.add_one_lt_exp hr0.ne'])
  exact eLpNorm_quotient_le hr0 hτ0 hp1 hp hs hc

end UnforcedLeray.B0418
