import UnforcedLeray.Short.PartIIb.Sub.T12_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable.Periodic

/-!
# Part II-b, task `PartII-b:T12/7/1` (`DeqSliceAe`): a.e. Fubini slices of `H_r` are good

Source of record: `the November 2 reference manuscript`, lines 1900-1903 (the
measure `s^{r/2-5/2} ds dq/c dη` of `H_r`) and 1923-1927.

Statement: `DeqSliceAe` (`Sub/T12_7.lean`): for `0 < c`, `1 < r`, `G ∈ H_r`, for a.e. `t > 0` the
slice `G(t, ·)` is `DeqSliceGood c r`, i.e. (a) it is a.e. `c`-periodic in `q`, (b) it is a.e.
strongly measurable on the plane, (c) it has finite `L^r(Cyl.avgμ c)` norm.

Proof outline:
1. `exists_periodic_rep` gives a strongly measurable `G'` with `G = G'` Lebesgue-a.e. on `{s > 0}`.
2. Fubini (`Measure.ae_ae_of_ae_prod`) gives, for a.e. `t > 0`, `G(t, ·) = G'(t, ·)` a.e. on the plane,
   hence (b); the periodicity (a) of `G` is transferred to slices by the same Fubini step.
3. `G = G'` holds `ageμ`-a.e. (since `ageμ = volume.withDensity (dens c a)` and `dens ≠ 0` only on
   `{s > 0}`), so `∫⁻ ‖G'‖ₑ^r dageμ < ∞`. Writing `ageμ` as `(s-measure).withDensity ⊗ avgμ` and
   applying `lintegral_prod` and `lintegral_withDensity_eq_lintegral_mul` gives
   `∫⁻ s, s^a * N(s) ds < ∞` with `N(s) = ∫⁻ ‖G'(s,·)‖ₑ^r davgμ`; hence `N(s) < ∞` for a.e. `s > 0`.
4. Fubini again (`ageμ`-a.e. equality restricted to the `avgμ` slices) gives `G(s,·) = G'(s,·)` `avgμ`-a.e.
   for a.e. `s > 0`, which transfers the finiteness of `N(s)` to `G(s, ·)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

instance deqsa_sFinite_avgμ (c : ℝ) : SFinite (UnforcedLeray.Cyl.avgμ c) := by
  unfold UnforcedLeray.Cyl.avgμ
  have := UnforcedLeray.Axi.sFinite_cellμ c
  infer_instance

/-- `dens c a x ≠ 0` forces `0 < x.1`. -/
theorem deqsa_pos_of_dens {c a : ℝ} {x : Coord} (h : dens c a x ≠ 0) : 0 < x.1 := by
  by_contra hneg
  apply h
  have hx : x ∉ Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c := fun hx => hneg hx.1
  unfold dens
  rw [Set.indicator_of_notMem hx, mul_zero]

/-- Slice finiteness (Tonelli in the age measure): for a strongly measurable `G'` with finite
`H_r` norm, `∫⁻ ‖G'(s,·)‖ₑ^r davgμ < ∞` for a.e. `s > 0`. -/
theorem deqsa_slice_lt_top {c r : ℝ} (_hc : 0 < c) (hr : 1 < r) {G' : CProf}
    (hG's : StronglyMeasurable G')
    (hfin : eLpNorm G' (ENNReal.ofReal r) (UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫⁻ z, ‖G' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) < ⊤ := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hI : ∫⁻ p, ‖G' p‖ₑ ^ r ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top).1 hfin
    rwa [ENNReal.toReal_ofReal hr0.le] at h
  have hmG : Measurable (fun p : ℝ × (ℝ × ℝ) => ‖G' p‖ₑ ^ r) :=
    (hG's.measurable.enorm).pow_const r
  have hgm : Measurable (fun s : ℝ => ∫⁻ z, ‖G' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c)) :=
    hmG.lintegral_prod_right'
  have hI2 : ∫⁻ s, ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
      ∫⁻ z, ‖G' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) ∂(volume.restrict (Ioi (0 : ℝ))) ≠ ⊤ := by
    have e : ∫⁻ p, ‖G' p‖ₑ ^ r ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) =
        ∫⁻ s, ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
          ∫⁻ z, ‖G' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c) ∂(volume.restrict (Ioi (0 : ℝ))) := by
      rw [UnforcedLeray.Axi.ageμ, lintegral_prod _ hmG.aemeasurable,
        lintegral_withDensity_eq_lintegral_mul _ (UnforcedLeray.Axi.measurable_ofReal_rpow _) hgm]
      rfl
    rw [← e]
    exact hI.ne
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ (r / 2 - 5 / 2)) *
      ∫⁻ z, ‖G' (s, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c)) :=
    (UnforcedLeray.Axi.measurable_ofReal_rpow _).mul hgm
  filter_upwards [ae_lt_top' hm.aemeasurable hI2, ae_restrict_mem measurableSet_Ioi] with s hs hsp
  rcases ENNReal.mul_lt_top_iff.1 hs with ⟨_, h2⟩ | h0 | h0
  · exact h2
  · exact absurd h0 (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hsp _)).ne'
  · rw [h0]
    exact ENNReal.zero_lt_top

/-- **Leaf `PartII-b:T12/7/1`** (Fubini slices of `H_r`; SP 1900-1903, 1923-1927). For `G ∈ H_r`,
for a.e. `t > 0` the slice `G(t, ·)` is `DeqSliceGood`. -/
theorem deqSliceAe : UnforcedLeray.Short.IIb.DeqSliceAe := by
  unfold DeqSliceAe
  intro c r G hc hr hG
  obtain ⟨G', hG's, hGG'⟩ :=
    exists_periodic_rep (a := r / 2 - 5 / 2) hc hG.periodic hG.meas
  -- `G = G'` for the age measure
  have hGGa : ∀ᵐ x ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)), G x = G' x := by
    rw [ageμ_eq_withDensity hc (r / 2 - 5 / 2), ae_withDensity_iff (measurable_dens c (r / 2 - 5 / 2))]
    filter_upwards [hGG'] with x hx hdens
    exact hx (deqsa_pos_of_dens hdens)
  have hGGa2 : G =ᵐ[UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)] G' := hGGa
  -- finiteness of the norm of `G'`
  have hfinG' : eLpNorm G' (ENNReal.ofReal r) (UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) < ⊤ := by
    rw [← eLpNorm_congr_ae hGGa2]
    exact hG.finite
  have hfin := deqsa_slice_lt_top hc hr hG's hfinG'
  -- avgμ-a.e. equality of slices, for a.e. s > 0
  have hGGa' : ∀ᵐ x ∂(((volume.restrict (Ioi (0 : ℝ))).withDensity fun s =>
      ENNReal.ofReal (s ^ (r / 2 - 5 / 2))).prod (UnforcedLeray.Cyl.avgμ c)), G x = G' x := hGGa
  have hsl := (ae_withDensity_iff (p := fun s : ℝ =>
      ∀ᵐ z ∂(UnforcedLeray.Cyl.avgμ c), G (s, z) = G' (s, z))
      (UnforcedLeray.Axi.measurable_ofReal_rpow _)).1 (Measure.ae_ae_of_ae_prod hGGa')
  have hslice_avg : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ z ∂(UnforcedLeray.Cyl.avgμ c), G (s, z) = G' (s, z) := by
    filter_upwards [hsl, ae_restrict_mem measurableSet_Ioi] with s hs hsp
    exact hs (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hsp _)).ne'
  -- Lebesgue-a.e. equality of slices on the plane, for a.e. s > 0
  have hslice_vol : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), G (s, z) = G' (s, z) := by
    have h' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))),
        0 < x.1 → G x = G' x := hGG'
    have h2 := ae_restrict_of_ae (s := Ioi (0 : ℝ)) (Measure.ae_ae_of_ae_prod h')
    filter_upwards [h2, ae_restrict_mem measurableSet_Ioi] with s hs hsp
    filter_upwards [hs] with z hz
    exact hz hsp
  -- periodicity of the slices, for a.e. s
  have hslice_per : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), G (s, (z.1 + c, z.2)) = G (s, z) := by
    -- `QPeriodic` is the a.e. identity on `s > 0`
    have hP : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))),
        0 < x.1 → G (qShift c x) = G x := QPerHalf.ae_imp hG.periodic
    have h2 := ae_restrict_of_ae (s := Ioi (0 : ℝ)) (Measure.ae_ae_of_ae_prod hP)
    filter_upwards [h2, ae_restrict_mem measurableSet_Ioi] with s hs hsp
    filter_upwards [hs] with z hz
    exact hz hsp
  filter_upwards [hslice_per, hslice_vol, hslice_avg, hfin] with s hp hv ha hf
  have hv' : (fun z : ℝ × ℝ => G (s, z)) =ᵐ[volume] (fun z => G' (s, z)) := hv
  have ha' : (fun z : ℝ × ℝ => G (s, z)) =ᵐ[UnforcedLeray.Cyl.avgμ c] (fun z => G' (s, z)) := ha
  unfold DeqSliceGood
  refine ⟨hp, ?_, ?_⟩
  · exact (hG's.comp_measurable measurable_prodMk_left).aestronglyMeasurable.congr hv'.symm
  · rw [eLpNorm_congr_ae ha',
      eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (ENNReal.ofReal_pos.2 (by linarith)).ne'
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)]
    exact hf

end UnforcedLeray.Short.IIb
