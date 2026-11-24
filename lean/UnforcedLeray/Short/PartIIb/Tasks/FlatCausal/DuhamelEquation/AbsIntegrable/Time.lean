import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Reduction

/-!
# Part II-b, task `PartII-b:T12/7/7/3` (`DeqAbsTime`): time integrability

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

Hölder in `t` against the `H_r` weight `s^{r/2-5/2}`. With `a = r/2 - 5/2`, the slice norm
`eLpNorm (G (t, ·)) r` equals `(∫ ‖G‖^r dCyl)^{1/r}`; writing `t^{μ-1} = t^{μ-1-a/r} · t^{a/r}`,
Hölder with exponents `r` and `r/(r-1)` bounds the time integral by the finite `H_r` energy times
`∫_{(0,H)} t^{(μ-1-a/r)·r/(r-1)}`, which is finite exactly when `Re μ + (3/r - 1)/2 > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

instance deqat_sFinite_avg (c : ℝ) : SFinite (UnforcedLeray.Cyl.avgμ c) := by
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  infer_instance

/-- Slice `L^r` energy of `g` at age `t`, in lintegral form (so `eLpNorm = (deqatFg)^{1/r}`). -/
def deqatFg (c r : ℝ) (g : CProf) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ℝ × ℝ, ‖g (t, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c)

theorem deqatFg_measurable (c r : ℝ) {g : CProf} (hg : Measurable g) :
    Measurable (deqatFg c r g) := by
  unfold deqatFg
  exact Measurable.lintegral_prod_right' (f := fun p : ℝ × (ℝ × ℝ) => ‖g p‖ₑ ^ r)
    (hg.enorm.pow_const r)

/-- The `H_r` energy splits as an age integral of the slice energies. -/
theorem deqat_split (c r : ℝ) {g : CProf} (hg : Measurable g) :
    ∫⁻ p, ‖g p‖ₑ ^ r ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * deqatFg c r g t := by
  unfold UnforcedLeray.Axi.ageμ
  rw [lintegral_prod (fun p : ℝ × (ℝ × ℝ) => ‖g p‖ₑ ^ r) (hg.enorm.pow_const r).aemeasurable]
  exact lintegral_withDensity_eq_lintegral_mul _
    (UnforcedLeray.Axi.measurable_ofReal_rpow _) (deqatFg_measurable c r hg)

/-- For a.e. age `t > 0`, the `L^r(avgμ)` slice norm of `G` is the slice energy of a measurable
representative `g`, raised to `1/r`. -/
theorem deqat_slice_eq (c r : ℝ) (hr0 : 0 < r) {G g : CProf}
    (hGg : G =ᵐ[UnforcedLeray.Short.IIb.hMeas c r] g) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) =
        deqatFg c r g t ^ (1 / r) := by
  have hG' : ∀ᵐ p ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)), G p = g p := hGg
  unfold UnforcedLeray.Axi.ageμ at hG'
  have h1 := Measure.ae_ae_of_ae_prod hG'
  have h2 := (ae_withDensity_iff (UnforcedLeray.Axi.measurable_ofReal_rpow _)).1 h1
  filter_upwards [h2, ae_restrict_mem measurableSet_Ioi] with t ht hmem
  have hpos : ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hmem _)).ne'
  have hz : (fun z : ℝ × ℝ => G (t, z)) =ᵐ[UnforcedLeray.Cyl.avgμ c]
      (fun z : ℝ × ℝ => g (t, z)) := ht hpos
  rw [eLpNorm_congr_ae hz, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr0.le]
  rfl

/-- Pointwise identity behind the Hölder split. -/
theorem deqat_pointwise (r : ℝ) (hr0 : 0 < r) (m : ℝ) {t : ℝ} (ht : 0 < t) (F : ℝ≥0∞) :
    ENNReal.ofReal (t ^ m) * F ^ (1 / r) =
      ENNReal.ofReal (t ^ (m - (r / 2 - 5 / 2) / r)) *
        (ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * F) ^ (1 / r) := by
  have key : t ^ m = t ^ (m - (r / 2 - 5 / 2) / r) * (t ^ (r / 2 - 5 / 2)) ^ (1 / r) := by
    rw [← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    congr 1
    ring
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hr0.le),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.le _) (one_div_nonneg.2 hr0.le), key,
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), mul_assoc]

/-- Integrability of a power weight on `(0, H)`, in lintegral form. -/
theorem deqat_int (H e q : ℝ) (hH : 0 < H) (hq : 0 ≤ q) (hexp : -1 < e * q) :
    ∫⁻ t in Ioo (0 : ℝ) H, (ENNReal.ofReal (t ^ e)) ^ q < ⊤ := by
  have hpt : (fun t : ℝ => (ENNReal.ofReal (t ^ e)) ^ q) =ᵐ[volume.restrict (Ioo (0 : ℝ) H)]
      (fun t : ℝ => ENNReal.ofReal (t ^ (e * q))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.1.le _) hq, ← Real.rpow_mul ht.1.le]
  rw [lintegral_congr_ae hpt]
  have hint : IntegrableOn (fun t : ℝ => t ^ (e * q)) (Ioo (0 : ℝ) H) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hH).2 hexp
  exact Integrable.lintegral_lt_top hint

/-- **Time integrability (`DeqAbsTime`).** -/
theorem deqAbsTime : DeqAbsTime := by
  intro r hr1 hr3 μ hμ c hc G hG H
  have hr0 : 0 < r := by linarith
  rcases le_or_gt H 0 with hH0 | hHpos
  · rw [Set.Ioo_eq_empty (not_lt.2 hH0)]
    simp
  obtain ⟨g, hgm, hGg⟩ : ∃ g : CProf, Measurable g ∧ G =ᵐ[hMeas c r] g :=
    ⟨hG.meas.mk G, hG.meas.stronglyMeasurable_mk.measurable, hG.meas.ae_eq_mk⟩
  have hG' : ∀ᵐ p ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)), G p = g p := hGg
  have hfinG : ∫⁻ p, ‖G p‖ₑ ^ r ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (μ := UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) (p := ENNReal.ofReal r) (f := G)
      (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top hG.finite
    rwa [ENNReal.toReal_ofReal hr0.le] at h
  have hgfin : ∫⁻ p, ‖g p‖ₑ ^ r ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) < ⊤ := by
    have heq : ∫⁻ p, ‖g p‖ₑ ^ r ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) =
        ∫⁻ p, ‖G p‖ₑ ^ r ∂(UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)) :=
      lintegral_congr_ae (hG'.mono fun p hp => by simp only [hp])
    rw [heq]
    exact hfinG
  rw [deqat_split c r hgm] at hgfin
  have hslice' : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) H)),
      eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) =
        deqatFg c r g t ^ (1 / r) :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self (deqat_slice_eq c r hr0 hGg)
  have hcongr : ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (μ.re - 1)) *
        eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) =
      ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (μ.re - 1 - (r / 2 - 5 / 2) / r)) *
        (ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * deqatFg c r g t) ^ (1 / r) := by
    apply lintegral_congr_ae
    filter_upwards [hslice', ae_restrict_mem measurableSet_Ioo] with t ht htm
    rw [ht, deqat_pointwise r hr0 (μ.re - 1) htm.1 (deqatFg c r g t)]
  rw [hcongr]
  have hrne : r ≠ 0 := hr0.ne'
  have hr1ne : (0 : ℝ) < r - 1 := by linarith
  have hpq : r.HolderConjugate (r / (r - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent (by linarith)).2 rfl
  have hq0 : 0 ≤ r / (r - 1) := div_nonneg hr0.le hr1ne.le
  have hexp : -1 < (μ.re - 1 - (r / 2 - 5 / 2) / r) * (r / (r - 1)) := by
    have h1 : (μ.re - 1 - (r / 2 - 5 / 2) / r) * (r / (r - 1)) + 1 =
        r * (μ.re + (3 / r - 1) / 2) / (r - 1) := by
      field_simp
      ring
    have h2 : 0 < r * (μ.re + (3 / r - 1) / 2) / (r - 1) :=
      div_pos (mul_pos hr0 hμ) hr1ne
    linarith
  have hU : Measurable (fun t : ℝ =>
      (ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * deqatFg c r g t) ^ (1 / r)) :=
    ((UnforcedLeray.Axi.measurable_ofReal_rpow _).mul (deqatFg_measurable c r hgm)).pow_const _
  have hW : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (μ.re - 1 - (r / 2 - 5 / 2) / r))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hH : ∫⁻ t in Ioo (0 : ℝ) H,
      ((ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * deqatFg c r g t) ^ (1 / r)) *
        ENNReal.ofReal (t ^ (μ.re - 1 - (r / 2 - 5 / 2) / r))
      ≤ (∫⁻ t in Ioo (0 : ℝ) H,
          (((ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * deqatFg c r g t) ^ (1 / r)) ^ r)) ^ (1 / r) *
        (∫⁻ t in Ioo (0 : ℝ) H, (ENNReal.ofReal (t ^ (μ.re - 1 - (r / 2 - 5 / 2) / r))) ^
          (r / (r - 1))) ^ (1 / (r / (r - 1))) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioo (0 : ℝ) H)) hpq
      hU.aemeasurable hW.aemeasurable
  have hUr : ∀ t : ℝ, ((ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * deqatFg c r g t) ^ (1 / r)) ^ r =
      ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * deqatFg c r g t := by
    intro t
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hrne, ENNReal.rpow_one]
  have hint1 : ∫⁻ t in Ioo (0 : ℝ) H,
      (((ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * deqatFg c r g t) ^ (1 / r)) ^ r) < ⊤ := by
    simp only [hUr]
    exact lt_of_le_of_lt (lintegral_mono_set Ioo_subset_Ioi_self) hgfin
  have hint2 := deqat_int H (μ.re - 1 - (r / 2 - 5 / 2) / r) (r / (r - 1)) hHpos hq0 hexp
  have hfinal : (∫⁻ t in Ioo (0 : ℝ) H,
          (((ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * deqatFg c r g t) ^ (1 / r)) ^ r)) ^ (1 / r) *
        (∫⁻ t in Ioo (0 : ℝ) H, (ENNReal.ofReal (t ^ (μ.re - 1 - (r / 2 - 5 / 2) / r))) ^
          (r / (r - 1))) ^ (1 / (r / (r - 1))) < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.2 hr0.le) hint1.ne)
      (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.2 hq0) hint2.ne)
  calc ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (μ.re - 1 - (r / 2 - 5 / 2) / r)) *
        (ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * deqatFg c r g t) ^ (1 / r)
      = ∫⁻ t in Ioo (0 : ℝ) H,
          ((ENNReal.ofReal (t ^ (r / 2 - 5 / 2)) * deqatFg c r g t) ^ (1 / r)) *
            ENNReal.ofReal (t ^ (μ.re - 1 - (r / 2 - 5 / 2) / r)) :=
        lintegral_congr fun t => mul_comm _ _
    _ ≤ _ := hH
    _ < ⊤ := hfinal

end UnforcedLeray.Short.IIb
