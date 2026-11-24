import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1

/-!
# Helpers for leaves `T11/2/1/1` (`DualFMeas`) and `T11/2/1/2` (`DualFPointwise`)

Source: `the November 2 reference manuscript` 1923-1927.

* `slice_aestronglyMeasurable`: for `b ∈ H_r`, a.e. `σ > 0`, `p ↦ b (σ, p)` is a.e.-strongly
  measurable for `avgμ c`;
* `b_aestronglyMeasurable_prod`: `b` is a.e.-strongly measurable for `dσ|_{(0,s)} ⊗ avgμ c`;
* `perpGradH_continuousOn`: `(σ, p) ↦ ∇^⊥ H(s-σ, ·)(p)` is continuous for `σ < s`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem sfinite_avgμ (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ Cyl.cellμ
  infer_instance

/-- `age`-measure is `dσ·σ^e ⊗ avgμ`; a.e. slices of `b` are measurable. -/
theorem slice_aestronglyMeasurable {c r : ℝ} {b : CProf} (hc : 0 < c) (hb : InHr c r b) :
    ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))),
      AEStronglyMeasurable (fun p : ℝ × ℝ => b (σ, p)) (Cyl.avgμ c) := by
  set e : ℝ := r / 2 - 5 / 2 with he
  have hb' : AEStronglyMeasurable b (Axi.ageμ c e) := hb.meas
  set g : Coord → CMerid := hb'.mk b with hgdef
  have hg : Measurable g := hb'.stronglyMeasurable_mk.measurable
  have hbg : b =ᵐ[Axi.ageμ c e] g := hb'.ae_eq_mk
  have h3 : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ e)).prod (Cyl.avgμ c), b z = g z := by
    unfold Axi.ageμ at hbg
    exact hbg
  have : SFinite (Cyl.avgμ c) := sfinite_avgμ c
  have h4 := Measure.ae_ae_of_ae_prod h3
  have hw : AEMeasurable (fun s : ℝ => ENNReal.ofReal (s ^ e))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const e)).aemeasurable
  have hne : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ENNReal.ofReal (s ^ e) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs e)).ne'
  have h5 := (withDensity_absolutelyContinuous' hw hne).ae_le h4
  filter_upwards [h5] with σ hσ
  have hm : Measurable (fun p : ℝ × ℝ => g (σ, p)) := hg.comp measurable_prodMk_left
  exact hm.aestronglyMeasurable.congr (hσ.mono fun x hx => hx.symm)

/-- `b` is a.e.-strongly measurable for `dσ|_{(0,s)} ⊗ avgμ`. -/
theorem b_aestronglyMeasurable_prod {c r : ℝ} {b : CProf} (hc : 0 < c) (hb : InHr c r b)
    (s : ℝ) :
    AEStronglyMeasurable b ((volume.restrict (Ioo (0 : ℝ) s)).prod (Cyl.avgμ c)) := by
  set e : ℝ := r / 2 - 5 / 2 with he
  have hb' : AEStronglyMeasurable b (Axi.ageμ c e) := hb.meas
  have : SFinite (Cyl.avgμ c) := sfinite_avgμ c
  have hw : AEMeasurable (fun s : ℝ => ENNReal.ofReal (s ^ e))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const e)).aemeasurable
  have hne : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ENNReal.ofReal (s ^ e) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs e)).ne'
  have h1 : volume.restrict (Ioo (0 : ℝ) s) ≪
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ e) :=
    (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl).absolutelyContinuous.trans
      (withDensity_absolutelyContinuous' hw hne)
  have h2 := h1.prod (Measure.AbsolutelyContinuous.refl (Cyl.avgμ c))
  unfold Axi.ageμ at hb'
  exact hb'.mono_ac h2

/-- Chain rule for slices: `∂ ζ(t,·) (p) v = (fderiv H (t,p)) (0,v)` for `t > 0`. -/
theorem fderiv_slice {H : Coord → ℝ} (hH : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    {t : ℝ} (ht : 0 < t) (p v : ℝ × ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => H (t, z)) p v = fderiv ℝ H (t, p) (0, v) := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hd : DifferentiableAt ℝ H (t, p) :=
    ((hH.contDiffAt (hopen.mem_nhds (by simp [ht]))).differentiableAt (by simp))
  have h1 := hd.hasFDerivAt.comp p (hasFDerivAt_prodMk_right (𝕜 := ℝ) t p)
  have h2 : fderiv ℝ (fun z : ℝ × ℝ => H (t, z)) p = _ := h1.fderiv
  rw [h2]
  simp

theorem perpGradH_continuousOn {H : Coord → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (s : ℝ) (i : Fin 2) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => perpGrad (fun z => H (s - q.1, z)) q.2 i)
      {q | q.1 < s} := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hF : ContinuousOn (fderiv ℝ H) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hH.continuousOn_fderiv_of_isOpen hopen (by simp)
  have hmap : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (s - q.1, q.2)) {q | q.1 < s} :=
    (by fun_prop : Continuous fun q : ℝ × (ℝ × ℝ) => (s - q.1, q.2)).continuousOn
  have hmaps : MapsTo (fun q : ℝ × (ℝ × ℝ) => (s - q.1, q.2)) {q | q.1 < s}
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro q hq
    simp only [mem_ofPred_eq] at hq
    simp [hq]
  have hc := hF.comp hmap hmaps
  have hv : ∀ v : Coord, ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      fderiv ℝ H (s - q.1, q.2) v) {q | q.1 < s} := fun v =>
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn hc
  have key : ∀ (v : ℝ × ℝ), ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun z : ℝ × ℝ => H (s - q.1, z)) q.2 v) {q | q.1 < s} := by
    intro v
    refine (hv (0, v)).congr ?_
    intro q hq
    simp only [mem_ofPred_eq] at hq
    exact fderiv_slice hH (by linarith) q.2 v
  fin_cases i
  · simpa [perpGrad] using key (0, 1)
  · refine ContinuousOn.congr (key (1, 0)).neg ?_
    intro q _
    simp [perpGrad]

end UnforcedLeray.Short.IIb
