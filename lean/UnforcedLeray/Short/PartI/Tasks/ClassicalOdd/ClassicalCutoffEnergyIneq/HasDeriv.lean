import UnforcedLeray.Short.PartI.Sub.T02_3_11

/-!
# Part I, task `PartI:T02/3/11`: `CcEnergyHasDeriv` (differentiation under the integral)

Target: `theorem ccEnergyHasDeriv : CcEnergyHasDeriv`, the leaf `CcEnergyHasDeriv` of
`Short/PartI/Sub/T02_3_11.lean` (line 196).

Source of record: `the November 2 reference manuscript`, lines 276-288.

## Proof

Write `W(t, z) = v t z - v' t z`.  On the open set `(0, T) × ℝ²` the map `W` is `C^∞`, so for
`t ∈ (0, T)` and each `z` the map `t ↦ W(t, z)` has derivative `fderiv W (t, z) (1, 0)` at `t`, and
`(t, z) ↦ 2⟨W, fderiv W (t, z) (1, 0)⟩` is continuous there.  Differentiation under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) on the neighbourhood
`Icc (t0/2) ((t0+T)/2)` of `t0 ∈ (0, T)` uses:

* domination: the derivative integrand is bounded by a constant on the compact box
  `Icc (-c) c ×ˢ Icc (-2R) (2R)` (continuity on the compact `Icc (t0/2) ((t0+T)/2) ×ˢ box`), and it
  vanishes for `|η| ≥ 2R` because `etaCutoff R η = 0` there;
* integrability of the value at `t0` on the cell, by the same bound.

The lemmas `ccEH_*` are copies of the proved train lemmas `cehd_*`
(`Short/PartI/Tasks/TrainCutoffEnergyProof/HasDeriv.lean`), with the open set `Ioi 0 ×ˢ univ`
replaced by `Ioo 0 T ×ˢ univ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Facts about the transverse cutoff `etaCutoff` -/

theorem ccEH_eta_cont (R : ℝ) : Continuous (fun z : Plane => etaCutoff R z.2) := by
  unfold etaCutoff
  have h1 : Continuous (fun z : Plane => 2 - |z.2| / R) :=
    continuous_const.sub ((continuous_abs.comp continuous_snd).div_const R)
  exact (Real.smoothTransition.continuous.comp h1).pow 2

theorem ccEH_eta_le_one (R η : ℝ) : etaCutoff R η ≤ 1 := by
  unfold etaCutoff
  exact pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem ccEH_eta_zero (R η : ℝ) (hR : 0 < R) (h : 2 * R ≤ |η|) : etaCutoff R η = 0 := by
  unfold etaCutoff
  have hle : 2 - |η| / R ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hR]
    exact h
  rw [Real.smoothTransition.zero_of_nonpos hle]
  norm_num

/-! ### The compact box and the cell -/

/-- A compact box containing the cell intersected with the strip `|η| ≤ 2R`. -/
def ccEHBox (c R : ℝ) : Set Plane := Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R)

theorem ccEH_box_compact (c R : ℝ) : IsCompact (ccEHBox c R) :=
  isCompact_Icc.prod isCompact_Icc

theorem ccEH_cell_measurable (c : ℝ) : MeasurableSet (Cyl.cell c) := by
  unfold Cyl.cell
  exact measurableSet_Ico.prod MeasurableSet.univ

/-- A point of the cell outside the box lies outside the strip `|η| ≤ 2R`. -/
theorem ccEH_outside_box (c R : ℝ) (hc : 0 < c) (z : Plane) (hz : z ∈ Cyl.cell c)
    (hm : z ∉ ccEHBox c R) : 2 * R ≤ |z.2| := by
  by_contra hlt
  have hlt' : |z.2| < 2 * R := not_le.1 hlt
  apply hm
  have hq : -c / 2 ≤ z.1 ∧ z.1 < c / 2 := hz.1
  exact ⟨⟨by linarith [hq.1], by linarith [hq.2]⟩, abs_le.1 hlt'.le⟩

theorem ccEH_bound_integrable (c R C : ℝ) :
    Integrable ((ccEHBox c R).indicator (fun _ : Plane => C)) (volume.restrict (Cyl.cell c)) := by
  rw [integrable_indicator_iff (ccEH_box_compact c R).isClosed.measurableSet]
  refine integrableOn_const ?_
  rw [Measure.restrict_apply (ccEH_box_compact c R).isClosed.measurableSet]
  exact ne_top_of_le_ne_top (ccEH_box_compact c R).measure_lt_top.ne
    (measure_mono inter_subset_left)

/-- A continuous function on the plane vanishing on `|η| ≥ 2R` is integrable on the cell. -/
theorem ccEH_integrableOn_cell (c R : ℝ) (hc : 0 < c) (g : Plane → ℝ) (hg : Continuous g)
    (hsupp : ∀ z : Plane, 2 * R ≤ |z.2| → g z = 0) : IntegrableOn g (Cyl.cell c) := by
  obtain ⟨C, hC⟩ := (ccEH_box_compact c R).exists_bound_of_continuousOn hg.continuousOn
  refine Integrable.mono' (ccEH_bound_integrable c R (max C 0)) hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (ccEH_cell_measurable c)] with z hz
  by_cases hm : z ∈ ccEHBox c R
  · rw [Set.indicator_of_mem hm]
    exact (hC z hm).trans (le_max_left _ _)
  · rw [hsupp z (ccEH_outside_box c R hc z hz hm), norm_zero]
    exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) z

/-! ### Calculus of the velocity difference -/

theorem ccEH_open (T : ℝ) : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
  isOpen_Ioo.prod isOpen_univ

/-- For `t ∈ (0, T)` the `t`-derivative of `W(·, z)` is the `(1, 0)`-derivative of `W`. -/
theorem ccEH_deriv_at {T : ℝ} {W : ℝ × Plane → Vec} (hW : ContDiffOn ℝ ∞ W (Ioo 0 T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (z : Plane) :
    HasDerivAt (fun u => W (u, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))) t := by
  have hmem : (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) ∈ 𝓝 (t, z) :=
    (ccEH_open T).mem_nhds (Set.mk_mem_prod ht (mem_univ z))
  have hF : HasFDerivAt W (fderiv ℝ W (t, z)) (t, z) :=
    ((hW.contDiffAt hmem).differentiableAt (by simp)).hasFDerivAt
  have hg : HasDerivAt (fun u : ℝ => (u, z)) ((1 : ℝ), (0 : Plane)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t z)
  exact hF.comp_hasDerivAt t hg

/-- The continuous function `(t, z) ↦ 2⟨W, ∂_t W⟩` on `(0, T) × ℝ²`. -/
theorem ccEH_cont_G {T : ℝ} {W : ℝ × Plane → Vec} (hW : ContDiffOn ℝ ∞ W (Ioo 0 T ×ˢ univ)) :
    ContinuousOn (fun x : ℝ × Plane => 2 * inner ℝ (W x) (fderiv ℝ W x ((1 : ℝ), (0 : Plane))))
      (Ioo 0 T ×ˢ univ) := by
  have h2 : ContinuousOn (fderiv ℝ W) (Ioo 0 T ×ˢ univ) :=
    hW.continuousOn_fderiv_of_isOpen (ccEH_open T) (by simp)
  have h3 : ContinuousOn (fun x : ℝ × Plane => fderiv ℝ W x ((1 : ℝ), (0 : Plane)))
      (Ioo 0 T ×ˢ univ) :=
    h2.clm_apply continuousOn_const
  exact continuousOn_const.mul (hW.continuousOn.inner h3)

/-! ### The generic differentiation under the integral sign -/

theorem ccEH_generic {T : ℝ} {W : ℝ × Plane → Vec} (hW : ContDiffOn ℝ ∞ W (Ioo 0 T ×ˢ univ))
    (c R : ℝ) (hc : 0 < c) (hR : 0 < R) (t0 : ℝ) (ht0 : 0 < t0) (ht0T : t0 < T) :
    HasDerivAt (fun t => ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖W (t, z)‖ ^ 2)
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * inner ℝ (W (t0, z)) (fderiv ℝ W (t0, z) ((1 : ℝ), (0 : Plane))))) t0 := by
  have hG := ccEH_cont_G hW
  have ht0I : t0 ∈ Ioo 0 T := ⟨ht0, ht0T⟩
  -- the neighbourhood `Icc (t0/2) ((t0+T)/2)` of `t0` lies in `(0, T)`
  have hJ_sub : Icc (t0 / 2) ((t0 + T) / 2) ⊆ Ioo 0 T := fun t ht =>
    ⟨lt_of_lt_of_le (by linarith) ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩
  -- continuity in `z` of the slices, for `t ∈ (0, T)`
  have hslice : ∀ t ∈ Ioo (0 : ℝ) T, Continuous (fun z : Plane => W (t, z)) := fun t ht =>
    hW.continuousOn.comp_continuous (f := fun z : Plane => (t, z)) (by fun_prop)
      (fun z => Set.mk_mem_prod ht (mem_univ z))
  -- the compact set of `(t, z)` on which the derivative is bounded
  have hKt : IsCompact (Icc (t0 / 2) ((t0 + T) / 2) ×ˢ ccEHBox c R) :=
    isCompact_Icc.prod (ccEH_box_compact c R)
  have hKt_sub : Icc (t0 / 2) ((t0 + T) / 2) ×ˢ ccEHBox c R ⊆ Ioo 0 T ×ˢ (univ : Set Plane) := by
    intro x hx
    exact Set.mk_mem_prod (hJ_sub hx.1) (mem_univ _)
  obtain ⟨Cg, hCg⟩ := hKt.exists_bound_of_continuousOn (hG.mono hKt_sub)
  -- the domination bound
  have hbound : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)), ∀ t ∈ Icc (t0 / 2) ((t0 + T) / 2),
      ‖etaCutoff R z.2 * (2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))))‖ ≤
        (ccEHBox c R).indicator (fun _ : Plane => max Cg 0) z := by
    filter_upwards [ae_restrict_mem (ccEH_cell_measurable c)] with z hz
    intro t ht
    by_cases hm : z ∈ ccEHBox c R
    · rw [Set.indicator_of_mem hm]
      have hg : ‖2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)))‖ ≤ Cg :=
        hCg (t, z) (Set.mk_mem_prod ht hm)
      have h1 : ‖etaCutoff R z.2‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (etaCutoff_nonneg R z.2)]
        exact ccEH_eta_le_one R z.2
      calc ‖etaCutoff R z.2 * (2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))))‖
          = ‖etaCutoff R z.2‖ *
              ‖2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)))‖ := norm_mul _ _
        _ ≤ 1 * Cg := mul_le_mul h1 hg (norm_nonneg _) zero_le_one
        _ ≤ max Cg 0 := by rw [one_mul]; exact le_max_left _ _
    · have hz2 := ccEH_outside_box c R hc z hz hm
      simp [ccEH_eta_zero R z.2 hR hz2, hm]
  -- measurability and integrability at `t0`
  have hF_meas : ∀ᶠ t in 𝓝 t0,
      AEStronglyMeasurable (fun z : Plane => etaCutoff R z.2 * ‖W (t, z)‖ ^ 2)
        (volume.restrict (Cyl.cell c)) := by
    filter_upwards [Ioo_mem_nhds ht0 ht0T] with t ht
    exact ((ccEH_eta_cont R).mul ((hslice t ht).norm.pow 2)).aestronglyMeasurable
  have hF_int : Integrable (fun z : Plane => etaCutoff R z.2 * ‖W (t0, z)‖ ^ 2)
      (volume.restrict (Cyl.cell c)) :=
    ccEH_integrableOn_cell c R hc (fun z : Plane => etaCutoff R z.2 * ‖W (t0, z)‖ ^ 2)
      ((ccEH_eta_cont R).mul ((hslice t0 ht0I).norm.pow 2))
      (fun z hz => by simp [ccEH_eta_zero R z.2 hR hz])
  have hF'_meas : AEStronglyMeasurable
      (fun z : Plane =>
        etaCutoff R z.2 * (2 * inner ℝ (W (t0, z)) (fderiv ℝ W (t0, z) ((1 : ℝ), (0 : Plane)))))
      (volume.restrict (Cyl.cell c)) := by
    have hGs : Continuous (fun z : Plane =>
        2 * inner ℝ (W (t0, z)) (fderiv ℝ W (t0, z) ((1 : ℝ), (0 : Plane)))) :=
      hG.comp_continuous (f := fun z : Plane => (t0, z)) (by fun_prop)
        (fun z => Set.mk_mem_prod ht0I (mem_univ z))
    exact ((ccEH_eta_cont R).mul hGs).aestronglyMeasurable
  -- pointwise differentiability in `t`
  have hdiff : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)), ∀ t ∈ Icc (t0 / 2) ((t0 + T) / 2),
      HasDerivAt (fun u => etaCutoff R z.2 * ‖W (u, z)‖ ^ 2)
        (etaCutoff R z.2 * (2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))))) t := by
    refine ae_of_all _ (fun z t ht => ?_)
    have htI : t ∈ Ioo (0 : ℝ) T := hJ_sub ht
    exact (ccEH_deriv_at hW htI z).norm_sq.const_mul (etaCutoff R z.2)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Cyl.cell c))
    (F := fun t z => etaCutoff R z.2 * ‖W (t, z)‖ ^ 2)
    (F' := fun t z =>
      etaCutoff R z.2 * (2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)))))
    (bound := (ccEHBox c R).indicator (fun _ : Plane => max Cg 0))
    (x₀ := t0) (s := Icc (t0 / 2) ((t0 + T) / 2))
    (Icc_mem_nhds (by linarith) (by linarith))
    hF_meas hF_int hF'_meas hbound (ccEH_bound_integrable c R (max Cg 0)) hdiff
  exact hmain.2

/-! ### The leaf -/

/-- **`PartI:T02/3/11`, leaf `CcEnergyHasDeriv`.** For `s ∈ (0, T)`, `F_R` has derivative
`∫_cell φ_R · 2⟨w, ∂_s w⟩`. -/
theorem ccEnergyHasDeriv : CcEnergyHasDeriv := by
  intro ν c T M v v' p p' h R hR s hs
  have hR0 : 0 < R := by linarith
  have hc : 0 < c := by linarith [h.c_ge]
  have hWd : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2 - v' x.1 x.2) (Ioo 0 T ×ˢ univ) :=
    (h.cl.smooth_v.sub h.cl'.smooth_v).mono
      (Set.prod_mono Ioo_subset_Icc_self subset_rfl)
  have hmain := ccEH_generic hWd c R hc hR0 s hs.1 hs.2
  have hdS : ∀ z : Plane, deriv (fun t => ccDiffV v v' t z) s =
      fderiv ℝ (fun x : ℝ × Plane => v x.1 x.2 - v' x.1 x.2) (s, z) ((1 : ℝ), (0 : Plane)) :=
    fun z => (ccEH_deriv_at hWd hs z).deriv
  unfold ccDt
  simp only [hdS]
  exact hmain

end UnforcedLeray.Short.PartI
