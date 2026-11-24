import UnforcedLeray.Short.PartI.Sub.T02_3_10

/-!


Target: `theorem ebHasDeriv : EtaCutoffFacts → EbHasDeriv` (`Short/PartI/Sub/T02_3_10.lean`,
`EbHasDeriv`). Source of record: `the November 2 reference manuscript`, lines 276-282.

Outline. For `s ∈ (0, T)` choose `d > 0` with `Icc (s - d) (s + d) ⊆ Ioo 0 T`. On the open set
`Ioo 0 T × ℝ²` the map `W(t, z) = v t z` is `C^∞`, so `t ↦ W(t, z)` has derivative
`fderiv W (t, z) (1, 0)`, and `(t, z) ↦ 2⟨W, ∂_t W⟩` is continuous there. Differentiation under the
integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) on the neighbourhood
`Icc (s - d) (s + d)` uses a constant bound on the compact set `Icc (s-d) (s+d) × box`,
`box = [-c, c] × [-2R, 2R]`, and the vanishing of the integrand for `2R ≤ |η|`.
`EtaCutoffFacts` is not needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Facts about the transverse cutoff `etaCutoff` -/

theorem ebHD_eta_cont (R : ℝ) : Continuous (fun z : Plane => etaCutoff R z.2) := by
  unfold etaCutoff
  have h1 : Continuous (fun z : Plane => 2 - |z.2| / R) :=
    continuous_const.sub ((continuous_abs.comp continuous_snd).div_const R)
  exact (Real.smoothTransition.continuous.comp h1).pow 2

theorem ebHD_eta_nonneg (R η : ℝ) : 0 ≤ etaCutoff R η := by
  show 0 ≤ Real.smoothTransition (2 - |η| / R) ^ 2
  positivity

theorem ebHD_eta_le_one (R η : ℝ) : etaCutoff R η ≤ 1 := by
  show Real.smoothTransition (2 - |η| / R) ^ 2 ≤ 1
  exact pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem ebHD_eta_zero (R η : ℝ) (hR : 0 < R) (h : 2 * R ≤ |η|) : etaCutoff R η = 0 := by
  have h2 : 2 ≤ |η| / R := (le_div_iff₀ hR).2 (by linarith)
  have hle : 2 - |η| / R ≤ 0 := by linarith
  show Real.smoothTransition (2 - |η| / R) ^ 2 = 0
  simp [Real.smoothTransition.zero_of_nonpos hle]

/-! ### The compact box and the cell -/

/-- A compact box containing the cell intersected with the strip `|η| ≤ 2R`. -/
def ebHDBox (c R : ℝ) : Set Plane := Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R)

theorem ebHD_box_compact (c R : ℝ) : IsCompact (ebHDBox c R) :=
  isCompact_Icc.prod isCompact_Icc

theorem ebHD_cell_measurable (c : ℝ) : MeasurableSet (Cyl.cell c) := by
  unfold Cyl.cell
  exact measurableSet_Ico.prod MeasurableSet.univ

/-- A point of the cell outside the box lies outside the strip `|η| ≤ 2R`. -/
theorem ebHD_outside_box (c R : ℝ) (hc : 0 < c) (z : Plane) (hz : z ∈ Cyl.cell c)
    (hm : z ∉ ebHDBox c R) : 2 * R ≤ |z.2| := by
  by_contra hlt
  have hlt' : |z.2| < 2 * R := not_le.1 hlt
  apply hm
  have hq : -c / 2 ≤ z.1 ∧ z.1 < c / 2 := hz.1
  exact ⟨⟨by linarith [hq.1], by linarith [hq.2]⟩, abs_le.1 hlt'.le⟩

theorem ebHD_bound_integrable (c R C : ℝ) :
    Integrable ((ebHDBox c R).indicator (fun _ : Plane => C)) (volume.restrict (Cyl.cell c)) := by
  rw [integrable_indicator_iff (ebHD_box_compact c R).isClosed.measurableSet]
  refine integrableOn_const ?_
  rw [Measure.restrict_apply (ebHD_box_compact c R).isClosed.measurableSet]
  exact ne_top_of_le_ne_top (ebHD_box_compact c R).measure_lt_top.ne
    (measure_mono inter_subset_left)

/-- A continuous function on the plane vanishing on `|η| ≥ 2R` is integrable on the cell. -/
theorem ebHD_integrableOn_cell (c R : ℝ) (hc : 0 < c) (g : Plane → ℝ) (hg : Continuous g)
    (hsupp : ∀ z : Plane, 2 * R ≤ |z.2| → g z = 0) : IntegrableOn g (Cyl.cell c) := by
  obtain ⟨C, hC⟩ := (ebHD_box_compact c R).exists_bound_of_continuousOn hg.continuousOn
  refine Integrable.mono' (ebHD_bound_integrable c R (max C 0)) hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (ebHD_cell_measurable c)] with z hz
  by_cases hm : z ∈ ebHDBox c R
  · rw [Set.indicator_of_mem hm]
    exact (hC z hm).trans (le_max_left _ _)
  · rw [hsupp z (ebHD_outside_box c R hc z hz hm), norm_zero]
    exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) z

/-! ### Calculus of the velocity -/

theorem ebHD_open (T : ℝ) : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
  isOpen_Ioo.prod isOpen_univ

/-- For `t ∈ (0, T)` the `t`-derivative of `W(·, z)` is the `(1, 0)`-derivative of `W`. -/
theorem ebHD_deriv_at {W : ℝ × Plane → Vec} {T : ℝ} (hW : ContDiffOn ℝ ∞ W (Ioo 0 T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (z : Plane) :
    HasDerivAt (fun u => W (u, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))) t := by
  have hmem : (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) ∈ 𝓝 (t, z) :=
    (ebHD_open T).mem_nhds (Set.mk_mem_prod ht (mem_univ z))
  have hF : HasFDerivAt W (fderiv ℝ W (t, z)) (t, z) :=
    ((hW.contDiffAt hmem).differentiableAt (by simp)).hasFDerivAt
  have hg : HasDerivAt (fun u : ℝ => (u, z)) ((1 : ℝ), (0 : Plane)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t z)
  exact hF.comp_hasDerivAt t hg

/-- The continuous function `(t, z) ↦ 2⟨W, ∂_t W⟩` on `(0, T) × ℝ²`. -/
theorem ebHD_cont_G {W : ℝ × Plane → Vec} {T : ℝ}
    (hW : ContDiffOn ℝ ∞ W (Ioo 0 T ×ˢ univ)) :
    ContinuousOn (fun x : ℝ × Plane => 2 * inner ℝ (W x) (fderiv ℝ W x ((1 : ℝ), (0 : Plane))))
      (Ioo 0 T ×ˢ univ) := by
  have h2 : ContinuousOn (fderiv ℝ W) (Ioo 0 T ×ˢ univ) :=
    hW.continuousOn_fderiv_of_isOpen (ebHD_open T) (by simp)
  have h3 : ContinuousOn (fun x : ℝ × Plane => fderiv ℝ W x ((1 : ℝ), (0 : Plane)))
      (Ioo 0 T ×ˢ univ) :=
    h2.clm_apply continuousOn_const
  exact continuousOn_const.mul (hW.continuousOn.inner h3)

/-! ### The generic differentiation under the integral sign -/

theorem ebHD_generic {W : ℝ × Plane → Vec} {T : ℝ} (hW : ContDiffOn ℝ ∞ W (Ioo 0 T ×ˢ univ))
    (c R : ℝ) (hc : 0 < c) (hR : 0 < R) (s : ℝ) (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun u => ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖W (u, z)‖ ^ 2)
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * inner ℝ (W (s, z)) (fderiv ℝ W (s, z) ((1 : ℝ), (0 : Plane))))) s := by
  have hG := ebHD_cont_G hW
  -- continuity in `z` of the slices, for `t ∈ (0, T)`
  have hslice : ∀ t ∈ Ioo 0 T, Continuous (fun z : Plane => W (t, z)) := fun t ht =>
    hW.continuousOn.comp_continuous (f := fun z : Plane => (t, z)) (by fun_prop)
      (fun z => Set.mk_mem_prod ht (mem_univ z))
  -- a neighbourhood `Icc (s - d) (s + d)` of `s` inside `(0, T)`
  obtain ⟨d, hd0, hdI⟩ : ∃ d : ℝ, 0 < d ∧ Icc (s - d) (s + d) ⊆ Ioo 0 T := by
    have h1 : 0 < min s (T - s) := lt_min hs.1 (by linarith [hs.2])
    refine ⟨min s (T - s) / 2, by linarith, ?_⟩
    intro t ht
    have hm1 : min s (T - s) ≤ s := min_le_left _ _
    have hm2 : min s (T - s) ≤ T - s := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  have hIcc_mem : Icc (s - d) (s + d) ∈ 𝓝 s := Icc_mem_nhds (by linarith) (by linarith)
  -- the compact set on which the derivative is bounded
  have hK : IsCompact (Icc (s - d) (s + d) ×ˢ ebHDBox c R) :=
    isCompact_Icc.prod (ebHD_box_compact c R)
  have hK_sub : Icc (s - d) (s + d) ×ˢ ebHDBox c R ⊆ Ioo 0 T ×ˢ (univ : Set Plane) :=
    Set.prod_mono hdI (subset_univ _)
  obtain ⟨Cg, hCg⟩ := hK.exists_bound_of_continuousOn (hG.mono hK_sub)
  -- the domination bound
  have hbound : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)), ∀ t ∈ Icc (s - d) (s + d),
      ‖etaCutoff R z.2 * (2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))))‖ ≤
        (ebHDBox c R).indicator (fun _ : Plane => max Cg 0) z := by
    filter_upwards [ae_restrict_mem (ebHD_cell_measurable c)] with z hz
    intro t ht
    by_cases hm : z ∈ ebHDBox c R
    · rw [Set.indicator_of_mem hm]
      have hg : ‖2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)))‖ ≤ Cg :=
        hCg (t, z) (Set.mk_mem_prod ht hm)
      have h1 : ‖etaCutoff R z.2‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (ebHD_eta_nonneg R z.2)]
        exact ebHD_eta_le_one R z.2
      calc ‖etaCutoff R z.2 * (2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))))‖
          = ‖etaCutoff R z.2‖ *
              ‖2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)))‖ := norm_mul _ _
        _ ≤ 1 * Cg := mul_le_mul h1 hg (norm_nonneg _) zero_le_one
        _ ≤ max Cg 0 := by rw [one_mul]; exact le_max_left _ _
    · have hz2 := ebHD_outside_box c R hc z hz hm
      simp [ebHD_eta_zero R z.2 hR hz2, hm]
  -- measurability and integrability at `s`
  have hF_meas : ∀ᶠ t in 𝓝 s,
      AEStronglyMeasurable (fun z : Plane => etaCutoff R z.2 * ‖W (t, z)‖ ^ 2)
        (volume.restrict (Cyl.cell c)) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    exact ((ebHD_eta_cont R).mul ((hslice t ht).norm.pow 2)).aestronglyMeasurable
  have hF_int : Integrable (fun z : Plane => etaCutoff R z.2 * ‖W (s, z)‖ ^ 2)
      (volume.restrict (Cyl.cell c)) :=
    ebHD_integrableOn_cell c R hc (fun z : Plane => etaCutoff R z.2 * ‖W (s, z)‖ ^ 2)
      ((ebHD_eta_cont R).mul ((hslice s hs).norm.pow 2))
      (fun z hz => by simp [ebHD_eta_zero R z.2 hR hz])
  have hF'_meas : AEStronglyMeasurable
      (fun z : Plane =>
        etaCutoff R z.2 * (2 * inner ℝ (W (s, z)) (fderiv ℝ W (s, z) ((1 : ℝ), (0 : Plane)))))
      (volume.restrict (Cyl.cell c)) := by
    have hGs : Continuous (fun z : Plane =>
        2 * inner ℝ (W (s, z)) (fderiv ℝ W (s, z) ((1 : ℝ), (0 : Plane)))) :=
      hG.comp_continuous (f := fun z : Plane => (s, z)) (by fun_prop)
        (fun z => Set.mk_mem_prod hs (mem_univ z))
    exact ((ebHD_eta_cont R).mul hGs).aestronglyMeasurable
  -- pointwise differentiability in `t`
  have hdiff : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)), ∀ t ∈ Icc (s - d) (s + d),
      HasDerivAt (fun u => etaCutoff R z.2 * ‖W (u, z)‖ ^ 2)
        (etaCutoff R z.2 * (2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))))) t := by
    refine ae_of_all _ (fun z t ht => ?_)
    exact (ebHD_deriv_at hW (hdI ht) z).norm_sq.const_mul (etaCutoff R z.2)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Cyl.cell c))
    (F := fun t z => etaCutoff R z.2 * ‖W (t, z)‖ ^ 2)
    (F' := fun t z =>
      etaCutoff R z.2 * (2 * inner ℝ (W (t, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)))))
    (bound := (ebHDBox c R).indicator (fun _ : Plane => max Cg 0))
    (x₀ := s) (s := Icc (s - d) (s + d)) hIcc_mem
    hF_meas hF_int hF'_meas hbound (ebHD_bound_integrable c R (max Cg 0)) hdiff
  exact hmain.2

/-! ### The leaf -/

/-- **`PartI:T02/3/10`, leaf `EbHasDeriv`.** For `s ∈ (0, T)`, `E_R` has derivative
`∫_cell φ_R · 2⟨v, ∂_s v⟩`. -/
theorem ebHasDeriv : EtaCutoffFacts → EbHasDeriv := by
  intro _hF
  unfold EbHasDeriv
  intro ν c T v p hc hcl R hR s hs
  have hR0 : 0 < R := by linarith
  have hWo : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Ioo 0 T ×ˢ univ) :=
    hcl.smooth_v.mono (Set.prod_mono Ioo_subset_Icc_self subset_rfl)
  have hmain := ebHD_generic hWo c R hc hR0 s hs
  have hdS : ∀ z : Plane, deriv (fun t => v t z) s =
      fderiv ℝ (fun x : ℝ × Plane => v x.1 x.2) (s, z) ((1 : ℝ), (0 : Plane)) :=
    fun z => (ebHD_deriv_at hWo hs z).deriv
  show HasDerivAt (fun u => ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖v u z‖ ^ 2) _ s
  unfold ebDtIntegral
  simp only [hdS]
  exact hmain

end UnforcedLeray.Short.PartI
