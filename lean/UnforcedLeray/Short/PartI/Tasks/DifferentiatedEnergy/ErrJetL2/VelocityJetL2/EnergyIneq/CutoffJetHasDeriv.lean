import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.HasDeriv

/-!
# Part I, task `PartI:T08/2/2/2/3`: differentiation of the cutoff jet energy

Target: `cutoffJetHasDeriv_proof : CutoffJetHasDeriv` (`Sub/PartI_T08_2_2/EnergyIneq.lean`).

Source of record: `the November 2 reference manuscript`, lines 286-287.

Adapts `cehd_generic` (`Tasks/TrainCutoffEnergyProof/HasDeriv.lean`) to the scalar integrand
`F t z = etaCutoff R z.2 * ∑ u ∈ ι, W u (t, z) ^ 2`, with derivative
`∑ u ∈ ι, 2 * W u (t, z) * ∂_t W u (t, z)`.  Differentiation under the integral sign on
`Icc (t₀/2) (2 t₀)`, with the same compact box `cehdBox c R` for domination.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- For `t > 0` the `t`-derivative of a scalar `W(·, z)` is the `(1, 0)`-derivative of `W`. -/
theorem cjh_deriv_at {W : ℝ × Plane → ℝ} (hW : ContDiffOn ℝ ∞ W (Ioi 0 ×ˢ univ))
    {t : ℝ} (ht : 0 < t) (z : Plane) :
    HasDerivAt (fun u => W (u, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))) t := by
  have hmem : (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) ∈ 𝓝 (t, z) :=
    cehd_open.mem_nhds (Set.mk_mem_prod ht (mem_univ z))
  have hF : HasFDerivAt W (fderiv ℝ W (t, z)) (t, z) :=
    ((hW.contDiffAt hmem).differentiableAt (by simp)).hasFDerivAt
  have hg : HasDerivAt (fun u : ℝ => (u, z)) ((1 : ℝ), (0 : Plane)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t z)
  exact hF.comp_hasDerivAt t hg

/-- The continuous function `x ↦ 2 W x ∂_t W x` on `(0, ∞) × ℝ²` (scalar case). -/
theorem cjh_cont_G {W : ℝ × Plane → ℝ} (hW : ContDiffOn ℝ ∞ W (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun x : ℝ × Plane => 2 * W x * fderiv ℝ W x ((1 : ℝ), (0 : Plane)))
      (Ioi 0 ×ˢ univ) := by
  have h2 : ContinuousOn (fderiv ℝ W) (Ioi 0 ×ˢ univ) :=
    hW.continuousOn_fderiv_of_isOpen cehd_open (by simp)
  have h3 : ContinuousOn (fun x : ℝ × Plane => fderiv ℝ W x ((1 : ℝ), (0 : Plane)))
      (Ioi 0 ×ˢ univ) :=
    h2.clm_apply continuousOn_const
  have h1 : ContinuousOn (fun x : ℝ × Plane => 2 * W x) (Ioi 0 ×ˢ univ) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ × Plane => (2 : ℝ)) (Ioi 0 ×ˢ univ)).mul
      hW.continuousOn
  exact h1.mul h3

/-- **Leaf `CutoffJetHasDeriv`** (proof): differentiation of the cutoff jet energy under the
integral sign, at `t₀ > 0`. -/
theorem cutoffJetHasDeriv_proof : CutoffJetHasDeriv := by
  unfold CutoffJetHasDeriv
  intro c R ι W hc hR hW t₀ ht₀
  have hR0 : 0 < R := hR
  -- the summed derivative integrand is continuous on `(0, ∞) × ℝ²`
  have hG : ContinuousOn
      (fun x : ℝ × Plane => ∑ u ∈ ι, 2 * W u x * fderiv ℝ (W u) x ((1 : ℝ), (0 : Plane)))
      (Ioi 0 ×ˢ univ) :=
    continuousOn_finsetSum ι (fun u hu => cjh_cont_G (hW u hu))
  -- continuity in `z` of the slices, for `t > 0`
  have hslice_u : ∀ u ∈ ι, ∀ t : ℝ, 0 < t → Continuous (fun z : Plane => W u (t, z)) :=
    fun u hu t ht =>
      (hW u hu).continuousOn.comp_continuous (f := fun z : Plane => (t, z)) (by fun_prop)
        (fun z => Set.mk_mem_prod ht (mem_univ z))
  have hslice : ∀ t : ℝ, 0 < t → Continuous (fun z : Plane => ∑ u ∈ ι, W u (t, z) ^ 2) :=
    fun t ht => continuous_finsetSum ι (fun u hu => (hslice_u u hu t ht).pow 2)
  -- the compact set of `(t, z)` on which the derivative is bounded
  have hKt : IsCompact (Icc (t₀ / 2) (2 * t₀) ×ˢ cehdBox c R) :=
    isCompact_Icc.prod (cehd_box_compact c R)
  have hKt_sub : Icc (t₀ / 2) (2 * t₀) ×ˢ cehdBox c R ⊆ Ioi 0 ×ˢ (univ : Set Plane) := by
    intro x hx
    have h1 : (0 : ℝ) < x.1 := lt_of_lt_of_le (by linarith) hx.1.1
    exact Set.mk_mem_prod h1 (mem_univ _)
  obtain ⟨Cg, hCg⟩ := hKt.exists_bound_of_continuousOn (hG.mono hKt_sub)
  -- the domination bound
  have hbound : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)), ∀ t ∈ Icc (t₀ / 2) (2 * t₀),
      ‖etaCutoff R z.2 *
          ∑ u ∈ ι, 2 * W u (t, z) * fderiv ℝ (W u) (t, z) ((1 : ℝ), (0 : Plane))‖ ≤
        (cehdBox c R).indicator (fun _ : Plane => max Cg 0) z := by
    filter_upwards [ae_restrict_mem (cehd_cell_measurable c)] with z hz
    intro t ht
    by_cases hm : z ∈ cehdBox c R
    · rw [Set.indicator_of_mem hm]
      have hg : ‖∑ u ∈ ι, 2 * W u (t, z) * fderiv ℝ (W u) (t, z) ((1 : ℝ), (0 : Plane))‖ ≤ Cg :=
        hCg (t, z) (Set.mk_mem_prod ht hm)
      have h1 : ‖etaCutoff R z.2‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (etaCutoff_nonneg R z.2)]
        exact cehd_eta_le_one R z.2
      calc ‖etaCutoff R z.2 *
              ∑ u ∈ ι, 2 * W u (t, z) * fderiv ℝ (W u) (t, z) ((1 : ℝ), (0 : Plane))‖
          = ‖etaCutoff R z.2‖ *
              ‖∑ u ∈ ι, 2 * W u (t, z) * fderiv ℝ (W u) (t, z) ((1 : ℝ), (0 : Plane))‖ :=
            norm_mul _ _
        _ ≤ 1 * Cg := mul_le_mul h1 hg (norm_nonneg _) zero_le_one
        _ ≤ max Cg 0 := by rw [one_mul]; exact le_max_left _ _
    · have hz2 := cehd_outside_box c R hc z hz hm
      simp [cehd_eta_zero R z.2 hR0 hz2, hm]
  -- integrability of the value at `t₀`
  have hF_int : Integrable (fun z : Plane => etaCutoff R z.2 * ∑ u ∈ ι, W u (t₀, z) ^ 2)
      (volume.restrict (Cyl.cell c)) :=
    cehd_integrableOn_cell c R hc (fun z : Plane => etaCutoff R z.2 * ∑ u ∈ ι, W u (t₀, z) ^ 2)
      ((cehd_eta_cont R).mul (hslice t₀ ht₀))
      (fun z hz => by simp [cehd_eta_zero R z.2 hR0 hz])
  have hF_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (fun z : Plane => etaCutoff R z.2 * ∑ u ∈ ι, W u (t, z) ^ 2)
        (volume.restrict (Cyl.cell c)) := by
    filter_upwards [Ioi_mem_nhds ht₀] with t ht
    exact ((cehd_eta_cont R).mul (hslice t ht)).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable
      (fun z : Plane =>
        etaCutoff R z.2 * ∑ u ∈ ι, 2 * W u (t₀, z) * fderiv ℝ (W u) (t₀, z) ((1 : ℝ), (0 : Plane)))
      (volume.restrict (Cyl.cell c)) := by
    have hGs : Continuous (fun z : Plane =>
        ∑ u ∈ ι, 2 * W u (t₀, z) * fderiv ℝ (W u) (t₀, z) ((1 : ℝ), (0 : Plane))) :=
      hG.comp_continuous (f := fun z : Plane => (t₀, z)) (by fun_prop)
        (fun z => Set.mk_mem_prod ht₀ (mem_univ z))
    exact ((cehd_eta_cont R).mul hGs).aestronglyMeasurable
  -- pointwise differentiability in `t`
  have hdiff : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)), ∀ t ∈ Icc (t₀ / 2) (2 * t₀),
      HasDerivAt (fun u => etaCutoff R z.2 * ∑ i ∈ ι, W i (u, z) ^ 2)
        (etaCutoff R z.2 *
          ∑ i ∈ ι, 2 * W i (t, z) * fderiv ℝ (W i) (t, z) ((1 : ℝ), (0 : Plane))) t := by
    refine ae_of_all _ (fun z t ht => ?_)
    have ht' : 0 < t := lt_of_lt_of_le (by linarith) ht.1
    have hs : HasDerivAt (fun u => ∑ i ∈ ι, W i (u, z) ^ 2)
        (∑ i ∈ ι, 2 * W i (t, z) * fderiv ℝ (W i) (t, z) ((1 : ℝ), (0 : Plane))) t :=
      HasDerivAt.fun_sum (fun i hi => ((cjh_deriv_at (hW i hi) ht' z).pow 2).congr_deriv (by norm_num))
    exact hs.const_mul (etaCutoff R z.2)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Cyl.cell c))
    (F := fun t z => etaCutoff R z.2 * ∑ u ∈ ι, W u (t, z) ^ 2)
    (F' := fun t z =>
      etaCutoff R z.2 * ∑ u ∈ ι, 2 * W u (t, z) * fderiv ℝ (W u) (t, z) ((1 : ℝ), (0 : Plane)))
    (bound := (cehdBox c R).indicator (fun _ : Plane => max Cg 0))
    (x₀ := t₀) (s := Icc (t₀ / 2) (2 * t₀)) (Icc_mem_nhds (by linarith) (by linarith))
    hF_meas hF_int hF'_meas hbound (cehd_bound_integrable c R (max Cg 0)) hdiff
  -- identify the `deriv` in the statement with the `fderiv` in the derivative integrand
  have hfun : (fun z : Plane =>
        etaCutoff R z.2 * ∑ u ∈ ι, 2 * W u (t₀, z) * deriv (fun t => W u (t, z)) t₀) =
      (fun z : Plane =>
        etaCutoff R z.2 * ∑ u ∈ ι, 2 * W u (t₀, z) * fderiv ℝ (W u) (t₀, z) ((1 : ℝ), (0 : Plane))) := by
    funext z
    congr 1
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [(cjh_deriv_at (hW u hu) ht₀ z).deriv]
  rw [hfun]
  exact hmain.2

end UnforcedLeray.Short.PartI
