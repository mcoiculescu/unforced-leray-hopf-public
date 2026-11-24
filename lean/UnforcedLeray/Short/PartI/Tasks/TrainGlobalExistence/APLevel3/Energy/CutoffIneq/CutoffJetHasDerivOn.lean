import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.HasDeriv

/-!
# Part I, `PartI:T04/10/1/2/1/6`: `CutoffJetHasDerivOn`

Source of record: `the November 2 reference manuscript`, lines 285-287.
Differentiation of the transverse cutoff jet energy on an open time strip `(a, b)`.
Adapts `cutoffJetHasDeriv_proof` (`Tasks/DifferentiatedEnergy/ErrJetL2/VelocityJetL2/EnergyIneq/
CutoffJetHasDeriv.lean`) from `Ioi 0` to `Ioo a b`, with the time window
`Icc (t₀ - d) (t₀ + d)`, `d = min (t₀ - a) (b - t₀) / 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

theorem cjoS_open (a b : ℝ) : IsOpen (Ioo a b ×ˢ (univ : Set Plane)) :=
  isOpen_Ioo.prod isOpen_univ

/-- For `t ∈ (a,b)` the `t`-derivative of a scalar `W(·, z)` is the `(1, 0)`-derivative of `W`. -/
theorem cjoS_deriv_at {a b : ℝ} {W : ℝ × Plane → ℝ} (hW : ContDiffOn ℝ ∞ W (Ioo a b ×ˢ univ))
    {t : ℝ} (ht : t ∈ Ioo a b) (z : Plane) :
    HasDerivAt (fun u => W (u, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))) t := by
  have hmem : (Ioo a b ×ˢ (univ : Set Plane)) ∈ 𝓝 (t, z) :=
    (cjoS_open a b).mem_nhds (Set.mk_mem_prod ht (mem_univ z))
  have hF : HasFDerivAt W (fderiv ℝ W (t, z)) (t, z) :=
    ((hW.contDiffAt hmem).differentiableAt (by simp)).hasFDerivAt
  have hg : HasDerivAt (fun u : ℝ => (u, z)) ((1 : ℝ), (0 : Plane)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t z)
  exact hF.comp_hasDerivAt t hg

/-- The continuous function `x ↦ 2 W x ∂_t W x` on the strip `(a, b) × ℝ²` (scalar case). -/
theorem cjoS_cont_G {a b : ℝ} {W : ℝ × Plane → ℝ} (hW : ContDiffOn ℝ ∞ W (Ioo a b ×ˢ univ)) :
    ContinuousOn (fun x : ℝ × Plane => 2 * W x * fderiv ℝ W x ((1 : ℝ), (0 : Plane)))
      (Ioo a b ×ˢ univ) := by
  have h2 : ContinuousOn (fderiv ℝ W) (Ioo a b ×ˢ univ) :=
    hW.continuousOn_fderiv_of_isOpen (cjoS_open a b) (by simp)
  have h3 : ContinuousOn (fun x : ℝ × Plane => fderiv ℝ W x ((1 : ℝ), (0 : Plane)))
      (Ioo a b ×ˢ univ) :=
    h2.clm_apply continuousOn_const
  have h1 : ContinuousOn (fun x : ℝ × Plane => 2 * W x) (Ioo a b ×ˢ univ) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ × Plane => (2 : ℝ)) (Ioo a b ×ˢ univ)).mul
      hW.continuousOn
  exact h1.mul h3

/-- **Target** `cutoffJetHasDerivOn_proof`: differentiation of the cutoff jet energy under the
integral sign, at `t₀` in the open strip `(a, b)` (`CutoffJetHasDerivOn`). -/
theorem cutoffJetHasDerivOn_proof : CutoffJetHasDerivOn := by
  unfold CutoffJetHasDerivOn
  intro c R a b ι W hc hR hW t₀ ht₀
  have hR0 : 0 < R := hR
  have hA : a < t₀ := ht₀.1
  have hB : t₀ < b := ht₀.2
  -- the summed derivative integrand is continuous on the strip
  have hG : ContinuousOn
      (fun x : ℝ × Plane => ∑ u ∈ ι, 2 * W u x * fderiv ℝ (W u) x ((1 : ℝ), (0 : Plane)))
      (Ioo a b ×ˢ univ) :=
    continuousOn_finsetSum ι (fun u hu => cjoS_cont_G (hW u hu))
  -- continuity in `z` of the slices, for `t ∈ (a, b)`
  have hslice_u : ∀ u ∈ ι, ∀ t ∈ Ioo a b, Continuous (fun z : Plane => W u (t, z)) :=
    fun u hu t ht =>
      (hW u hu).continuousOn.comp_continuous (f := fun z : Plane => (t, z)) (by fun_prop)
        (fun z => Set.mk_mem_prod ht (mem_univ z))
  have hslice : ∀ t ∈ Ioo a b, Continuous (fun z : Plane => ∑ u ∈ ι, W u (t, z) ^ 2) :=
    fun t ht => continuous_finsetSum ι (fun u hu => (hslice_u u hu t ht).pow 2)
  -- the time window `[t₀ - d, t₀ + d]` inside the strip
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = min (t₀ - a) (b - t₀) / 2 := ⟨_, rfl⟩
  have hm1 : min (t₀ - a) (b - t₀) ≤ t₀ - a := min_le_left _ _
  have hm2 : min (t₀ - a) (b - t₀) ≤ b - t₀ := min_le_right _ _
  have hpos : 0 < min (t₀ - a) (b - t₀) := lt_min (by linarith) (by linarith)
  have hd0 : 0 < d := by rw [hd_def]; linarith
  have hdA : d < t₀ - a := by linarith
  have hdB : d < b - t₀ := by linarith
  have hsub : Icc (t₀ - d) (t₀ + d) ⊆ Ioo a b := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the compact set of `(t, z)` on which the derivative is bounded
  have hKt : IsCompact (Icc (t₀ - d) (t₀ + d) ×ˢ cehdBox c R) :=
    isCompact_Icc.prod (cehd_box_compact c R)
  have hKt_sub : Icc (t₀ - d) (t₀ + d) ×ˢ cehdBox c R ⊆ Ioo a b ×ˢ (univ : Set Plane) := by
    intro x hx
    exact Set.mk_mem_prod (hsub hx.1) (mem_univ _)
  obtain ⟨Cg, hCg⟩ := hKt.exists_bound_of_continuousOn (hG.mono hKt_sub)
  -- the domination bound
  have hbound : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)), ∀ t ∈ Icc (t₀ - d) (t₀ + d),
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
    filter_upwards [Ioo_mem_nhds hA hB] with t ht
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
  have hdiff : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)), ∀ t ∈ Icc (t₀ - d) (t₀ + d),
      HasDerivAt (fun u => etaCutoff R z.2 * ∑ i ∈ ι, W i (u, z) ^ 2)
        (etaCutoff R z.2 *
          ∑ i ∈ ι, 2 * W i (t, z) * fderiv ℝ (W i) (t, z) ((1 : ℝ), (0 : Plane))) t := by
    refine ae_of_all _ (fun z t ht => ?_)
    have ht' : t ∈ Ioo a b := hsub ht
    have hs : HasDerivAt (fun u => ∑ i ∈ ι, W i (u, z) ^ 2)
        (∑ i ∈ ι, 2 * W i (t, z) * fderiv ℝ (W i) (t, z) ((1 : ℝ), (0 : Plane))) t :=
      HasDerivAt.fun_sum (fun i hi =>
        ((cjoS_deriv_at (hW i hi) ht' z).pow 2).congr_deriv (by norm_num))
    exact hs.const_mul (etaCutoff R z.2)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Cyl.cell c))
    (F := fun t z => etaCutoff R z.2 * ∑ u ∈ ι, W u (t, z) ^ 2)
    (F' := fun t z =>
      etaCutoff R z.2 * ∑ u ∈ ι, 2 * W u (t, z) * fderiv ℝ (W u) (t, z) ((1 : ℝ), (0 : Plane)))
    (bound := (cehdBox c R).indicator (fun _ : Plane => max Cg 0))
    (x₀ := t₀) (s := Icc (t₀ - d) (t₀ + d)) (Icc_mem_nhds (by linarith) (by linarith))
    hF_meas hF_int hF'_meas hbound (cehd_bound_integrable c R (max Cg 0)) hdiff
  -- identify the `deriv` in the statement with the `fderiv` in the derivative integrand
  have hfun : (fun z : Plane =>
        etaCutoff R z.2 * ∑ u ∈ ι, 2 * W u (t₀, z) * deriv (fun t => W u (t, z)) t₀) =
      (fun z : Plane =>
        etaCutoff R z.2 * ∑ u ∈ ι, 2 * W u (t₀, z) * fderiv ℝ (W u) (t₀, z) ((1 : ℝ), (0 : Plane))) := by
    funext z
    congr 1
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [(cjoS_deriv_at (hW u hu) ht₀ z).deriv]
  rw [hfun]
  exact hmain.2

end UnforcedLeray.Short.PartI
