import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

instance bf_sfinite_avg (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ Cyl.cellμ
  infer_instance

/-- Pointwise: the perpendicular gradient of a slice is bounded by the full derivative. -/
theorem bf_perp_le (H : Coord → ℝ) (τ : ℝ) (p : ℝ × ℝ) (hd : DifferentiableAt ℝ H (τ, p)) :
    ‖perpGrad (fun z => H (τ, z)) p‖ ≤ ‖fderiv ℝ H (τ, p)‖ := by
  have hsl : HasFDerivAt (fun z : ℝ × ℝ => (τ, z))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p :=
    (hasFDerivAt_const τ p).prodMk (hasFDerivAt_id p)
  have hc := hd.hasFDerivAt.comp p hsl
  have hf : fderiv ℝ (fun z => H (τ, z)) p =
      (fderiv ℝ H (τ, p)).comp ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) :=
    hc.fderiv
  have h1 : ∀ v : ℝ × ℝ, ‖v‖ ≤ 1 → ‖fderiv ℝ (fun z => H (τ, z)) p v‖ ≤ ‖fderiv ℝ H (τ, p)‖ := by
    intro v hv
    rw [hf]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      zero_apply, ContinuousLinearMap.id_apply]
    calc ‖fderiv ℝ H (τ, p) (0, v)‖ ≤ ‖fderiv ℝ H (τ, p)‖ * ‖((0 : ℝ), v)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ H (τ, p)‖ * 1 := by
          gcongr
          simpa [Prod.norm_def] using hv
      _ = _ := mul_one _
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i => ?_)
  fin_cases i
  · simpa [perpGrad] using h1 (0, 1) (by simp [Prod.norm_def])
  · simpa [perpGrad] using h1 (1, 0) (by simp [Prod.norm_def])

/-- On `Icc τ₁ τ₂ ×ˢ univ`, `ageμ c 0` is `dτ ⊗ avgμ`. -/
theorem bf_restrict_eq (c τ₁ τ₂ : ℝ) (h : 0 < τ₁) :
    (Axi.ageμ c 0).restrict (Icc τ₁ τ₂ ×ˢ (univ : Set (ℝ × ℝ))) =
      (volume.restrict (Icc τ₁ τ₂)).prod (Cyl.avgμ c) := by
  have hs : Icc τ₁ τ₂ ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le h hx.1
  have e1 : Axi.ageμ c 0 = (volume.restrict (Ioi (0 : ℝ))).prod (Cyl.avgμ c) := by
    unfold Axi.ageμ
    simp
  have e2 : ∀ t : Set ℝ, (volume.restrict t).prod (Cyl.avgμ c) =
      (volume.prod (Cyl.avgμ c)).restrict (t ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro t
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e1, e2, e2, Measure.restrict_restrict (measurableSet_Icc.prod MeasurableSet.univ)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_prod, mem_univ, and_true]
  exact ⟨fun h => h.1, fun h => ⟨h, hs h⟩⟩

theorem DualFBFinite_proof : UnforcedLeray.Short.IIb.DualFBFinite := by
  intro c r ν H hc hν hr hH τ₁ τ₂ hτ₁ hτ
  set r' : ℝ := r / (r - 1) with hr'
  have hr'pos : 0 < r' := div_pos (by linarith) (by linarith)
  have hp0 : ENNReal.ofReal r' ≠ 0 := (ENNReal.ofReal_pos.2 hr'pos).ne'
  have hpt : ENNReal.ofReal r' ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmem := hH.deriv_memLp 1 (by norm_num) τ₁ τ₂ hτ₁ hτ
  rw [bf_restrict_eq c τ₁ τ₂ hτ₁] at hmem
  set G : Coord → ℝ≥0∞ := fun x => ‖iteratedFDeriv ℝ 1 H x‖ₑ ^ r' with hG
  have hfin : ∫⁻ x, G x ∂((volume.restrict (Icc τ₁ τ₂)).prod (Cyl.avgμ c)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt).1 hmem.eLpNorm_lt_top
    rwa [ENNReal.toReal_ofReal hr'pos.le] at h
  have hGm : AEMeasurable G ((volume.restrict (Icc τ₁ τ₂)).prod (Cyl.avgμ c)) :=
    (hmem.aestronglyMeasurable.enorm).pow_const r'
  have hdf : ∀ τ : ℝ, dfB c r' H τ ^ r' =
      ∫⁻ x, ‖perpGrad (fun z => H (τ, z)) x‖ₑ ^ r' ∂(Cyl.avgμ c) := by
    intro τ
    unfold dfB
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ENNReal.toReal_ofReal hr'pos.le, one_div,
      ENNReal.rpow_inv_rpow hr'pos.ne']
  calc ∫⁻ τ in Icc τ₁ τ₂, dfB c r' H τ ^ r'
      ≤ ∫⁻ τ in Icc τ₁ τ₂, ∫⁻ x, G (τ, x) ∂(Cyl.avgμ c) := by
        refine setLIntegral_mono' measurableSet_Icc (fun τ hτm => ?_)
        rw [hdf τ]
        refine lintegral_mono (fun x => ?_)
        have hd : DifferentiableAt ℝ H (τ, x) := by
          have hop : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
          have hm : (τ, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
            ⟨lt_of_lt_of_le hτ₁ hτm.1, mem_univ _⟩
          exact ((hH.smooth.differentiableOn (by simp)).differentiableAt (hop.mem_nhds hm))
        simp only [hG]
        gcongr
        rw [← ofReal_norm, ← ofReal_norm]
        have hle := bf_perp_le H τ x hd
        rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)] at hle
        exact ENNReal.ofReal_le_ofReal hle
    _ = ∫⁻ x, G x ∂((volume.restrict (Icc τ₁ τ₂)).prod (Cyl.avgμ c)) :=
        (lintegral_prod _ hGm).symm
    _ < ⊤ := hfin

end UnforcedLeray.Short.IIb
