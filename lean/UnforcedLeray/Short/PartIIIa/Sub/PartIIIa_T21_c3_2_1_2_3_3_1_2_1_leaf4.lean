import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L2_1

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/2/1/4`: `DualTestSep`

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2918,
2937-2945, 2074-2105.

Proves `DualTestSep`: the tests `ψ_χ = I_d (a⁻¹ χ(√a ·)) ⟨y⟩^{-2m}` (`χ` real cylinder tests
of period `c`) together with the tests vanishing on `C_{c/√a}` separate `L²_m`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.IIIa

namespace ComplMildTestedSplit

namespace FrameDuhamelSub

private theorem wMeasure_zero : Planar.wMeasure 0 = volume := by
  unfold Planar.wMeasure
  simp only [Real.rpow_zero, ENNReal.ofReal_one]
  exact withDensity_one

private theorem wMeasure_zero_le {m : ℝ} (hm : 0 ≤ m) :
    Planar.wMeasure 0 ≤ Planar.wMeasure m := by
  rw [wMeasure_zero]
  conv_lhs => rw [← withDensity_one (μ := (volume : Measure ℂ))]
  refine withDensity_mono ?_
  filter_upwards with z
  have h1 : 1 ≤ (1 + ‖z‖ ^ 2) ^ m := Real.one_le_rpow (by linarith [sq_nonneg ‖z‖]) hm
  simpa using ENNReal.ofReal_le_ofReal h1

/-- **Leaf T (separation)**: the tests `ψ_χ` (`χ` real cylinder tests of period `c`) and the
tests vanishing on `C_{c/√a}` separate `L²_m`. -/
theorem dualTestSep : DualTestSep := by
  intro m c a hm hc ha V h1 h2
  set d : ℝ := cellLen c a with hd_def
  have hd : 0 < d := div_pos hc (Real.sqrt_pos.2 ha)
  have hm0 : 0 ≤ m := by linarith
  -- Step 1: `V` vanishes a.e. outside `B0579.cell d` (i.e. `IsCellSupportedW d V`).
  have hsupp : BlockPropagatorInteriorSub.IsCellSupportedW d V := by
    have hS : MeasurableSet (RelBlockDiagonalSub.extSet d) :=
      RelBlockDiagonalSub.measurableSet_extSet d
    have hmem_ext : MemLp ((RelBlockDiagonalSub.extSet d).indicator (V : ℂ → ℂ))
        2 (Planar.wMeasure m) := (Lp.memLp V).indicator hS
    let ψ_ext : Planar.L2w m := hmem_ext.toLp _
    have hψ_ae : (ψ_ext : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
        (RelBlockDiagonalSub.extSet d).indicator (V : ℂ → ℂ) := MemLp.coeFn_toLp hmem_ext
    have hψ_vol : ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell d → (ψ_ext : ℂ → ℂ) z = 0 := by
      filter_upwards [(Planar.volume_ac m).ae_le hψ_ae] with z hz hmem
      rw [hz, Set.indicator_of_notMem]
      simp [RelBlockDiagonalSub.extSet, hmem]
    have hinner : ⟪ψ_ext, V⟫_ℂ = 0 := h2 ψ_ext hψ_vol
    have hint_int : Integrable (fun z => (RelBlockDiagonalSub.extSet d).indicator
        (fun z => ‖(V : ℂ → ℂ) z‖ ^ 2) z) (Planar.wMeasure m) := by
      refine Integrable.indicator ?_ hS
      exact (Lp.memLp V).norm.integrable_sq
    have hinner_eq : ⟪ψ_ext, V⟫_ℂ =
        (((∫ z, (RelBlockDiagonalSub.extSet d).indicator
          (fun z => ‖(V : ℂ → ℂ) z‖ ^ 2) z ∂(Planar.wMeasure m)) : ℝ) : ℂ) := by
      rw [MeasureTheory.L2.inner_def]
      have hint_eq : ∫ z, ⟪(ψ_ext : ℂ → ℂ) z, (V : ℂ → ℂ) z⟫_ℂ ∂(Planar.wMeasure m) =
          ∫ z, (((RelBlockDiagonalSub.extSet d).indicator
            (fun z => ‖(V : ℂ → ℂ) z‖ ^ 2) z : ℝ) : ℂ) ∂(Planar.wMeasure m) := by
        refine integral_congr_ae ?_
        filter_upwards [hψ_ae] with z hz
        rw [hz]
        by_cases hzS : z ∈ RelBlockDiagonalSub.extSet d
        · rw [Set.indicator_of_mem hzS, Set.indicator_of_mem hzS, RCLike.inner_apply,
            Complex.mul_conj']
          push_cast
          rfl
        · simp [hzS]
      rw [hint_eq]
      simpa using (Complex.ofRealCLM.integral_comp_comm hint_int)
    have hint_zero : ∫ z, (RelBlockDiagonalSub.extSet d).indicator
        (fun z => ‖(V : ℂ → ℂ) z‖ ^ 2) z ∂(Planar.wMeasure m) = 0 := by
      have := congrArg Complex.re (hinner.symm.trans hinner_eq)
      simpa using this.symm
    have hae_zero : (RelBlockDiagonalSub.extSet d).indicator
        (fun z => ‖(V : ℂ → ℂ) z‖ ^ 2) =ᵐ[Planar.wMeasure m] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (ae_of_all _ fun z => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
        hint_int).1 hint_zero
    filter_upwards [(Planar.volume_ac m).ae_le hae_zero] with z hz hnot
    have hzS : z ∈ RelBlockDiagonalSub.extSet d := hnot
    rw [Set.indicator_of_mem hzS] at hz
    exact norm_eq_zero.1 (sq_eq_zero_iff.1 hz)
  -- Step 2: View `V` as an element `W : Planar.L2w 0`.
  have hmemW : MemLp (V : ℂ → ℂ) 2 (Planar.wMeasure 0) :=
    (Lp.memLp V).mono_measure (wMeasure_zero_le hm0)
  let W : Planar.L2w 0 := hmemW.toLp (V : ℂ → ℂ)
  have hWV : (W : ℂ → ℂ) =ᵐ[volume] (V : ℂ → ℂ) :=
    (Planar.volume_ac 0).ae_le (MemLp.coeFn_toLp hmemW)
  have hWsupp : BlockPropagatorInteriorSub.IsCellSupportedW d W := by
    filter_upwards [hWV, hsupp] with z hz1 hz2 hnot
    rw [hz1, hz2 hnot]
  -- Step 3: `W` is orthogonal to `testW 0 hφ` for every cylinder test `φ` of period `d`.
  have hW_orth : ∀ (φ : ℝ × ℝ → ℝ) (hφ : B0579.IsCylTest d φ),
      ⟪RelBlockDiagonalSub.testW 0 hφ, W⟫_ℂ = 0 := by
    intro φ hφ
    let χ : B0579.Plane → ℝ := fun x => (a ^ 2)⁻¹ * φ (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
    have hχ : B0579.IsCylTest c χ := RelBlockDiagonalSub.isCylTest_rescale ha hφ
    have htestW_mem : MemLp (fun z => cellZeroExt d (fun y => ((φ y : ℝ) : ℂ)) (cToPlane z))
        2 (Planar.wMeasure m) :=
      BlockPropagatorSub.memLp_cellZeroExt_cToPlane d m ((hφ.memLp m).ofReal (K := ℂ))
    have hψ_eq : ∀ z : ℂ, testPsiFun m c a χ z =
        (((a ^ 3)⁻¹ / (1 + ‖z‖ ^ 2) ^ m : ℝ) : ℂ) *
          cellZeroExt d (fun y => ((φ y : ℝ) : ℂ)) (cToPlane z) := by
      intro z
      unfold testPsiFun cellZeroExt
      by_cases hmem : cToPlane z ∈ B0579.cell d
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
        have hχ_eval : a⁻¹ * χ (Real.sqrt a * (cToPlane z).1, Real.sqrt a * (cToPlane z).2) =
            (a ^ 3)⁻¹ * φ (cToPlane z) := by
          simp only [χ, mul_div_cancel_left₀ _ hsa]
          ring
        rw [hχ_eval]
        push_cast
        ring
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
        simp
    have hψ_eq_fun : testPsiFun m c a χ = fun z =>
        (((a ^ 3)⁻¹ / (1 + ‖z‖ ^ 2) ^ m : ℝ) : ℂ) *
          cellZeroExt d (fun y => ((φ y : ℝ) : ℂ)) (cToPlane z) := funext hψ_eq
    have hψ_meas : AEStronglyMeasurable (testPsiFun m c a χ) (Planar.wMeasure m) := by
      have hc0 : Continuous (fun z : ℂ => (((a ^ 3)⁻¹ / (1 + ‖z‖ ^ 2) ^ m : ℝ) : ℂ)) := by
        refine Complex.continuous_ofReal.comp ?_
        refine Continuous.div continuous_const ?_ (fun z => (Real.rpow_pos_of_pos (by positivity) _).ne')
        exact (continuous_const.add (continuous_norm.pow 2)).rpow_const
          (fun z => Or.inl (by positivity : (0 : ℝ) < 1 + ‖z‖ ^ 2).ne')
      rw [hψ_eq_fun]
      exact hc0.aestronglyMeasurable.mul htestW_mem.aestronglyMeasurable
    have hψ_mem : MemLp (testPsiFun m c a χ) 2 (Planar.wMeasure m) := by
      rw [hψ_eq_fun] at hψ_meas ⊢
      have hg : MemLp (fun z => (((a ^ 3)⁻¹ : ℝ) : ℂ) *
          cellZeroExt d (fun y => ((φ y : ℝ) : ℂ)) (cToPlane z)) 2 (Planar.wMeasure m) :=
        htestW_mem.const_mul (((a ^ 3)⁻¹ : ℝ) : ℂ)
      refine ⟨hψ_meas, (eLpNorm_mono_ae ?_).trans_lt hg.eLpNorm_lt_top⟩
      filter_upwards with z
      have hden : 1 ≤ (1 + ‖z‖ ^ 2) ^ m := Real.one_le_rpow (by linarith [sq_nonneg ‖z‖]) hm0
      have ha3 : 0 ≤ (a ^ 3)⁻¹ := by positivity
      calc ‖(((a ^ 3)⁻¹ / (1 + ‖z‖ ^ 2) ^ m : ℝ) : ℂ) *
              cellZeroExt d (fun y => ((φ y : ℝ) : ℂ)) (cToPlane z)‖
          = |(a ^ 3)⁻¹ / (1 + ‖z‖ ^ 2) ^ m| *
              ‖cellZeroExt d (fun y => ((φ y : ℝ) : ℂ)) (cToPlane z)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = ((a ^ 3)⁻¹ / (1 + ‖z‖ ^ 2) ^ m) *
              ‖cellZeroExt d (fun y => ((φ y : ℝ) : ℂ)) (cToPlane z)‖ := by
            rw [abs_of_nonneg (div_nonneg ha3 (by positivity))]
        _ ≤ (a ^ 3)⁻¹ * ‖cellZeroExt d (fun y => ((φ y : ℝ) : ℂ)) (cToPlane z)‖ := by
            gcongr
            exact div_le_self ha3 hden
        _ = ‖(((a ^ 3)⁻¹ : ℝ) : ℂ) *
              cellZeroExt d (fun y => ((φ y : ℝ) : ℂ)) (cToPlane z)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha3]
    let ψ : Planar.L2w m := hψ_mem.toLp (testPsiFun m c a χ)
    have hψ_vol : (ψ : ℂ → ℂ) =ᵐ[volume] testPsiFun m c a χ :=
      (Planar.volume_ac m).ae_le (MemLp.coeFn_toLp hψ_mem)
    have hzero : ⟪ψ, V⟫_ℂ = 0 := h1 χ hχ ψ hψ_vol
    have hpair_eq : ⟪ψ, V⟫_ℂ =
        (((a ^ 3)⁻¹ : ℝ) : ℂ) * ⟪RelBlockDiagonalSub.testW 0 hφ, W⟫_ℂ := by
      rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
      let fW : ℂ → ℂ := fun z => ⟪(RelBlockDiagonalSub.testW 0 hφ : ℂ → ℂ) z, (W : ℂ → ℂ) z⟫_ℂ
      change ∫ z, ⟪(ψ : ℂ → ℂ) z, (V : ℂ → ℂ) z⟫_ℂ ∂(Planar.wMeasure m) =
        (((a ^ 3)⁻¹ : ℝ) : ℂ) * ∫ z, fW z ∂(Planar.wMeasure 0)
      rw [wMeasure_zero]
      have hmeas_dens : Measurable (fun z : ℂ => ENNReal.ofReal ((1 + ‖z‖ ^ 2) ^ m)) :=
        Planar.measurable_wDensity m
      have hlt_top : ∀ᵐ z : ℂ ∂volume, ENNReal.ofReal ((1 + ‖z‖ ^ 2) ^ m) < ∞ :=
        ae_of_all _ fun _ => ENNReal.ofReal_lt_top
      change ∫ z, ⟪(ψ : ℂ → ℂ) z, (V : ℂ → ℂ) z⟫_ℂ
          ∂(volume.withDensity fun z => ENNReal.ofReal ((1 + ‖z‖ ^ 2) ^ m)) =
        (((a ^ 3)⁻¹ : ℝ) : ℂ) * ∫ z, fW z ∂volume
      rw [integral_withDensity_eq_integral_toReal_smul hmeas_dens hlt_top]
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      have ht0 := (Planar.volume_ac 0).ae_le (RelBlockDiagonalSub.coeFn_testW 0 hφ)
      filter_upwards [hψ_vol, hWV, ht0] with z hzψ hzW hzt
      rw [ENNReal.toReal_ofReal (by positivity), hzψ, hψ_eq z]
      simp only [fW, ← hzW, hzt, RCLike.inner_apply, map_mul, Complex.conj_ofReal, Complex.real_smul]
      have hden_ne : (1 + ‖z‖ ^ 2) ^ m ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
      push_cast
      field_simp [hden_ne]
    rw [hpair_eq] at hzero
    have ha3_ne : (((a ^ 3)⁻¹ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (inv_ne_zero (pow_ne_zero 3 ha.ne'))
    exact (mul_eq_zero.1 hzero).resolve_left ha3_ne
  -- Step 4: Conclude `W = 0` by density `exists_test_approx_cell`, hence `V = 0`.
  have hW_zero : W = 0 := by
    by_contra hne
    have hpos : 0 < ‖W‖ := norm_pos_iff.2 hne
    obtain ⟨φ₁, φ₂, h₁, h₂, happrox⟩ :=
      RelBlockDiagonalSub.exists_test_approx_cell hd W hWsupp hpos
    have h_orth : ⟪RelBlockDiagonalSub.testW 0 h₁ + Complex.I • RelBlockDiagonalSub.testW 0 h₂, W⟫_ℂ = 0 := by
      rw [inner_add_left, inner_smul_left, hW_orth φ₁ h₁, hW_orth φ₂ h₂, mul_zero, add_zero]
    have hsq : ‖W‖ ^ 2 ≤ ‖W - (RelBlockDiagonalSub.testW 0 h₁ + Complex.I • RelBlockDiagonalSub.testW 0 h₂)‖ * ‖W‖ := by
      have hre : ((‖W‖ ^ 2 : ℝ) : ℂ) =
          ⟪W - (RelBlockDiagonalSub.testW 0 h₁ + Complex.I • RelBlockDiagonalSub.testW 0 h₂), W⟫_ℂ := by
        rw [inner_sub_left, h_orth, sub_zero, inner_self_eq_norm_sq_to_K]
        norm_cast
      calc ‖W‖ ^ 2 = ‖((‖W‖ ^ 2 : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
        _ = ‖⟪W - (RelBlockDiagonalSub.testW 0 h₁ + Complex.I • RelBlockDiagonalSub.testW 0 h₂), W⟫_ℂ‖ := by
            rw [hre]
        _ ≤ ‖W - (RelBlockDiagonalSub.testW 0 h₁ + Complex.I • RelBlockDiagonalSub.testW 0 h₂)‖ * ‖W‖ :=
            norm_inner_le_norm _ _
    have hlt : ‖W‖ ^ 2 < ‖W‖ * ‖W‖ := by
      calc ‖W‖ ^ 2 ≤ ‖W - (RelBlockDiagonalSub.testW 0 h₁ + Complex.I • RelBlockDiagonalSub.testW 0 h₂)‖ * ‖W‖ := hsq
        _ < ‖W‖ * ‖W‖ := mul_lt_mul_of_pos_right happrox hpos
    linarith [sq (‖W‖)]
  have hV_zero_vol : (V : ℂ → ℂ) =ᵐ[volume] 0 := by
    have hW0 : (W : ℂ → ℂ) =ᵐ[volume] 0 := by
      rw [hW_zero]
      exact (Planar.volume_ac 0).ae_le (Lp.coeFn_zero ℂ 2 (Planar.wMeasure 0))
    exact hWV.symm.trans hW0
  exact Lp.ext (EventuallyEq.trans ((Planar.wMeasure_ac m).ae_le hV_zero_vol)
    (Lp.coeFn_zero ℂ 2 (Planar.wMeasure m)).symm)

end FrameDuhamelSub

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
