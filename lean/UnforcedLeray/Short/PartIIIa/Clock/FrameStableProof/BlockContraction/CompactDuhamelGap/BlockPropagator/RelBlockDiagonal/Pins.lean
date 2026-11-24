import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelBlockDiagonal.Support

/-!
# `PartIII-a:T21/c3/2/1/1/org/2`, helpers: the block families on cell-supported data

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2945,
2974-2977.

* `freeBlock_testW_cell`: the pin of `IsPeriodizedRelFreeBlockEvol` at the cylinder datum
  `f = J_a^{-1}`-preimage of a real cylinder test `φ` of period `d(s)` (the free cylinder flow
  `ω₀` from `free_cyl_exists_unique`): `F_rel τ σ` maps the zero extension of `φ` to data
  supported in the exit cell `d(t)` (the exterior dilation of zero exterior data vanishes).
* `freeBlock_cell_to_cell`: by density (`exists_test_approx_cell`) and closedness, `F_rel τ σ`
  maps all data supported in `d(s)` to data supported in `d(t)`.
* `dampedInt_cellSupported`: `A_rel τ` lands in the cell `d(r)` (pin on smooth compactly
  supported data, the cell zero extension, density of smooth data in `L²_m`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open CompactDuhamelGapSub BlockPropagatorSub BlockPropagatorInteriorSub RelExteriorSub

namespace RelBlockDiagonalSub

/-- A cylinder test of period `cellLen c a = c/√a`, rescaled by `J_a`, is a cylinder test of
period `c`. -/
theorem isCylTest_rescale {a c : ℝ} (ha : 0 < a) {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest (cellLen c a) φ) :
    B0579.IsCylTest c (fun x => (a ^ 2)⁻¹ * φ (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) where
  smooth := contDiff_const.mul (hφ.smooth.comp
    ((contDiff_fst.div_const _).prodMk (contDiff_snd.div_const _)))
  periodic x := by
    have h := hφ.periodic (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
    have hx : (x.1 + c) / Real.sqrt a = x.1 / Real.sqrt a + cellLen c a := by
      unfold cellLen
      rw [add_div]
    show (a ^ 2)⁻¹ * φ ((x.1 + c) / Real.sqrt a, x.2 / Real.sqrt a) =
      (a ^ 2)⁻¹ * φ (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
    rw [hx]
    exact congrArg _ h
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    refine ⟨R * Real.sqrt a, fun x hx => ?_⟩
    have h : R < |x.2 / Real.sqrt a| := by
      rw [abs_div, abs_of_pos hsa, lt_div_iff₀ hsa]
      exact hx
    show (a ^ 2)⁻¹ * φ (x.1 / Real.sqrt a, x.2 / Real.sqrt a) = 0
    rw [hR (x.1 / Real.sqrt a, x.2 / Real.sqrt a) h, mul_zero]

theorem jscaleInv_rescale {a : ℝ} (ha : 0 < a) (φ : ℝ × ℝ → ℝ) (y : ℝ × ℝ) :
    JscaleInv a (fun x => (((a ^ 2)⁻¹ * φ (x.1 / Real.sqrt a, x.2 / Real.sqrt a) : ℝ) : ℂ)) y =
      ((φ y : ℝ) : ℂ) := by
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have ha2 : (a ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 ha.ne'
  unfold JscaleInv
  have hy : (Real.sqrt a * y.1 / Real.sqrt a, Real.sqrt a * y.2 / Real.sqrt a) = y := by
    rw [mul_div_cancel_left₀ _ hsa, mul_div_cancel_left₀ _ hsa]
  show ((a ^ 2 : ℝ) : ℂ) *
      (((a ^ 2)⁻¹ * φ (Real.sqrt a * y.1 / Real.sqrt a, Real.sqrt a * y.2 / Real.sqrt a) : ℝ) : ℂ) =
    ((φ y : ℝ) : ℂ)
  rw [hy, ← Complex.ofReal_mul, ← mul_assoc, mul_inv_cancel₀ ha2, one_mul]

/-- **Pin on zero-extended cylinder tests** (SP 2941-2943): `F_rel τ σ` maps the zero extension
of a real cylinder test of period `d(s)` to data supported in the exit cell `d(t)`. -/
theorem freeBlock_testW_cell {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel) (hν : 0 < ν) (hm : 8 < m)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {σ τ : ℝ} (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτB : τ ≤ B)
    (hs : 0 ≤ ageAt ν t₁ σ) (ht : 0 ≤ ageAt ν t₁ τ) {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) φ) :
    IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
      (F_rel τ σ (testW m hφ)) := by
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha : 0 < clockA ν (ageAt ν t₁ σ) := by unfold clockA; positivity
  have hds : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) := cellLen_pos hν hs
  have hdt : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) := cellLen_pos hν ht
  have hf : B0579.IsCylTest (ν ^ (-2 : ℝ)) (fun x => (clockA ν (ageAt ν t₁ σ) ^ 2)⁻¹ *
      φ (x.1 / Real.sqrt (clockA ν (ageAt ν t₁ σ)), x.2 / Real.sqrt (clockA ν (ageAt ν t₁ σ)))) :=
    isCylTest_rescale (c := ν ^ (-2 : ℝ)) ha hφ
  obtain ⟨⟨ω₀, hω₀⟩, -⟩ := UnforcedLeray.Short.IIb.free_cyl_exists_unique m ν (ν ^ (-2 : ℝ)) hm
    hν hc tr htr (ageAt ν t₁ σ) hs _ (hf.memLp m)
  have hV := coeFn_testW m hφ
  have hagree : ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) →
        (testW m hφ : ℂ → ℂ) z = JscaleInv (clockA ν (ageAt ν t₁ σ))
          (fun x => (((clockA ν (ageAt ν t₁ σ) ^ 2)⁻¹ * φ (x.1 / Real.sqrt (clockA ν (ageAt ν t₁ σ)),
            x.2 / Real.sqrt (clockA ν (ageAt ν t₁ σ))) : ℝ) : ℂ)) (cToPlane z) := by
    filter_upwards [(Planar.volume_ac m).ae_le hV] with z hz hmem
    rw [hz, jscaleInv_rescale ha φ, cellZeroExt, Set.indicator_of_mem hmem]
  have h := hF σ τ hσ hστ hτB _ hf ω₀ hω₀ (testW m hφ) hagree
  have hVext : ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane z ∉ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) →
        (testW m hφ : ℂ → ℂ) z = 0 := by
    filter_upwards [(Planar.volume_ac m).ae_le hV] with z hz hnot
    rw [hz, cellZeroExt, Set.indicator_of_notMem hnot]
  set ρ : ℝ := cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) /
    cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) with hρdef
  have hρ : 0 < ρ := div_pos hds hdt
  have hV' : ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane (ρ • z) ∉ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) →
        (testW m hφ : ℂ → ℂ) (ρ • z) = 0 :=
    (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℂ)) hρ.ne').ae hVext
  filter_upwards [h, hV'] with z hz hz' hnot
  rw [hz, periodizedExt_apply_of_notMem hds hdt _ _ hnot]
  have hcp : cToPlane (ρ • z) = (ρ * (cToPlane z).1, ρ * (cToPlane z).2) := by
    simp [cToPlane]
  have hpl : planeToC (ρ * (cToPlane z).1, ρ * (cToPlane z).2) = ρ • z := by
    apply Complex.ext <;> simp [planeToC, cToPlane]
  have hnot' : cToPlane (ρ • z) ∉
      B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) := by
    rw [hcp]
    exact mt (scaleMem_cell_iff hds hdt _).1 hnot
  unfold extDilCocycle
  show _ * ((((ρ) ^ 4 : ℝ) : ℂ) *
    (testW m hφ : ℂ → ℂ) (planeToC (ρ * (cToPlane z).1, ρ * (cToPlane z).2))) = 0
  rw [hpl, hz' hnot', mul_zero, mul_zero]

/-- **`F_rel` maps cell data to cell data** (SP 2941-2943, density, SP 2974-2977). -/
theorem freeBlock_cell_to_cell {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel) (hν : 0 < ν) (hm : 8 < m)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {σ τ : ℝ} (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτB : τ ≤ B)
    (hs : 0 ≤ ageAt ν t₁ σ) (ht : 0 ≤ ageAt ν t₁ τ) (W : Planar.L2w m)
    (hW : IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) W) :
    IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) (F_rel τ σ W) := by
  refine isCellSupportedW_of_approx fun ε hε => ?_
  have hδ : 0 < ε / (‖F_rel τ σ‖ + 1) := by positivity
  obtain ⟨φ₁, φ₂, h₁, h₂, happrox⟩ := exists_test_approx_cell (cellLen_pos hν hs) W hW hδ
  refine ⟨F_rel τ σ (testW m h₁ + Complex.I • testW m h₂), ?_, ?_⟩
  · rw [map_add, map_smul]
    exact isCellSupportedW_add
      (freeBlock_testW_cell hF hν hm htr hσ hστ hτB hs ht h₁)
      (isCellSupportedW_smul _ (freeBlock_testW_cell hF hν hm htr hσ hστ hτB hs ht h₂))
  · calc ‖F_rel τ σ W - F_rel τ σ (testW m h₁ + Complex.I • testW m h₂)‖
        = ‖F_rel τ σ (W - (testW m h₁ + Complex.I • testW m h₂))‖ := by rw [map_sub]
      _ ≤ ‖F_rel τ σ‖ * ‖W - (testW m h₁ + Complex.I • testW m h₂)‖ :=
          (F_rel τ σ).le_opNorm _
      _ ≤ ‖F_rel τ σ‖ * (ε / (‖F_rel τ σ‖ + 1)) :=
          mul_le_mul_of_nonneg_left happrox.le (norm_nonneg _)
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (F_rel τ σ)]

/-- **`A_rel` lands in the cell** (SP 2920-2923, 2974-2978): the pin on smooth compactly supported
data is a cell zero extension, and smooth compactly supported data are dense in `L²_m`. -/
theorem dampedInt_cellSupported {κ : PlanarFrameKernels} {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hA : IsDampedComplBlockInt κ P ν m tr t₁ B A_rel) {τ : ℝ} (hτ : τ ∈ Icc 0 B)
    (V : Planar.L2w m) :
    IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) (A_rel τ V) := by
  have : IsLocallyFiniteMeasure (Planar.wMeasure m) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure m))
  refine isCellSupportedW_of_approx fun ε hε => ?_
  have hδ : 0 < ε / (‖A_rel τ‖ + 1) := by positivity
  obtain ⟨Ψ₀, hΨc, hΨs, hΨerr⟩ := (Lp.memLp V).exist_eLpNorm_sub_le (p := 2)
    ENNReal.ofNat_ne_top (by norm_num) hδ
  have hΨmem : MemLp Ψ₀ 2 (Planar.wMeasure m) :=
    hΨs.continuous.memLp_of_hasCompactSupport hΨc
  have hΦs : ContDiff ℝ ∞ (fun y => Ψ₀ (planeToC y)) := hΨs.comp contDiff_planeToC
  have hΦc : HasCompactSupport (fun y => Ψ₀ (planeToC y)) := by
    refine HasCompactSupport.intro (K := cToPlane '' tsupport Ψ₀)
      (hΨc.isCompact.image continuous_cToPlane) fun y hy => ?_
    have : planeToC y ∉ tsupport Ψ₀ := fun h => hy ⟨planeToC y, h, cToPlane_planeToC y⟩
    exact image_eq_zero_of_notMem_tsupport this
  have hX : ⇑(hΨmem.toLp Ψ₀) =ᵐ[volume] fun z => (fun y => Ψ₀ (planeToC y)) (cToPlane z) := by
    filter_upwards [(Planar.volume_ac m).ae_le hΨmem.coeFn_toLp] with z hz
    rw [hz, planeToC_cToPlane]
  have h := hA τ hτ _ hΦs hΦc (hΨmem.toLp Ψ₀) hX
  refine ⟨A_rel τ (hΨmem.toLp Ψ₀), ?_, ?_⟩
  · filter_upwards [h] with z hz hnot
    rw [hz, cellZeroExt, Set.indicator_of_notMem hnot]
  · have hVX : ‖V - hΨmem.toLp Ψ₀‖ ≤ ε / (‖A_rel τ‖ + 1) := by
      rw [Lp.norm_def]
      have he : eLpNorm (⇑(V - hΨmem.toLp Ψ₀)) 2 (Planar.wMeasure m) =
          eLpNorm (⇑V - Ψ₀) 2 (Planar.wMeasure m) := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [Lp.coeFn_sub V (hΨmem.toLp Ψ₀), hΨmem.coeFn_toLp] with z h1 h2
        rw [h1, Pi.sub_apply, h2, Pi.sub_apply]
      rw [he]
      exact ENNReal.toReal_le_of_le_ofReal hδ.le hΨerr
    calc ‖A_rel τ V - A_rel τ (hΨmem.toLp Ψ₀)‖ = ‖A_rel τ (V - hΨmem.toLp Ψ₀)‖ := by
          rw [map_sub]
      _ ≤ ‖A_rel τ‖ * ‖V - hΨmem.toLp Ψ₀‖ := (A_rel τ).le_opNorm _
      _ ≤ ‖A_rel τ‖ * (ε / (‖A_rel τ‖ + 1)) :=
          mul_le_mul_of_nonneg_left hVX (norm_nonneg _)
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (A_rel τ)]

end RelBlockDiagonalSub

end UnforcedLeray.Short.IIIa
