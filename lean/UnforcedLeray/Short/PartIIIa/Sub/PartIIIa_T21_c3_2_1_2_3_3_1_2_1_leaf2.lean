import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L2_1

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/2/1/2`: Leaf D (`FrelDualRep`)

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2918,
2937-2945, 2074-2105.

Proves `frelDualRep`: against the terminal-age test `ψ_χ` (`t = s(τ)`), the relative free block
evolution `F_rel τ σ X` is represented by `dualPair` with the backward cylinder solution `φ`
(`φ(t) = χ`). On real pinned data `X = J_{a(s)}⁻¹ f` on `C_{d(s)}`, both sides reduce via the
change of variables `x = √a y` (the exterior cocycle part vanishes on `C_{d(t)}` by
`periodizedExt_apply_of_mem` / `extDilCocycle_sub_cellZeroExt_eq_zero_on_cell`) to
`N(s,t)⁻¹ ∫_{C_c} ω(t) χ = N(s,t)⁻¹ ∫_{C_c} f φ(s)`, which holds by `IIb.cylWeakTimeDep` and
`IIb.cyl_rhs_zero`. Complex linearity extends this to `relFreeClassAt`, and `RelB3s` density plus
continuity of both sides in `X : Planar.L2w m` concludes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildTestedSplit

namespace FrameDuhamelSub

section Helpers

/-- Change of variables `x = √a y` on the centered cell:
`a⁻¹ ∫_{C_{c/√a}} g(√a y) (J_a⁻¹ f)(y) dy = ∫_{C_c} f(x) g(x) dx`. -/
private lemma cellScale_integral {c a : ℝ} (hc : 0 < c) (ha : 0 < a)
    (g f : B0579.Plane → ℝ) :
    ((a⁻¹ : ℝ) : ℂ) * ∫ z : ℂ,
      (B0579.cell (cellLen c a)).indicator
        (fun y => ((g (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) (cToPlane z) *
        JscaleInv a (fun x => ((f x : ℝ) : ℂ)) (cToPlane z) =
      (((∫ x in B0579.cell c, f x * g x) : ℝ) : ℂ) := by
  set s : ℝ := Real.sqrt a with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 ha
  have hsq : s ^ 2 = a := Real.sq_sqrt ha.le
  set K : ℝ × ℝ → ℂ := fun y =>
    (B0579.cell (cellLen c a)).indicator
      (fun y => ((g (s * y.1, s * y.2) : ℝ) : ℂ)) y *
      JscaleInv a (fun x => ((f x : ℝ) : ℂ)) y with hK_def
  have hemb : MeasurableEmbedding cToPlane := by
    rw [cToPlane_eq_equiv]
    exact Complex.measurableEquivRealProd.measurableEmbedding
  have hcomp : (∫ z : ℂ, K (cToPlane z)) = ∫ y : ℝ × ℝ, K y :=
    measurePreserving_cToPlane_volume.integral_comp hemb K
  set H : ℝ × ℝ → ℝ := (B0579.cell c).indicator (fun x => f x * g x) with hH_def
  have hmem : ∀ y : ℝ × ℝ, s • y ∈ B0579.cell c ↔ y ∈ B0579.cell (cellLen c a) := by
    intro y
    simp only [B0579.cell, cellLen, ← hs_def, Set.mem_prod, Set.mem_univ, and_true,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Set.mem_Ico]
    have e : c / 2 = (c / s / 2) * s := by field_simp
    have e' : -(c / 2) = -(c / s / 2) * s := by rw [e]; ring
    rw [e', e]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by nlinarith, by nlinarith⟩,
      fun ⟨h1, h2⟩ => ⟨by nlinarith, by nlinarith⟩⟩
  have hpt : ∀ y : ℝ × ℝ, K y = (((a ^ 2 * H (s • y)) : ℝ) : ℂ) := by
    intro y
    by_cases hy : y ∈ B0579.cell (cellLen c a)
    · have hx : s • y ∈ B0579.cell c := (hmem y).2 hy
      have es : s • y = (s * y.1, s * y.2) := by ext <;> simp [smul_eq_mul]
      rw [hK_def, hH_def]
      dsimp only
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, es]
      unfold JscaleInv
      rw [← hs_def]
      push_cast
      ring
    · have hx : s • y ∉ B0579.cell c := fun h => hy ((hmem y).1 h)
      rw [hK_def, hH_def]
      dsimp only
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
      simp
  have hfr : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hsmul : ∫ y : ℝ × ℝ, H (s • y) = |((s ^ Module.finrank ℝ (ℝ × ℝ))⁻¹)| • ∫ x : ℝ × ℝ, H x :=
    MeasureTheory.Measure.integral_comp_smul volume H s
  rw [hfr, hsq, abs_of_pos (inv_pos.2 ha), smul_eq_mul] at hsmul
  change ((a⁻¹ : ℝ) : ℂ) * (∫ z : ℂ, K (cToPlane z)) = _
  rw [hcomp]
  have hKint : (∫ y : ℝ × ℝ, K y) =
      (((a ^ 2 * (a⁻¹ * ∫ x in B0579.cell c, f x * g x)) : ℝ) : ℂ) := by
    simp_rw [hpt]
    rw [integral_complex_ofReal, integral_const_mul, hsmul, hH_def,
      integral_indicator (B0579.measurableSet_cell c)]
  rw [hKint]
  have ha_ne : a ≠ 0 := ha.ne'
  push_cast
  field_simp [ha_ne]

/-- Pairing in `Planar.L2w m` against a vector a.e. equal to `testPsiFun m c a χ`. -/
private lemma inner_testPsi_eq {m c a : ℝ} (χ : B0579.Plane → ℝ)
    (ψ Y : Planar.L2w m) (hψ : ⇑ψ =ᵐ[volume] testPsiFun m c a χ) :
    ⟪ψ, Y⟫_ℂ = ((a⁻¹ : ℝ) : ℂ) * ∫ z : ℂ,
      (B0579.cell (cellLen c a)).indicator
        (fun y => ((χ (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) (cToPlane z) *
        (Y : ℂ → ℂ) z := by
  rw [MeasureTheory.L2.inner_def]
  change ∫ z, ⟪(ψ : ℂ → ℂ) z, (Y : ℂ → ℂ) z⟫_ℂ ∂(volume.withDensity (Planar.wDensity m)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (Planar.measurable_wDensity m)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hψ] with z hz
  dsimp only [Planar.wDensity]
  rw [ENNReal.toReal_ofReal (by positivity), hz]
  have hw : (1 + ‖z‖ ^ 2) ^ m ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  unfold testPsiFun
  by_cases hmem : cToPlane z ∈ B0579.cell (cellLen c a)
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, Complex.real_smul,
      RCLike.inner_apply', Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      mul_div_cancel₀ _ hw, Complex.ofReal_mul, mul_assoc]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    simp

/-- Cylinder duality on `[s, t] ⊆ [t₁, t]` between a forward `IsFreeCylFlow` and `IsBwdSol`. -/
private lemma cyl_bwd_duality {m ν t₁ s t : ℝ} (hm : 8 < m) (hν : 0 < ν)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (ht₁ : 0 ≤ t₁) (hs1 : t₁ ≤ s) (hst : s ≤ t)
    {f : B0579.Plane → ℝ} {ω₀ : ℝ → B0579.Plane → ℝ}
    (hω₀ : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s f ω₀)
    {χ : B0579.Plane → ℝ} {φ : ℝ → B0579.Plane → ℝ}
    (hφ : IsBwdSol ν tr t₁ t χ φ) :
    ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ω₀ t x * χ x =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f x * φ s x := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ht0 : 0 ≤ t := ht₁.trans (hs1.trans hst)
  obtain ⟨hφt, hφsp, hφpde⟩ := hφ
  have hsubIcc : Icc s t ⊆ Icc t₁ t := Icc_subset_Icc hs1 le_rfl
  have hsubIoo : Ioo s t ⊆ Ioo t₁ t := Ioo_subset_Ioo hs1 le_rfl
  have hφsp_st : UnforcedLeray.Short.IIb.CylEtaSpatial (ν ^ (-2 : ℝ)) s t φ :=
    ⟨hφsp.smooth.mono (Set.prod_mono hsubIcc Subset.rfl),
      fun r hr x => hφsp.periodic r (hsubIcc hr) x,
      fun N => let ⟨C, hC⟩ := hφsp.decay N; ⟨C, fun r hr x => hC r (hsubIcc hr) x⟩⟩
  have hφpde_st : ∀ r ∈ Ioo s t, ∀ x : B0579.Plane,
      HasDerivAt (fun r' => φ r' x)
        (-(ν * UnforcedLeray.Short.IIb.lapP (φ r) x + (tr.v r x 0 * B0579.pd 0 (φ r) x +
          tr.v r x 1 * B0579.pd 1 (φ r) x))) r :=
    fun r hr x => hφpde r (hsubIoo hr) x
  obtain ⟨V, _, hV⟩ := UnforcedLeray.Short.IIb.driftC2Bdd_of_buc (tr := tr) htr ht0
  have hMr : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ 2 * V := by
    intro r hr x
    have hr0 : r ∈ Icc 0 t := ⟨(ht₁.trans hs1).trans hr.1, hr.2⟩
    have h0 := (hV r hr0 x 0).1
    have h1 := (hV r hr0 x 1).1
    linarith
  have hφ_test : UnforcedLeray.Short.IIb.CylEtaTest (ν ^ (-2 : ℝ)) s t φ :=
    hφsp_st.toCylEtaTest hν.le tr.v hMr hφpde_st
  have k := UnforcedLeray.Short.IIb.cylWeakTimeDep m hm ν (ν ^ (-2 : ℝ)) tr s f ω₀ hc hω₀
    t φ hst hφ_test ⟨2 * V, hMr⟩
  rw [UnforcedLeray.Short.IIb.cyl_rhs_zero hst ω₀ φ tr.v _ hφpde_st, hφt] at k
  linarith

/-- Measurability and uniform boundedness of the cell-indicator test factor in `dualPair`. -/
private lemma dualKernel_meas_bdd {c t₁ t s d a : ℝ}
    {φ : ℝ → B0579.Plane → ℝ} (hφsp : UnforcedLeray.Short.IIb.CylEtaSpatial c t₁ t φ)
    (hs : s ∈ Icc t₁ t) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      Measurable (fun z : ℂ => (B0579.cell d).indicator
        (fun y => ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) (cToPlane z)) ∧
      ∀ z : ℂ, ‖(B0579.cell d).indicator
        (fun y => ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) (cToPlane z)‖ ≤ C₀ := by
  obtain ⟨C, hC⟩ := hφsp.decay 0
  have hφ_cont : Continuous (φ s) := by
    have hmap : MapsTo (fun x : B0579.Plane => (s, x)) univ (Icc t₁ t ×ˢ univ) :=
      fun x _ => ⟨hs, mem_univ x⟩
    have hc_on : ContinuousOn (φ s) univ :=
      hφsp.smooth.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap
    exact continuousOn_univ.1 hc_on
  have hinner_cont : Continuous (fun y : ℝ × ℝ =>
      ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ_cont.comp
      ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)))
  have hmeas : Measurable (fun z : ℂ => (B0579.cell d).indicator
      (fun y => ((φ s (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ) : ℂ)) (cToPlane z)) :=
    (hinner_cont.measurable.indicator (B0579.measurableSet_cell d)).comp measurable_cToPlane
  refine ⟨max C 0, le_max_right _ _, hmeas, fun z => ?_⟩
  by_cases hmem : cToPlane z ∈ B0579.cell d
  · rw [Set.indicator_of_mem hmem, Complex.norm_real, Real.norm_eq_abs]
    have hb := hC s hs (Real.sqrt a * (cToPlane z).1, Real.sqrt a * (cToPlane z).2)
    simp only [Real.rpow_zero, mul_one] at hb
    have h1 := abs_nonneg (B0579.pd 0 (φ s) (Real.sqrt a * (cToPlane z).1, Real.sqrt a * (cToPlane z).2))
    have h2 := abs_nonneg (B0579.pd 1 (φ s) (Real.sqrt a * (cToPlane z).1, Real.sqrt a * (cToPlane z).2))
    have h3 := abs_nonneg (UnforcedLeray.Short.IIb.lapP (φ s)
      (Real.sqrt a * (cToPlane z).1, Real.sqrt a * (cToPlane z).2))
    exact (by linarith : |φ s _| ≤ C).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hmem, norm_zero]
    exact le_max_right _ _

private lemma integrable_mul_of_meas_bdd {m C₀ : ℝ} (hm1 : 1 < m) (_hC₀ : 0 ≤ C₀)
    {Φ : ℂ → ℂ} (hΦm : Measurable Φ) (hΦb : ∀ z, ‖Φ z‖ ≤ C₀) (Y : Planar.L2w m) :
    Integrable (fun z : ℂ => Φ z * (Y : ℂ → ℂ) z) volume := by
  have hY : Integrable (Y : ℂ → ℂ) volume := Planar.integrable_L2w hm1 Y
  refine (hY.norm.const_mul C₀).mono' (hΦm.aestronglyMeasurable.mul hY.aestronglyMeasurable) ?_
  filter_upwards with z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hΦb z) (norm_nonneg _)

end Helpers

/-- **Leaf D (duality representation, SP 2937-2945, 2074-2105)**: against `ψ_χ`, `F_rel τ σ` is
represented by `dualPair` with the backward cylinder solution `φ`. -/
theorem frelDualRep (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.FrameDuhamelSub.FrelDualRep κ := by
  intro P m K B b ν tr t₁ t₂ ctx F_rel hFr τ hτ χ _hχ φ hφ ψ hψ σ hσ X
  have ⟨_hκ, _hP, hm, _hB, _hb, hν, _hF, htr, ht₁, ht₁₂, _hbt, hBz⟩ := ctx
  have hm1 : 1 < m := by linarith
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨hs1, hst, _ht2⟩ := RelB4locAux.ageAt_props hν ht₁ ht₁₂ hBz hσ.1 hσ.2 hτ.2
  have hs0 : 0 ≤ ageAt ν t₁ σ := ht₁.trans hs1
  have ht0 : 0 ≤ ageAt ν t₁ τ := hs0.trans hst
  have has : 0 < clockA ν (ageAt ν t₁ σ) := by unfold clockA; positivity
  have hat : 0 < clockA ν (ageAt ν t₁ τ) := by unfold clockA; positivity
  have hds : 0 < dOf ν t₁ σ := div_pos hc (Real.sqrt_pos.2 has)
  have hdt : 0 < dOf ν t₁ τ := div_pos hc (Real.sqrt_pos.2 hat)
  -- Step 1: Verify the identity on real pinned data `(f, ω₀, U)`.
  have hpin_real : ∀ (f : B0579.Plane → ℝ), B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
      ∀ (ω₀ : ℝ → B0579.Plane → ℝ),
        UnforcedLeray.Short.IIb.IsFreeCylFlow m tr (ageAt ν t₁ σ) f ω₀ →
      ∀ (U : Planar.L2w m),
        (∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell (dOf ν t₁ σ) →
          (U : ℂ → ℂ) z = JscaleInv (clockA ν (ageAt ν t₁ σ))
            (fun x => ((f x : ℝ) : ℂ)) (cToPlane z)) →
        ⟪ψ, F_rel τ σ U⟫_ℂ = dualPair P ν t₁ τ φ σ ⇑U := by
    intro f hf ω₀ hω₀ U hUc
    have hFU := hFr σ τ hσ.1 hσ.2 hτ.2 f hf ω₀ hω₀ U hUc
    -- Compute LHS: `⟪ψ, F_rel τ σ U⟫_ℂ = N⁻¹ ∫_{C_c} ω₀(t) χ`
    have hlhs : ⟪ψ, F_rel τ σ U⟫_ℂ =
        (((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ : ℝ) : ℂ) *
          (((∫ x in B0579.cell (ν ^ (-2 : ℝ)), ω₀ (ageAt ν t₁ τ) x * χ x) : ℝ) : ℂ) := by
      rw [inner_testPsi_eq χ ψ (F_rel τ σ U) hψ]
      have hae_lhs :
          (fun z : ℂ =>
            (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))).indicator
              (fun y => ((χ (Real.sqrt (clockA ν (ageAt ν t₁ τ)) * y.1,
                Real.sqrt (clockA ν (ageAt ν t₁ τ)) * y.2) : ℝ) : ℂ)) (cToPlane z) *
              (F_rel τ σ U : ℂ → ℂ) z) =ᵐ[volume]
          fun z : ℂ =>
            (((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ : ℝ) : ℂ) *
              ((B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))).indicator
                (fun y => ((χ (Real.sqrt (clockA ν (ageAt ν t₁ τ)) * y.1,
                  Real.sqrt (clockA ν (ageAt ν t₁ τ)) * y.2) : ℝ) : ℂ)) (cToPlane z) *
                JscaleInv (clockA ν (ageAt ν t₁ τ))
                  (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ)) (cToPlane z)) := by
        filter_upwards [hFU] with z hz
        rw [hz]
        by_cases hmem : cToPlane z ∈ B0579.cell (dOf ν t₁ τ)
        · have hmem' : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) :=
            hmem
          rw [Set.indicator_of_mem hmem',
            periodizedExt_apply_of_mem hds hdt _ _ hmem]
          push_cast
          ring
        · have hmem' : cToPlane z ∉ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) :=
            hmem
          rw [Set.indicator_of_notMem hmem']
          simp
      rw [integral_congr_ae hae_lhs, integral_const_mul, ← mul_assoc,
        mul_comm (((clockA ν (ageAt ν t₁ τ))⁻¹ : ℝ) : ℂ), mul_assoc,
        cellScale_integral hc hat χ (ω₀ (ageAt ν t₁ τ))]
    -- Compute RHS: `dualPair ... U = N⁻¹ ∫_{C_c} f φ(s)`
    have hrhs : dualPair P ν t₁ τ φ σ ⇑U =
        (((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ : ℝ) : ℂ) *
          (((∫ x in B0579.cell (ν ^ (-2 : ℝ)), f x * φ (ageAt ν t₁ σ) x) : ℝ) : ℂ) := by
      unfold dualPair
      have hae_rhs :
          (fun z : ℂ =>
            (B0579.cell (dOf ν t₁ σ)).indicator
              (fun y => ((φ (ageAt ν t₁ σ) (Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.1,
                Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.2) : ℝ) : ℂ)) (cToPlane z) *
              (U : ℂ → ℂ) z) =ᵐ[volume]
          fun z : ℂ =>
            (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))).indicator
              (fun y => ((φ (ageAt ν t₁ σ) (Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.1,
                Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.2) : ℝ) : ℂ)) (cToPlane z) *
              JscaleInv (clockA ν (ageAt ν t₁ σ))
                (fun x => ((f x : ℝ) : ℂ)) (cToPlane z) := by
        filter_upwards [hUc] with z hz
        dsimp only [dOf] at hUc hz ⊢
        by_cases hmem : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
        · rw [Set.indicator_of_mem hmem, hz hmem]
        · rw [Set.indicator_of_notMem hmem]
          simp
      rw [integral_congr_ae hae_rhs, Complex.ofReal_mul, mul_assoc,
        cellScale_integral hc has (φ (ageAt ν t₁ σ)) f]
    rw [hlhs, hrhs, cyl_bwd_duality hm hν htr ht₁ hs1 hst hω₀ hφ]
  -- Step 2: Linearity and Lipschitz bound of `dualPair` on `Planar.L2w m`.
  obtain ⟨C₀, hC₀, hΦm, hΦb⟩ := dualKernel_meas_bdd hφ.2.1 (⟨hs1, hst⟩ : ageAt ν t₁ σ ∈ Icc t₁ (ageAt ν t₁ τ))
  set Φ : ℂ → ℂ := fun z => (B0579.cell (dOf ν t₁ σ)).indicator
    (fun y => ((φ (ageAt ν t₁ σ) (Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.1,
      Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.2) : ℝ) : ℂ)) (cToPlane z) with hΦ_def
  set α : ℂ := (((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ *
    (clockA ν (ageAt ν t₁ σ))⁻¹ : ℝ) : ℂ) with hα_def
  have hdp_eq : ∀ Y : Planar.L2w m, dualPair P ν t₁ τ φ σ ⇑Y = α * ∫ z : ℂ, Φ z * (Y : ℂ → ℂ) z :=
    fun _ => rfl
  have hdp_add_smul : ∀ U V : Planar.L2w m,
      dualPair P ν t₁ τ φ σ ⇑(U + Complex.I • V) =
        dualPair P ν t₁ τ φ σ ⇑U + Complex.I * dualPair P ν t₁ τ φ σ ⇑V := by
    intro U V
    have hIU := integrable_mul_of_meas_bdd hm1 hC₀ hΦm hΦb U
    have hIV := integrable_mul_of_meas_bdd hm1 hC₀ hΦm hΦb V
    have hae : (fun z : ℂ => Φ z * ((U + Complex.I • V : Planar.L2w m) : ℂ → ℂ) z) =ᵐ[volume]
        fun z : ℂ => Φ z * (U : ℂ → ℂ) z + Complex.I * (Φ z * (V : ℂ → ℂ) z) := by
      filter_upwards [(Planar.volume_ac m).ae_le (Lp.coeFn_add U (Complex.I • V)),
        (Planar.volume_ac m).ae_le (Lp.coeFn_smul Complex.I V)] with z h1 h2
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hdp_eq, hdp_eq, hdp_eq, integral_congr_ae hae,
      integral_add hIU (hIV.const_mul Complex.I), integral_const_mul]
    ring
  have hdp_sub : ∀ U V : Planar.L2w m,
      dualPair P ν t₁ τ φ σ ⇑U - dualPair P ν t₁ τ φ σ ⇑V =
        dualPair P ν t₁ τ φ σ ⇑(U - V) := by
    intro U V
    have hIU := integrable_mul_of_meas_bdd hm1 hC₀ hΦm hΦb U
    have hIV := integrable_mul_of_meas_bdd hm1 hC₀ hΦm hΦb V
    have hae : (fun z : ℂ => Φ z * ((U - V : Planar.L2w m) : ℂ → ℂ) z) =ᵐ[volume]
        fun z : ℂ => Φ z * (U : ℂ → ℂ) z - Φ z * (V : ℂ → ℂ) z := by
      filter_upwards [(Planar.volume_ac m).ae_le (Lp.coeFn_sub U V)] with z h1
      rw [h1, Pi.sub_apply, mul_sub]
    rw [hdp_eq, hdp_eq, hdp_eq, integral_congr_ae hae, integral_sub hIU hIV, mul_sub]
  have hdp_bound : ∀ Y : Planar.L2w m,
      ‖dualPair P ν t₁ τ φ σ ⇑Y‖ ≤ ‖α‖ * C₀ * B0008.CM m * ‖Y‖ := by
    intro Y
    have hIY : Integrable (Y : ℂ → ℂ) volume := Planar.integrable_L2w hm1 Y
    rw [hdp_eq, norm_mul]
    have h1 : ‖∫ z : ℂ, Φ z * (Y : ℂ → ℂ) z‖ ≤ ∫ z : ℂ, ‖Φ z * (Y : ℂ → ℂ) z‖ :=
      norm_integral_le_integral_norm _
    have h2 : ∫ z : ℂ, ‖Φ z * (Y : ℂ → ℂ) z‖ ≤ ∫ z : ℂ, C₀ * ‖(Y : ℂ → ℂ) z‖ := by
      refine integral_mono_ae (integrable_mul_of_meas_bdd hm1 hC₀ hΦm hΦb Y).norm
        (hIY.norm.const_mul C₀) (Eventually.of_forall fun z => ?_)
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hΦb z) (norm_nonneg _)
    have h3 : ∫ z : ℂ, C₀ * ‖(Y : ℂ → ℂ) z‖ ≤ C₀ * (B0008.CM m * ‖Y‖) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (B0008.integral_norm_le hm1 Y) hC₀
    calc ‖α‖ * ‖∫ z : ℂ, Φ z * (Y : ℂ → ℂ) z‖
        ≤ ‖α‖ * (C₀ * (B0008.CM m * ‖Y‖)) :=
          mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) (norm_nonneg _)
      _ = ‖α‖ * C₀ * B0008.CM m * ‖Y‖ := by ring
  -- Step 3: Extend to the complex per-`σ` class `relFreeClassAt ν m tr t₁ σ`.
  have hclass : ∀ W ∈ RelRegularityOrg2.relFreeClassAt ν m tr t₁ σ,
      ⟪ψ, F_rel τ σ W⟫_ℂ = dualPair P ν t₁ τ φ σ ⇑W := by
    rintro W ⟨f₁, f₂, hf₁, hf₂, ⟨ω₁, hω₁⟩, ⟨ω₂, hω₂⟩, hWc⟩
    have hf₂_lp : MemLp f₂ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := hf₂.memLp m
    set E₂ : Planar.L2w m :=
      RelRegularityOrg2.RelB1cAux.b1cCellPart hm1 (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) f₂
    set W₁ : Planar.L2w m := W - Complex.I • E₂
    have hE₂c : ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell (dOf ν t₁ σ) →
        (E₂ : ℂ → ℂ) z = JscaleInv (clockA ν (ageAt ν t₁ σ))
          (fun x => ((f₂ x : ℝ) : ℂ)) (cToPlane z) := by
      filter_upwards [(Planar.volume_ac m).ae_le
        (RelRegularityOrg2.RelB1cAux.b1c_coeFn_cellPart hm1 hc has hf₂_lp)] with z hz hin
      rw [hz, cellZeroExt, Set.indicator_of_mem hin]
    have hW₁c : ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell (dOf ν t₁ σ) →
        (W₁ : ℂ → ℂ) z = JscaleInv (clockA ν (ageAt ν t₁ σ))
          (fun x => ((f₁ x : ℝ) : ℂ)) (cToPlane z) := by
      filter_upwards [(Planar.volume_ac m).ae_le (Lp.coeFn_sub W (Complex.I • E₂)),
        (Planar.volume_ac m).ae_le (Lp.coeFn_smul Complex.I E₂), hE₂c, hWc] with z h1 h2 h3 h4 hin
      rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3 hin, h4 hin, smul_eq_mul]
      simp only [JscaleInv]
      ring
    have hW_eq : W = W₁ + Complex.I • E₂ := by simp [W₁]
    rw [hW_eq, map_add, map_smul, inner_add_right, inner_smul_right, hdp_add_smul,
      hpin_real f₁ hf₁ ω₁ hω₁ W₁ hW₁c, hpin_real f₂ hf₂ ω₂ hω₂ E₂ hE₂c]
  -- Step 4: Conclude on all `X : Planar.L2w m` by `RelB3s` density and continuity.
  have hσB : σ ∈ Icc (0 : ℝ) B := ⟨hσ.1, hσ.2.trans hτ.2⟩
  have hdense := RelRegularityOrg2.relB3s_leaf κ P m K B b ν tr t₁ t₂ ctx σ hσB
  have hCM_nonneg : 0 ≤ B0008.CM m := by unfold B0008.CM; exact Real.sqrt_nonneg _
  set L : ℝ := ‖ψ‖ * ‖F_rel τ σ‖ + ‖α‖ * C₀ * B0008.CM m + 1 with hL_def
  have hL_pos : 0 < L := by positivity
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨W, hW_dist, hW_mem⟩ := Metric.dense_iff.1 hdense X (ε / L) (div_pos hε hL_pos)
  rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hW_dist
  rw [dist_eq_norm]
  have hdiff : ⟪ψ, F_rel τ σ X⟫_ℂ - dualPair P ν t₁ τ φ σ ⇑X =
      ⟪ψ, F_rel τ σ (X - W)⟫_ℂ - dualPair P ν t₁ τ φ σ ⇑(X - W) := by
    have h1 : ⟪ψ, F_rel τ σ X⟫_ℂ - ⟪ψ, F_rel τ σ W⟫_ℂ = ⟪ψ, F_rel τ σ (X - W)⟫_ℂ := by
      rw [map_sub, inner_sub_right]
    rw [← hdp_sub X W, ← hclass W hW_mem]
    linear_combination h1
  rw [hdiff]
  have hb1 : ‖⟪ψ, F_rel τ σ (X - W)⟫_ℂ‖ ≤ ‖ψ‖ * ‖F_rel τ σ‖ * ‖X - W‖ := by
    calc ‖⟪ψ, F_rel τ σ (X - W)⟫_ℂ‖ ≤ ‖ψ‖ * ‖F_rel τ σ (X - W)‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ‖ * (‖F_rel τ σ‖ * ‖X - W‖) :=
          mul_le_mul_of_nonneg_left ((F_rel τ σ).le_opNorm _) (norm_nonneg _)
      _ = ‖ψ‖ * ‖F_rel τ σ‖ * ‖X - W‖ := by ring
  have hb2 := hdp_bound (X - W)
  calc ‖⟪ψ, F_rel τ σ (X - W)⟫_ℂ - dualPair P ν t₁ τ φ σ ⇑(X - W)‖
      ≤ ‖⟪ψ, F_rel τ σ (X - W)⟫_ℂ‖ + ‖dualPair P ν t₁ τ φ σ ⇑(X - W)‖ := norm_sub_le _ _
    _ ≤ ‖ψ‖ * ‖F_rel τ σ‖ * ‖X - W‖ + ‖α‖ * C₀ * B0008.CM m * ‖X - W‖ := add_le_add hb1 hb2
    _ ≤ L * ‖X - W‖ := by
        have := norm_nonneg (X - W)
        nlinarith [hL_def]
    _ ≤ L * (ε / L) := mul_le_mul_of_nonneg_left hW_dist.le hL_pos.le
    _ = ε := mul_div_cancel₀ ε hL_pos.ne'

end FrameDuhamelSub

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
