import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

/-!
# Part III-a, `PartIII-a:T21/2/1/2/4`: the duality (Fubini) identity for the adjoint kernel

Source of record: `the November 2 reference manuscript` lines 3052-3057
(the adjoint `K_d^T` is characterised by `∫ χ ψ = ∫ F · K_d ψ`).  Proof of `kerAdjFubini_of`:
the kernel is `d`-periodic with integrable near part and bounded far part (`KerNearFar`), a test
`ψ` is bounded, periodic and has finite `L¹(cell)` norm, so the transported test integral
`∫_cell |K_d(x - y)| |ψ(y)| dy` is bounded uniformly in `x`; Tonelli gives the joint integrability
of `F j x · K_d(x - y) · ψ y` on `cell × cell`, and `integral_integral_swap` is the identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace AdjFubiniAux

theorem enorm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ₑ = ‖r‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

theorem cell_eq (d : ℝ) : UnforcedLeray.B0579.cell d = UnforcedLeray.Cyl.cell d := by
  unfold UnforcedLeray.B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

/-- A cylinder test is bounded on the plane and has finite `L¹(cell)` norm. -/
theorem test_facts {d : ℝ} (hd : 0 < d) {ψ : ℝ × ℝ → ℝ} (hψ : UnforcedLeray.B0579.IsCylTest d ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ y, |ψ y| ≤ B) ∧
      ∫⁻ y in UnforcedLeray.Cyl.cell d, ‖ψ y‖ₑ < ⊤ := by
  obtain ⟨R, hR⟩ := hψ.band
  set K : Set (ℝ × ℝ) := Icc (-(d / 2)) (d / 2) ×ˢ Icc (-|R|) |R| with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hψ.continuous.continuousOn
  have hvan : ∀ x ∈ UnforcedLeray.Cyl.cell d, x ∉ K → ψ x = 0 := by
    intro x hx hxK
    refine hR x ?_
    by_contra hcon
    push Not at hcon
    apply hxK
    have h1 := UnforcedLeray.Cyl.mem_cell.1 hx
    refine ⟨⟨by linarith [h1.1, neg_div d 2], by linarith [h1.2]⟩, abs_le.1 ?_⟩
    exact le_trans hcon (le_abs_self R)
  have hcell : ∀ x ∈ UnforcedLeray.Cyl.cell d, |ψ x| ≤ max C 0 := by
    intro x hx
    by_cases hxK : x ∈ K
    · rw [← Real.norm_eq_abs]; exact (hC x hxK).trans (le_max_left _ _)
    · rw [hvan x hx hxK]; simp
  have hd' : 0 < d := hd
  have hglob : ∀ y : ℝ × ℝ, |ψ y| ≤ max C 0 := by
    intro y
    have hmem := toIcoMod_mem_Ico hd' (-(d / 2)) y.1
    set x' : ℝ × ℝ := (toIcoMod hd' (-(d / 2)) y.1, y.2) with hx'
    have hx'c : x' ∈ UnforcedLeray.Cyl.cell d := by
      rw [UnforcedLeray.Cyl.mem_cell]
      refine ⟨by linarith [hmem.1, neg_div d 2], ?_⟩
      have := hmem.2
      show toIcoMod hd' (-(d / 2)) y.1 < d / 2
      linarith
    have hy : y = (x'.1 + (toIcoDiv hd' (-(d / 2)) y.1) • d, x'.2) := by
      have := self_sub_toIcoMod hd' (-(d / 2)) y.1
      ext
      · show y.1 = toIcoMod hd' (-(d / 2)) y.1 + (toIcoDiv hd' (-(d / 2)) y.1) • d
        linarith
      · rfl
    have hper : UnforcedLeray.Cyl.IsPeriodic d ψ := hψ.periodic
    have := hper.add_zsmul (toIcoDiv hd' (-(d / 2)) y.1) x'
    rw [← hy] at this
    rw [this]
    exact hcell x' hx'c
  refine ⟨max C 0, le_max_right _ _, hglob, ?_⟩
  calc ∫⁻ y in UnforcedLeray.Cyl.cell d, ‖ψ y‖ₑ
      ≤ ∫⁻ y in UnforcedLeray.Cyl.cell d, K.indicator (fun _ => ENNReal.ofReal (max C 0)) y := by
        refine setLIntegral_mono' (UnforcedLeray.Cyl.measurableSet_cell d) fun x hx => ?_
        by_cases hxK : x ∈ K
        · rw [indicator_of_mem hxK, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (hcell x hx)
        · rw [hvan x hx hxK]; simp
    _ ≤ ∫⁻ y, K.indicator (fun _ => ENNReal.ofReal (max C 0)) y := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (max C 0) * volume K := lintegral_indicator_const hKc.measurableSet _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKc.measure_lt_top

open UnforcedLeray in
/-- The transported test integral of the kernel is bounded uniformly in `x`. -/
theorem kernel_test_bound {d : ℝ} (hd : 1 ≤ d) {C B : ℝ} (hC0 : 0 ≤ C)
    (hper : ∀ (z : ℝ × ℝ) (j : Fin 2), kerD d (z.1 + d, z.2) j = kerD d z j)
    (hnear : (∫⁻ z in B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ j, ‖kerD d z j‖ₑ) ≤
      ENNReal.ofReal C)
    (hfar : ∀ z ∈ B0579.cell d, z ∉ Metric.ball (0 : ℝ × ℝ) 1 → ∀ j, |kerD d z j| ≤ C)
    (hmeas : ∀ j : Fin 2, Measurable fun z => kerD d z j)
    {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest d ψ) (hB : ∀ y, |ψ y| ≤ B)
    (hB0 : 0 ≤ B) (j : Fin 2) (x : ℝ × ℝ) :
    ∫⁻ y in B0579.cell d, ‖kerD d (x - y) j‖ₑ * ‖ψ y‖ₑ ≤
      ENNReal.ofReal B * ENNReal.ofReal C + ENNReal.ofReal C * ∫⁻ y in Cyl.cell d, ‖ψ y‖ₑ := by
  have hd0 : 0 < d := by linarith
  rw [cell_eq] at hnear hfar ⊢
  have hψper : Cyl.IsPeriodic d ψ := hψ.periodic
  have hkper : Cyl.IsPeriodic d (fun z : ℝ × ℝ => ‖kerD d z j‖ₑ) := fun z => by
    simp only [hper z j]
  have hGper : Cyl.IsPeriodic d (fun w : ℝ × ℝ => ‖kerD d w j‖ₑ * ‖ψ (x - w)‖ₑ) := by
    intro w
    have h1 : ψ (x - (w.1 + d, w.2)) = ψ (x - w) := by
      have := hψper.sub_eq (x - w)
      rw [← this]
      congr 1
      ext <;> simp; ring
    simp only [h1, hper w j]
  have hψper' : Cyl.IsPeriodic d (fun y : ℝ × ℝ => ‖ψ y‖ₑ) := fun z => by simp only [hψper z]
  have e1 : ∫⁻ y in Cyl.cell d, ‖kerD d (x - y) j‖ₑ * ‖ψ y‖ₑ =
      ∫⁻ w in Cyl.cell d, ‖kerD d w j‖ₑ * ‖ψ (x - w)‖ₑ := by
    have := Cyl.lintegral_cell_comp_sub_left hd0 hGper x
    rw [← this]
    refine lintegral_congr fun y => ?_
    simp
  rw [e1]
  have hmb : MeasurableSet (Metric.ball (0 : ℝ × ℝ) 1) := Metric.isOpen_ball.measurableSet
  rw [← lintegral_inter_add_diff _ _ hmb]
  gcongr
  · calc ∫⁻ w in Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ‖kerD d w j‖ₑ * ‖ψ (x - w)‖ₑ
        ≤ ∫⁻ w in Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
            ENNReal.ofReal B * ∑ i, ‖kerD d w i‖ₑ := by
          refine setLIntegral_mono' ((Cyl.measurableSet_cell d).inter hmb) fun w _ => ?_
          rw [mul_comm (ENNReal.ofReal B)]
          refine mul_le_mul' ?_ ?_
          · have := Finset.single_le_sum (f := fun i => ‖kerD d w i‖ₑ) (fun _ _ => bot_le)
              (Finset.mem_univ j)
            exact this
          · rw [← ofReal_norm, Real.norm_eq_abs]
            exact ENNReal.ofReal_le_ofReal (hB _)
      _ = ENNReal.ofReal B * ∫⁻ w in Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ i, ‖kerD d w i‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  · calc ∫⁻ w in Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1, ‖kerD d w j‖ₑ * ‖ψ (x - w)‖ₑ
        ≤ ∫⁻ w in Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1, ENNReal.ofReal C * ‖ψ (x - w)‖ₑ := by
          refine setLIntegral_mono' ((Cyl.measurableSet_cell d).diff hmb) fun w hw => ?_
          gcongr
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (hfar w hw.1 hw.2 j)
      _ ≤ ∫⁻ w in Cyl.cell d, ENNReal.ofReal C * ‖ψ (x - w)‖ₑ :=
          lintegral_mono_set diff_subset
      _ = ENNReal.ofReal C * ∫⁻ w in Cyl.cell d, ‖ψ (x - w)‖ₑ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = _ := by
          rw [Cyl.lintegral_cell_comp_sub_left hd0 (G := fun y => ‖ψ y‖ₑ) hψper' x]

end AdjFubiniAux

open UnforcedLeray in
/-- **The duality (Fubini) identity** `KerAdjFubini` from the near/far bounds `KerNearFar`
(SP 3052-3057). -/
theorem kerAdjFubini_of (h : UnforcedLeray.Short.IIIa.KerNearFar) :
    UnforcedLeray.Short.IIIa.KerAdjFubini := by
  obtain ⟨C, hC0, hC⟩ := h
  intro d hd F hF ψ hψ
  have hd0 : 0 < d := by linarith
  obtain ⟨hmeas, hper, -, hnear, hfar⟩ := hC d hd
  obtain ⟨B, hB0, hB, hL⟩ := AdjFubiniAux.test_facts hd0 hψ
  set M : ℝ≥0∞ := ENNReal.ofReal B * ENNReal.ofReal C +
    ENNReal.ofReal C * ∫⁻ y in Cyl.cell d, ‖ψ y‖ₑ with hM
  have hMtop : M ≠ ⊤ := by
    rw [hM]
    exact (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL⟩).ne
  have hbound : ∀ (j : Fin 2) (x : ℝ × ℝ),
      ∫⁻ y in B0579.cell d, ‖kerD d (x - y) j‖ₑ * ‖ψ y‖ₑ ≤ M := fun j x =>
    AdjFubiniAux.kernel_test_bound hd hC0 hper hnear hfar hmeas hψ hB hB0 j x
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell d) with hμ
  have hkm : ∀ j : Fin 2, Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => kerD d (p.1 - p.2) j :=
    fun j => (hmeas j).comp (measurable_fst.sub measurable_snd)
  have hHj : ∀ j : Fin 2, Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      F j p.1 * ((kerD d (p.1 - p.2) j : ℝ) : ℂ) * (ψ p.2 : ℂ)) (μ.prod μ) := by
    intro j
    have hF1 : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F j p.1) (μ.prod μ) :=
      (hF j).aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst
    have hF2 : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((kerD d (p.1 - p.2) j : ℝ) : ℂ))
        (μ.prod μ) := (Complex.measurable_ofReal.comp (hkm j)).aestronglyMeasurable
    have hF3 : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (ψ p.2 : ℂ)) (μ.prod μ) :=
      ((Complex.continuous_ofReal.comp hψ.continuous).comp continuous_snd).aestronglyMeasurable
    have hsm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        F j p.1 * ((kerD d (p.1 - p.2) j : ℝ) : ℂ) * (ψ p.2 : ℂ)) (μ.prod μ) :=
      (hF1.mul hF2).mul hF3
    refine ⟨hsm, ?_⟩
    show ∫⁻ p, ‖F j p.1 * ((kerD d (p.1 - p.2) j : ℝ) : ℂ) * (ψ p.2 : ℂ)‖ₑ ∂(μ.prod μ) < ⊤
    rw [lintegral_prod _ hsm.enorm]
    have hin : ∀ x : ℝ × ℝ, ∫⁻ y, ‖F j x * ((kerD d (x - y) j : ℝ) : ℂ) * (ψ y : ℂ)‖ₑ ∂μ ≤
        ‖F j x‖ₑ * M := by
      intro x
      calc ∫⁻ y, ‖F j x * ((kerD d (x - y) j : ℝ) : ℂ) * (ψ y : ℂ)‖ₑ ∂μ
          = ∫⁻ y, ‖F j x‖ₑ * (‖kerD d (x - y) j‖ₑ * ‖ψ y‖ₑ) ∂μ := by
            refine lintegral_congr fun y => ?_
            simp only [enorm_mul, AdjFubiniAux.enorm_ofReal_complex, mul_assoc]
        _ = ‖F j x‖ₑ * ∫⁻ y, ‖kerD d (x - y) j‖ₑ * ‖ψ y‖ₑ ∂μ := by
            refine lintegral_const_mul'' _ ?_
            exact ((hmeas j).comp (measurable_const.sub measurable_id)).enorm.mul
              hψ.continuous.measurable.enorm |>.aemeasurable
        _ ≤ ‖F j x‖ₑ * M := by gcongr; exact hbound j x
    calc ∫⁻ x, ∫⁻ y, ‖F j x * ((kerD d (x - y) j : ℝ) : ℂ) * (ψ y : ℂ)‖ₑ ∂μ ∂μ
        ≤ ∫⁻ x, ‖F j x‖ₑ * M ∂μ := lintegral_mono hin
      _ = (∫⁻ x, ‖F j x‖ₑ ∂μ) * M := lintegral_mul_const' _ _ hMtop
      _ < ⊤ := ENNReal.mul_lt_top (hF j).hasFiniteIntegral hMtop.lt_top
  set Hs : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x y =>
    ∑ j, F j x * ((kerD d (x - y) j : ℝ) : ℂ) * (ψ y : ℂ) with hHs
  have hHsI : Integrable (Function.uncurry Hs) (μ.prod μ) :=
    integrable_finset_sum _ fun j _ => hHj j
  have hkey : ∀ y, kerAdj d F y * (ψ y : ℂ) = ∫ x, Hs x y ∂μ := by
    intro y
    unfold kerAdj
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hHs, Finset.sum_mul]
  have hinner : ∀ (x : ℝ × ℝ), ∫ y, Hs x y ∂μ = ∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ) := by
    intro x
    have hIy : ∀ j : Fin 2, Integrable (fun y => ((ψ y * kerD d (x - y) j : ℝ) : ℂ)) μ := by
      intro j
      refine Integrable.ofReal ⟨?_, ?_⟩
      · exact (hψ.continuous.measurable.mul
          ((hmeas j).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      · unfold HasFiniteIntegral
        calc ∫⁻ y, ‖ψ y * kerD d (x - y) j‖ₑ ∂μ
            = ∫⁻ y, ‖kerD d (x - y) j‖ₑ * ‖ψ y‖ₑ ∂μ := by
              refine lintegral_congr fun y => ?_
              rw [enorm_mul, mul_comm]
          _ ≤ M := hbound j x
          _ < ⊤ := hMtop.lt_top
    have e : ∀ y, Hs x y = ∑ j, F j x * ((ψ y * kerD d (x - y) j : ℝ) : ℂ) := by
      intro y
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    simp_rw [e]
    rw [integral_finset_sum _ fun j _ => (hIy j).const_mul (F j x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_complex_ofReal]
    rfl
  refine ⟨?_, ?_⟩
  · show Integrable (fun y => kerAdj d F y * (ψ y : ℂ)) μ
    simp_rw [hkey]
    exact hHsI.integral_prod_right
  · calc ∫ y in B0579.cell d, kerAdj d F y * (ψ y : ℂ) = ∫ y, ∫ x, Hs x y ∂μ ∂μ := by
          simp_rw [hkey]; rfl
      _ = ∫ x, ∫ y, Hs x y ∂μ ∂μ := (integral_integral_swap hHsI).symm
      _ = ∫ x in B0579.cell d, ∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ) := by
          simp_rw [hinner]; rfl

end UnforcedLeray.Short.IIIa
