import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv.Duality.KernelIntegrable.Tiling

/-!
# Part III-a, `PartIII-a:T21/3/2/1/2/1/2`: integrability of the duality kernel (lemma B)

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
With `G = heatKernel2 τ`, the kernel `G(z - y) F(y) φ(z)` is integrable on `cell × plane`:
its absolute integral is at most `M ∫_{cell} ∫_y G(z-y)|F y|`, and the Tonelli swap gives
`∫_y |F y| H(y)` with `H(y) = ∫_{cell} G(z - y) dz`. Tiling the plane by the cell translates,
`∑_k H(y - k c e₁) = 1`, so the integral is `∫_{cell} |F|`, finite since `F` is integrable on the
cell.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Function
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

theorem dualityKernelIntegrable : UnforcedLeray.Short.IIIa.Exist.DualityKernelIntegrable := by
  intro c hc τ hτ F φ hFm hFper hFint hφm M hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hGm : Measurable (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 τ w) :=
    UnforcedLeray.B0284.measurable_heatKernel2_right τ
  have hGnn : ∀ w : ℝ × ℝ, 0 ≤ UnforcedLeray.B0284.heatKernel2 τ w :=
    fun w => UnforcedLeray.B0284.heatKernel2_nonneg hτ w
  -- periodicity of `F` along all integer shifts
  have hPer : ∀ k : ℤ, ∀ y : ℝ × ℝ, F (y - ((k : ℝ) * c, (0 : ℝ))) = F y := by
    intro k y
    have hP : Function.Periodic F ((c, (0 : ℝ)) : ℝ × ℝ) := fun x => by
      have h := hFper x
      rw [← h]
      congr 1
      ext <;> simp
    have h2 := (hP.zsmul (-k)) y
    have e : ((-k : ℤ) • ((c, (0 : ℝ)) : ℝ × ℝ)) = (-((k : ℝ) * c), (0 : ℝ)) := by
      ext <;> simp [zsmul_eq_mul]
    rw [e] at h2
    rw [← h2]
    congr 1
    ext <;> simp [sub_eq_add_neg]
  have hFm' : Measurable (fun y : ℝ × ℝ => ENNReal.ofReal |F y|) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hFm)
  -- the kernel `A(z,y) = G(z-y) |F y|` and the cell-section `H(y) = ∫_{cell} G(z-y) dz`
  set A : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 τ (p.1 - p.2)) * ENNReal.ofReal |F p.2|
    with hA
  have hAm : Measurable A :=
    (ENNReal.measurable_ofReal.comp (hGm.comp (measurable_fst.sub measurable_snd))).mul
      (hFm'.comp measurable_snd)
  set H : ℝ × ℝ → ℝ≥0∞ := fun y =>
    ∫⁻ z in UnforcedLeray.B0579.cell c, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 τ (z - y))
    with hH
  have hHm : Measurable H := by
    have h0 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 τ (p.1 - p.2))) :=
      ENNReal.measurable_ofReal.comp (hGm.comp (measurable_fst.sub measurable_snd))
    exact h0.lintegral_prod_left'
  -- `∑_k H(y + k c e₁) = 1` by tiling, and the same for `y - k c e₁` by reindexing `k ↦ -k`
  have hsumPlus : ∀ y : ℝ × ℝ, ∑' k : ℤ, H (y + ((k : ℝ) * c, (0 : ℝ))) = 1 := by
    intro y
    have hT := UnforcedLeray.Short.IIIa.Exist.KI.lintegral_eq_tsum_minus c hc
      (fun w => ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 τ (w - y)))
      (ENNReal.measurable_ofReal.comp (hGm.comp (measurable_id.sub_const y)))
    have hI : ∫⁻ p, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 τ (p - y)) = 1 := by
      have := lintegral_sub_right_eq_self
        (μ := volume) (fun p : ℝ × ℝ => ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 τ p)) y
      simpa [UnforcedLeray.B0284.lintegral_heatKernel2 hτ] using this
    have hT' : ∑' k : ℤ, H (y + ((k : ℝ) * c, (0 : ℝ))) =
        ∑' k : ℤ, ∫⁻ p in UnforcedLeray.B0579.cell c,
          ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 τ (p - ((k : ℝ) * c, (0 : ℝ)) - y)) := by
      refine tsum_congr fun k => ?_
      simp only [hH]
      refine lintegral_congr fun z => ?_
      rw [show z - (y + ((k : ℝ) * c, (0 : ℝ))) = z - ((k : ℝ) * c, (0 : ℝ)) - y by abel]
    rw [hT', ← hT, hI]
  have hsumH : ∀ y : ℝ × ℝ, ∑' k : ℤ, H (y - ((k : ℝ) * c, (0 : ℝ))) = 1 := by
    intro y
    rw [← hsumPlus y, ← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => H (y + ((k : ℝ) * c, (0 : ℝ))))]
    refine tsum_congr fun k => ?_
    congr 1
    ext <;> simp [sub_eq_add_neg, neg_mul]
  -- `∫_{cell} |F|` is finite
  have hFfin : ∫⁻ p in UnforcedLeray.B0579.cell c, ENNReal.ofReal |F p| < ⊤ := by
    have h := hFint.2
    unfold HasFiniteIntegral at h
    simpa [Real.enorm_eq_ofReal_abs] using h
  -- `∫_y |F y| H(y) < ∞`
  have hfin : ∫⁻ y, H y * ENNReal.ofReal |F y| < ⊤ := by
    have hPm : Measurable (fun y => H y * ENNReal.ofReal |F y|) := hHm.mul hFm'
    rw [UnforcedLeray.Short.IIIa.Exist.KI.lintegral_eq_tsum_minus c hc _ hPm]
    have hstep : ∀ k : ℤ, ∫⁻ p in UnforcedLeray.B0579.cell c,
        H (p - ((k : ℝ) * c, (0 : ℝ))) * ENNReal.ofReal |F (p - ((k : ℝ) * c, (0 : ℝ)))| =
        ∫⁻ p in UnforcedLeray.B0579.cell c,
          ENNReal.ofReal |F p| * H (p - ((k : ℝ) * c, (0 : ℝ))) := by
      intro k
      refine lintegral_congr fun p => ?_
      rw [hPer k p]
      ring
    rw [tsum_congr hstep]
    have hmeask : ∀ k : ℤ, Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal |F p| * H (p - ((k : ℝ) * c, (0 : ℝ)))) :=
      fun k => hFm'.mul (hHm.comp (measurable_id.sub_const _))
    rw [← lintegral_tsum (μ := volume.restrict (UnforcedLeray.B0579.cell c))
      (fun k => (hmeask k).aemeasurable)]
    have hsum2 : ∀ p : ℝ × ℝ, ∑' k : ℤ, ENNReal.ofReal |F p| * H (p - ((k : ℝ) * c, (0 : ℝ))) =
        ENNReal.ofReal |F p| := by
      intro p
      rw [ENNReal.tsum_mul_left, hsumH p, mul_one]
    rw [lintegral_congr hsum2]
    exact hFfin
  -- the integrability statement
  have hK : Measurable (Function.uncurry fun z y : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 τ (z - y) * F y * φ z) := by
    show Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      UnforcedLeray.B0284.heatKernel2 τ (p.1 - p.2) * F p.2 * φ p.1)
    exact ((hGm.comp (measurable_fst.sub measurable_snd)).mul (hFm.comp measurable_snd)).mul
      (hφm.comp measurable_fst)
  refine ⟨hK.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hbound : ∀ p : (ℝ × ℝ) × (ℝ × ℝ),
      ‖Function.uncurry (fun z y : ℝ × ℝ =>
        UnforcedLeray.B0284.heatKernel2 τ (z - y) * F y * φ z) p‖ₑ ≤ ENNReal.ofReal M * A p := by
    intro p
    rw [← ofReal_norm_eq_enorm]
    have hGp := hGnn (p.1 - p.2)
    have hGF : 0 ≤ UnforcedLeray.B0284.heatKernel2 τ (p.1 - p.2) * |F p.2| :=
      mul_nonneg hGp (abs_nonneg _)
    have hnorm : ‖Function.uncurry (fun z y : ℝ × ℝ =>
        UnforcedLeray.B0284.heatKernel2 τ (z - y) * F y * φ z) p‖ ≤
        M * (UnforcedLeray.B0284.heatKernel2 τ (p.1 - p.2) * |F p.2|) := by
      show ‖UnforcedLeray.B0284.heatKernel2 τ (p.1 - p.2) * F p.2 * φ p.1‖ ≤ _
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hGp]
      calc UnforcedLeray.B0284.heatKernel2 τ (p.1 - p.2) * |F p.2| * |φ p.1|
          ≤ UnforcedLeray.B0284.heatKernel2 τ (p.1 - p.2) * |F p.2| * M :=
            mul_le_mul_of_nonneg_left (hM p.1) hGF
        _ = M * (UnforcedLeray.B0284.heatKernel2 τ (p.1 - p.2) * |F p.2|) := by ring
    calc ENNReal.ofReal ‖Function.uncurry (fun z y : ℝ × ℝ =>
          UnforcedLeray.B0284.heatKernel2 τ (z - y) * F y * φ z) p‖
        ≤ ENNReal.ofReal (M * (UnforcedLeray.B0284.heatKernel2 τ (p.1 - p.2) * |F p.2|)) :=
          ENNReal.ofReal_le_ofReal hnorm
      _ = ENNReal.ofReal M * A p := by
          simp only [hA]
          rw [ENNReal.ofReal_mul hM0, ENNReal.ofReal_mul hGp]
  calc ∫⁻ p, ‖Function.uncurry (fun z y : ℝ × ℝ =>
          UnforcedLeray.B0284.heatKernel2 τ (z - y) * F y * φ z) p‖ₑ
        ∂((volume.restrict (UnforcedLeray.B0579.cell c)).prod volume)
      ≤ ∫⁻ p, ENNReal.ofReal M * A p ∂((volume.restrict (UnforcedLeray.B0579.cell c)).prod volume) :=
        lintegral_mono hbound
    _ = ENNReal.ofReal M * ∫⁻ p, A p ∂((volume.restrict (UnforcedLeray.B0579.cell c)).prod volume) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal M * ∫⁻ z in UnforcedLeray.B0579.cell c, ∫⁻ y, A (z, y) := by
        rw [lintegral_prod _ hAm.aemeasurable]
    _ = ENNReal.ofReal M * ∫⁻ y, ∫⁻ z in UnforcedLeray.B0579.cell c, A (z, y) := by
        rw [lintegral_lintegral_swap hAm.aemeasurable]
    _ = ENNReal.ofReal M * ∫⁻ y, H y * ENNReal.ofReal |F y| := by
        congr 1
        refine lintegral_congr fun y => ?_
        simp only [hA, hH]
        exact lintegral_mul_const _ (ENNReal.measurable_ofReal.comp
          (hGm.comp (measurable_id.sub_const y)))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end UnforcedLeray.Short.IIIa.Exist
