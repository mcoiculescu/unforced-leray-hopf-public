import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.PeriodicEntireVanish
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.CRDifferentiable
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.CellLintegralComplex

/-!


Periodic `L^r` fields `B₀, B₁` on the plane with `div = curl = 0` vanish. Classical 2D Liouville
step (source of record: `the November 2 reference manuscript`, SP 2618; the
argument is not written there).

Proof. `f z = B₀ (re z, im z) - i B₁ (re z, im z)` is real-`C¹` with `f_1 + i f_I = 0`, hence
entire (`CRDifferentiable`); it is `c`-periodic and has finite strip `L^r` integral
(`CellLintegralComplex`), so `f = 0` (`PeriodicEntireVanish`). Likewise
`g z = B₀ (re z, -im z) + i B₁ (re z, -im z)` is entire, periodic, with finite strip integral (the
reflection `η ↦ -η` preserves Lebesgue measure on the cell), so `g = 0`. Then
`B₀ = i B₁` and `B₀ + i B₁ = 0` give `2 i B₁ = 0`, so `B₁ = B₀ = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The real-linear map `z ↦ (re z, im z)`. -/
def dcvPh : ℂ →L[ℝ] ℝ × ℝ := Complex.reCLM.prod Complex.imCLM

/-- The real-linear map `z ↦ (re z, -im z)`. -/
def dcvPc : ℂ →L[ℝ] ℝ × ℝ := Complex.reCLM.prod (-Complex.imCLM)

theorem dcv_ph_apply (z : ℂ) : dcvPh z = (z.re, z.im) := by simp [dcvPh]

theorem dcv_pc_apply (z : ℂ) : dcvPc z = (z.re, -z.im) := by simp [dcvPc]

theorem dcv_ph_one : dcvPh 1 = ((1 : ℝ), (0 : ℝ)) := by simp [dcv_ph_apply]

theorem dcv_ph_I : dcvPh Complex.I = ((0 : ℝ), (1 : ℝ)) := by simp [dcv_ph_apply]

theorem dcv_pc_one : dcvPc 1 = ((1 : ℝ), (0 : ℝ)) := by simp [dcv_pc_apply]

theorem dcv_pc_I : dcvPc Complex.I = ((0 : ℝ), (-1 : ℝ)) := by simp [dcv_pc_apply]

/-- The combination `q ↦ B₀ q + s * B₁ q` on the plane. -/
def dcvG (B₀ B₁ : ℝ × ℝ → ℂ) (s : ℂ) : ℝ × ℝ → ℂ := fun q => B₀ q + s * B₁ q

/-- The majorant `2^(r-1) (‖B₀ p‖ₑ^r + ‖B₁ p‖ₑ^r)` on the plane. -/
def dcvH (r : ℝ) (B₀ B₁ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (r - 1) * (‖B₀ p‖ₑ ^ r + ‖B₁ p‖ₑ ^ r)

theorem dcv_contDiff {B₀ B₁ : ℝ × ℝ → ℂ} (hB₀ : ContDiff ℝ 1 B₀) (hB₁ : ContDiff ℝ 1 B₁)
    (s : ℂ) : ContDiff ℝ 1 (dcvG B₀ B₁ s) := by
  unfold dcvG
  exact hB₀.add (contDiff_const.mul hB₁)

theorem dcv_fderiv_G (B₀ B₁ : ℝ × ℝ → ℂ) (s : ℂ) (p v : ℝ × ℝ)
    (h₀ : DifferentiableAt ℝ B₀ p) (h₁ : DifferentiableAt ℝ B₁ p) :
    fderiv ℝ (dcvG B₀ B₁ s) p v = fderiv ℝ B₀ p v + s * fderiv ℝ B₁ p v := by
  unfold dcvG
  show fderiv ℝ (B₀ + fun y => s * B₁ y) p v = _
  rw [(h₀.hasFDerivAt.add (h₁.hasFDerivAt.const_mul s)).fderiv]
  simp [smul_eq_mul]

theorem dcv_fderiv_comp (G : ℝ × ℝ → ℂ) (Φ : ℂ →L[ℝ] ℝ × ℝ) (z v : ℂ)
    (hG : DifferentiableAt ℝ G (Φ z)) :
    fderiv ℝ (fun w => G (Φ w)) z v = fderiv ℝ G (Φ z) (Φ v) := by
  have h : fderiv ℝ (fun w => G (Φ w)) z = (fderiv ℝ G (Φ z)).comp (fderiv ℝ Φ z) :=
    fderiv_comp z hG Φ.differentiableAt
  rw [h, Φ.fderiv, ContinuousLinearMap.comp_apply]

theorem dcv_fd_comp (B₀ B₁ : ℝ × ℝ → ℂ) (s : ℂ) (Φ : ℂ →L[ℝ] ℝ × ℝ)
    (hB₀ : ContDiff ℝ 1 B₀) (hB₁ : ContDiff ℝ 1 B₁) (z v : ℂ) :
    fderiv ℝ (fun w => dcvG B₀ B₁ s (Φ w)) z v
      = fderiv ℝ B₀ (Φ z) (Φ v) + s * fderiv ℝ B₁ (Φ z) (Φ v) := by
  have hd : DifferentiableAt ℝ (dcvG B₀ B₁ s) (Φ z) :=
    ((dcv_contDiff hB₀ hB₁ s).differentiable one_ne_zero) _
  rw [dcv_fderiv_comp _ Φ z v hd]
  exact dcv_fderiv_G B₀ B₁ s (Φ z) (Φ v) (hB₀.differentiable one_ne_zero _)
    (hB₁.differentiable one_ne_zero _)

/-- Liouville step for a real-`C¹`, Cauchy-Riemann, `c`-periodic function with finite strip
`L^r` integral: it vanishes. Uses `CRDifferentiable` and `PeriodicEntireVanish`. -/
theorem dcv_vanish (c r : ℝ) (hc : 0 < c) (hr : 1 ≤ r) (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f)
    (hcr : ∀ z : ℂ, fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0)
    (hper : ∀ z : ℂ, f (z + (c : ℂ)) = f z)
    (hI : (∫⁻ z in {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)}, ‖f z‖ₑ ^ r) ≠ ⊤) : f = 0 := by
  have hCR : UnforcedLeray.Short.IIb.CRDifferentiable := UnforcedLeray.Short.IIb.crDifferentiable
  unfold UnforcedLeray.Short.IIb.CRDifferentiable at hCR
  have hd : Differentiable ℂ f := hCR f hf hcr
  have hPEV : UnforcedLeray.Short.IIb.PeriodicEntireVanish :=
    UnforcedLeray.Short.IIb.periodicEntireVanish
  unfold UnforcedLeray.Short.IIb.PeriodicEntireVanish at hPEV
  exact hPEV c r f hc hr hd hper hI

/-- Finite strip integral from a finite cell majorant. Uses `CellLintegralComplex`. -/
theorem dcv_strip_fin (c r : ℝ) (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H)
    (hHfin : (∫⁻ p in UnforcedLeray.Cyl.cell c, H p) ≠ ⊤) (f : ℂ → ℂ)
    (hf : ∀ z : ℂ, ‖f z‖ₑ ^ r ≤ H (z.re, z.im)) :
    (∫⁻ z in {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)}, ‖f z‖ₑ ^ r) ≠ ⊤ := by
  have hcl : UnforcedLeray.Short.IIb.CellLintegralComplex :=
    UnforcedLeray.Short.IIb.cellLintegralComplex
  unfold UnforcedLeray.Short.IIb.CellLintegralComplex at hcl
  have h1 := hcl c H hH
  have h2 : (∫⁻ z in {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)}, ‖f z‖ₑ ^ r)
      ≤ ∫⁻ z in {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)}, H (z.re, z.im) :=
    lintegral_mono (fun z => hf z)
  refine ne_top_of_le_ne_top ?_ h2
  rw [h1]
  exact hHfin

theorem dcv_enorm_I : ‖Complex.I‖ₑ = 1 := by
  simp [enorm_eq_nnnorm]

theorem dcv_norm_le (a b c : ℂ) (hc : ‖c‖ₑ = 1) : ‖a + c * b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  calc ‖a + c * b‖ₑ ≤ ‖a‖ₑ + ‖c * b‖ₑ := enorm_add_le _ _
    _ = ‖a‖ₑ + ‖b‖ₑ := by rw [enorm_mul, hc, one_mul]

theorem dcv_pt (r : ℝ) (hr : 1 ≤ r) (B₀ B₁ : ℝ × ℝ → ℂ) (c : ℂ) (hc : ‖c‖ₑ = 1)
    (p : ℝ × ℝ) : ‖B₀ p + c * B₁ p‖ₑ ^ r ≤ dcvH r B₀ B₁ p := by
  unfold dcvH
  calc ‖B₀ p + c * B₁ p‖ₑ ^ r ≤ (‖B₀ p‖ₑ + ‖B₁ p‖ₑ) ^ r :=
        ENNReal.rpow_le_rpow (dcv_norm_le _ _ _ hc) (by linarith)
    _ ≤ (2 : ℝ≥0∞) ^ (r - 1) * (‖B₀ p‖ₑ ^ r + ‖B₁ p‖ₑ ^ r) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr

theorem dcv_H_meas (r : ℝ) (B₀ B₁ : ℝ × ℝ → ℂ) (hB₀ : Continuous B₀) (hB₁ : Continuous B₁) :
    Measurable (dcvH r B₀ B₁) := by
  unfold dcvH
  exact ((hB₀.enorm.measurable.pow_const r).add (hB₁.enorm.measurable.pow_const r)).const_mul _

theorem dcv_H_fin (c r : ℝ) (hr : 1 ≤ r) (B₀ B₁ : ℝ × ℝ → ℂ) (hB₀ : Continuous B₀)
    (hB₁ : Continuous B₁)
    (h₀ : (∫⁻ p in UnforcedLeray.Cyl.cell c, ‖B₀ p‖ₑ ^ r) ≠ ⊤)
    (h₁ : (∫⁻ p in UnforcedLeray.Cyl.cell c, ‖B₁ p‖ₑ ^ r) ≠ ⊤) :
    (∫⁻ p in UnforcedLeray.Cyl.cell c, dcvH r B₀ B₁ p) ≠ ⊤ := by
  have hA : Measurable (fun p => ‖B₀ p‖ₑ ^ r) := hB₀.enorm.measurable.pow_const r
  have hB : Measurable (fun p => ‖B₁ p‖ₑ ^ r) := hB₁.enorm.measurable.pow_const r
  have hS : Measurable (fun p => ‖B₀ p‖ₑ ^ r + ‖B₁ p‖ₑ ^ r) := hA.add hB
  unfold dcvH
  rw [lintegral_const_mul _ hS, lintegral_add_left hA]
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
    (ENNReal.add_ne_top.2 ⟨h₀, h₁⟩)

/-- Reflection `η ↦ -η` preserves the cell integral. -/
theorem dcv_refl (c : ℝ) (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p in UnforcedLeray.Cyl.cell c, H (p.1, -p.2))
      = ∫⁻ p in UnforcedLeray.Cyl.cell c, H p := by
  have hσ : MeasurePreserving (fun p : ℝ × ℝ => (p.1, -p.2)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)
  have hs : MeasurableSet (UnforcedLeray.Cyl.cell c) := UnforcedLeray.Cyl.measurableSet_cell c
  have hpre : (fun p : ℝ × ℝ => (p.1, -p.2)) ⁻¹' UnforcedLeray.Cyl.cell c
      = UnforcedLeray.Cyl.cell c := by
    ext p
    simp [UnforcedLeray.Cyl.cell]
  have key := hσ.setLIntegral_comp_preimage hs hH
  rw [hpre] at key
  exact key

theorem divCurlFreeVanish : UnforcedLeray.Short.IIb.DivCurlFreeVanish := by
  unfold UnforcedLeray.Short.IIb.DivCurlFreeVanish
  intro c r B₀ B₁ hc hr hB₀ hB₁ hp₀ hp₁ hd hcurl hfin₀ hfin₁
  have hB₀c : Continuous B₀ := hB₀.continuous
  have hB₁c : Continuous B₁ := hB₁.continuous
  have hH : Measurable (dcvH r B₀ B₁) := dcv_H_meas r B₀ B₁ hB₀c hB₁c
  have hHfin : (∫⁻ p in UnforcedLeray.Cyl.cell c, dcvH r B₀ B₁ p) ≠ ⊤ :=
    dcv_H_fin c r hr B₀ B₁ hB₀c hB₁c hfin₀ hfin₁
  have hHg : Measurable (fun p : ℝ × ℝ => dcvH r B₀ B₁ (p.1, -p.2)) :=
    hH.comp (measurable_fst.prodMk measurable_snd.neg)
  have hHgFin : (∫⁻ p in UnforcedLeray.Cyl.cell c, dcvH r B₀ B₁ (p.1, -p.2)) ≠ ⊤ := by
    rw [dcv_refl c (dcvH r B₀ B₁) hH]
    exact hHfin
  -- the field `f = B₀ - i B₁` on the plane
  have hcrF : ∀ z : ℂ,
      fderiv ℝ (fun w => dcvG B₀ B₁ (-Complex.I) (dcvPh w)) z 1
        + Complex.I * fderiv ℝ (fun w => dcvG B₀ B₁ (-Complex.I) (dcvPh w)) z Complex.I = 0 := by
    intro z
    rw [dcv_fd_comp B₀ B₁ (-Complex.I) dcvPh hB₀ hB₁ z 1,
      dcv_fd_comp B₀ B₁ (-Complex.I) dcvPh hB₀ hB₁ z Complex.I, dcv_ph_one, dcv_ph_I]
    linear_combination hd (dcvPh z) + Complex.I * hcurl (dcvPh z)
      + (-(fderiv ℝ B₁ (dcvPh z) ((0 : ℝ), (1 : ℝ)))) * Complex.I_mul_I
  have hperF : ∀ z : ℂ,
      (fun w => dcvG B₀ B₁ (-Complex.I) (dcvPh w)) (z + (c : ℂ))
        = (fun w => dcvG B₀ B₁ (-Complex.I) (dcvPh w)) z := by
    intro z
    have h0 : B₀ (z.re + c, z.im) = B₀ (z.re, z.im) := hp₀ (z.re, z.im)
    have h1 : B₁ (z.re + c, z.im) = B₁ (z.re, z.im) := hp₁ (z.re, z.im)
    have e : dcvPh (z + (c : ℂ)) = (z.re + c, z.im) := by
      rw [dcv_ph_apply]
      simp
    show dcvG B₀ B₁ (-Complex.I) (dcvPh (z + (c : ℂ)))
      = dcvG B₀ B₁ (-Complex.I) (dcvPh z)
    rw [e, dcv_ph_apply]
    unfold dcvG
    rw [h0, h1]
  have hfF : ∀ z : ℂ, ‖dcvG B₀ B₁ (-Complex.I) (dcvPh z)‖ₑ ^ r
      ≤ dcvH r B₀ B₁ (z.re, z.im) := by
    intro z
    have hc1 : ‖-Complex.I‖ₑ = 1 := by rw [enorm_neg, dcv_enorm_I]
    have h := dcv_pt r hr B₀ B₁ (-Complex.I) hc1 (dcvPh z)
    rw [dcv_ph_apply] at h ⊢
    exact h
  have hF : (fun z : ℂ => dcvG B₀ B₁ (-Complex.I) (dcvPh z)) = 0 := by
    apply dcv_vanish c r hc hr
    · exact (dcv_contDiff hB₀ hB₁ _).comp dcvPh.contDiff
    · exact hcrF
    · exact hperF
    · exact dcv_strip_fin c r (dcvH r B₀ B₁) hH hHfin
        (fun z : ℂ => dcvG B₀ B₁ (-Complex.I) (dcvPh z)) hfF
  -- the reflected field `g = B₀ + i B₁` at `(re z, -im z)`
  have hcrG : ∀ z : ℂ,
      fderiv ℝ (fun w => dcvG B₀ B₁ Complex.I (dcvPc w)) z 1
        + Complex.I * fderiv ℝ (fun w => dcvG B₀ B₁ Complex.I (dcvPc w)) z Complex.I = 0 := by
    intro z
    have hneg : ((0 : ℝ), (-1 : ℝ)) = -((0 : ℝ), (1 : ℝ)) := by simp
    rw [dcv_fd_comp B₀ B₁ Complex.I dcvPc hB₀ hB₁ z 1,
      dcv_fd_comp B₀ B₁ Complex.I dcvPc hB₀ hB₁ z Complex.I, dcv_pc_one, dcv_pc_I, hneg]
    simp only [map_neg]
    linear_combination hd (dcvPc z) - Complex.I * hcurl (dcvPc z)
      + (-(fderiv ℝ B₁ (dcvPc z) ((0 : ℝ), (1 : ℝ)))) * Complex.I_mul_I
  have hperG : ∀ z : ℂ,
      (fun w => dcvG B₀ B₁ Complex.I (dcvPc w)) (z + (c : ℂ))
        = (fun w => dcvG B₀ B₁ Complex.I (dcvPc w)) z := by
    intro z
    have h0 : B₀ (z.re + c, -z.im) = B₀ (z.re, -z.im) := hp₀ (z.re, -z.im)
    have h1 : B₁ (z.re + c, -z.im) = B₁ (z.re, -z.im) := hp₁ (z.re, -z.im)
    have e : dcvPc (z + (c : ℂ)) = (z.re + c, -z.im) := by
      rw [dcv_pc_apply]
      simp
    show dcvG B₀ B₁ Complex.I (dcvPc (z + (c : ℂ))) = dcvG B₀ B₁ Complex.I (dcvPc z)
    rw [e, dcv_pc_apply]
    unfold dcvG
    rw [h0, h1]
  have hfG : ∀ z : ℂ, ‖dcvG B₀ B₁ Complex.I (dcvPc z)‖ₑ ^ r
      ≤ (fun p : ℝ × ℝ => dcvH r B₀ B₁ (p.1, -p.2)) (z.re, z.im) := by
    intro z
    have hc1 : ‖Complex.I‖ₑ = 1 := dcv_enorm_I
    have h := dcv_pt r hr B₀ B₁ Complex.I hc1 (dcvPc z)
    rw [dcv_pc_apply] at h ⊢
    exact h
  have hG : (fun z : ℂ => dcvG B₀ B₁ Complex.I (dcvPc z)) = 0 := by
    apply dcv_vanish c r hc hr
    · exact (dcv_contDiff hB₀ hB₁ _).comp dcvPc.contDiff
    · exact hcrG
    · exact hperG
    · exact dcv_strip_fin c r (fun p : ℝ × ℝ => dcvH r B₀ B₁ (p.1, -p.2)) hHg hHgFin
        (fun z : ℂ => dcvG B₀ B₁ Complex.I (dcvPc z)) hfG
  -- pointwise identities
  have E1 : ∀ p : ℝ × ℝ, B₀ p + (-Complex.I) * B₁ p = 0 := by
    intro p
    have h : dcvG B₀ B₁ (-Complex.I) (dcvPh ⟨p.1, p.2⟩) = 0 := congrFun hF ⟨p.1, p.2⟩
    have hp : dcvPh (⟨p.1, p.2⟩ : ℂ) = p := by rw [dcv_ph_apply]
    rw [hp] at h
    exact h
  have E2 : ∀ p : ℝ × ℝ, B₀ p + Complex.I * B₁ p = 0 := by
    intro p
    have h : dcvG B₀ B₁ Complex.I (dcvPc ⟨p.1, -p.2⟩) = 0 := congrFun hG ⟨p.1, -p.2⟩
    have hp : dcvPc (⟨p.1, -p.2⟩ : ℂ) = p := by
      rw [dcv_pc_apply]
      simp
    rw [hp] at h
    exact h
  have hB1 : ∀ p : ℝ × ℝ, B₁ p = 0 := by
    intro p
    have h2 : (2 * Complex.I) * B₁ p = 0 := by linear_combination E2 p - E1 p
    exact (mul_eq_zero.1 h2).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hB0 : ∀ p : ℝ × ℝ, B₀ p = 0 := by
    intro p
    linear_combination E2 p - Complex.I * hB1 p
  exact ⟨funext hB0, funext hB1⟩

end UnforcedLeray.Short.IIb

end
